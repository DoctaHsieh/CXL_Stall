/*
 * test_stall_numa.c - arm the CXL read-stall against a real, owned buffer
 *                     in CXL memory (NUMA node, mode=ram).
 *
 * Build: gcc -O2 -o test_stall_numa test_stall_numa.c
 * Run:   sudo ./test_stall_numa [options]
 *
 *   --bdf    <bdf>    CSR function          (default 0000:40:00.1)
 *   --base   <hex>    CXL HPA base          (default 8080000000)
 *   --size   <hex>    CXL window size       (default 400000000)
 *   --cycles <n>      stall cycles, 1-65535 (default 8000)
 *   --offset <hex>    byte offset into the test buffer (default 0)
 *   --hold            stay armed until you press Enter
 *   --disarm          clear the stall and exit
 *
 * Calibration result this is built on: araddr carries the RAW host physical
 * address. No HDM base subtraction, no interleave transform. So the value
 * written to csr_stall_addr is just the 64B-aligned HPA of the target line.
 *
 * CSR map (ex_default_csr_avmm_slave.sv), PF1 BAR2:
 *   0x1000 : csr_stall_addr (64-bit)
 *   0x1008 : bit0 = csr_stall_en, bits 16:1 = csr_stall_cycles
 *
 * IMPORTANT: the stall targets a physical address. This program keeps the
 * backing page allocated and locked for as long as the stall is armed, and
 * disarms on exit and on SIGINT/SIGTERM. Do not arm and then exit -- the
 * kernel would be free to reuse that frame while the FPGA still stalls it.
 */

#define _GNU_SOURCE
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <unistd.h>
#include <errno.h>
#include <signal.h>
#include <dirent.h>
#include <sched.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <x86intrin.h>

#define CSR_STALL_ADDR 0x1000
#define CSR_STALL_CTRL 0x1008
#define CSR_MAP_LEN    0x2000

#define PAGE_SZ    4096
#define BUF_PAGES  512          /* 2 MB */
#define REPS       128
#define LINE_MASK  (~63ULL)     /* araddr arrives 64B aligned */

#define MPOL_BIND      2
#define MPOL_MF_MOVE   (1<<1)
#define MPOL_MF_STRICT (1<<0)

static volatile uint8_t *g_csr = NULL;

/* ---------------- CSR ---------------- */

static void stall_disarm(void)
{
    if (!g_csr)
        return;
    *(volatile uint64_t *)(g_csr + CSR_STALL_CTRL) = 0;
    _mm_sfence();
}

static void on_signal(int sig)
{
    stall_disarm();
    fprintf(stderr, "\nsignal %d: stall disarmed.\n", sig);
    _exit(128 + sig);
}

static void stall_arm(uint64_t hpa, uint16_t cycles)
{
    *(volatile uint64_t *)(g_csr + CSR_STALL_ADDR) = hpa;
    _mm_sfence();
    *(volatile uint64_t *)(g_csr + CSR_STALL_CTRL) =
        ((uint64_t)cycles << 1) | 1ULL;
    _mm_sfence();
    usleep(200);
}

static void stall_readback(uint64_t *addr, uint16_t *cyc, int *en)
{
    uint64_t a = *(volatile uint64_t *)(g_csr + CSR_STALL_ADDR);
    uint64_t c = *(volatile uint64_t *)(g_csr + CSR_STALL_CTRL);
    *addr = a;
    *en   = (int)(c & 1);
    *cyc  = (uint16_t)((c >> 1) & 0xFFFF);
}

static volatile uint8_t *map_csr(const char *bdf)
{
    char path[512];
    void *p;
    int fd;

    snprintf(path, sizeof(path), "/sys/bus/pci/devices/%s/resource2", bdf);
    fd = open(path, O_RDWR | O_SYNC);
    if (fd < 0) {
        fprintf(stderr, "open(%s): %s\n", path, strerror(errno));
        return NULL;
    }
    p = mmap(NULL, CSR_MAP_LEN, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    close(fd);
    if (p == MAP_FAILED) {
        fprintf(stderr, "mmap CSR: %s\n", strerror(errno));
        return NULL;
    }
    return (volatile uint8_t *)p;
}

/* ---------------- timing ---------------- */

static inline uint64_t tsc_begin(void)
{
    unsigned a, d;
    __asm__ __volatile__("lfence\n\trdtsc" : "=a"(a), "=d"(d) :: "memory");
    return ((uint64_t)d << 32) | a;
}

static inline uint64_t tsc_end(void)
{
    unsigned a, d, c;
    __asm__ __volatile__("rdtscp\n\tlfence"
                         : "=a"(a), "=d"(d), "=c"(c) :: "memory");
    return ((uint64_t)d << 32) | a;
}

static int cmp_u64(const void *x, const void *y)
{
    uint64_t a = *(const uint64_t *)x, b = *(const uint64_t *)y;
    return (a > b) - (a < b);
}

static uint64_t measure(volatile uint8_t *p, uint64_t *median_out)
{
    static uint64_t s[REPS];
    int i;

    for (i = 0; i < REPS; i++) {
        uint64_t t0, t1, v;

        _mm_clflush((const void *)p);
        _mm_mfence();
        t0 = tsc_begin();
        v  = *(volatile uint64_t *)p;
        t1 = tsc_end();
        __asm__ __volatile__("" :: "r"(v));
        s[i] = t1 - t0;
    }
    qsort(s, REPS, sizeof(s[0]), cmp_u64);
    if (median_out)
        *median_out = s[REPS / 2];
    return s[0];
}

/* ---------------- physical addresses ---------------- */

static int pagemap_fd = -1;

static uint64_t virt_to_phys(void *va)
{
    uint64_t entry, pfn;
    off_t off = ((uintptr_t)va / PAGE_SZ) * 8;

    if (pagemap_fd < 0) {
        pagemap_fd = open("/proc/self/pagemap", O_RDONLY);
        if (pagemap_fd < 0)
            return 0;
    }
    if (pread(pagemap_fd, &entry, sizeof(entry), off) != sizeof(entry))
        return 0;
    if (!(entry & (1ULL << 63)))
        return 0;
    pfn = entry & ((1ULL << 55) - 1);
    if (!pfn)
        return 0;
    return (pfn * PAGE_SZ) + ((uintptr_t)va % PAGE_SZ);
}

/* ---------------- NUMA ---------------- */

static int mbind_to_node(void *addr, size_t len, int node)
{
    unsigned long mask[16];

    memset(mask, 0, sizeof(mask));
    mask[node / (8 * sizeof(unsigned long))] |=
        1UL << (node % (8 * sizeof(unsigned long)));
    return (int)syscall(__NR_mbind, addr, len, MPOL_BIND, mask,
                        16 * 8 * sizeof(unsigned long),
                        MPOL_MF_MOVE | MPOL_MF_STRICT);
}

static int max_numa_node(void)
{
    DIR *d = opendir("/sys/devices/system/node");
    struct dirent *e;
    int max = -1;

    if (!d)
        return -1;
    while ((e = readdir(d))) {
        int n;
        if (sscanf(e->d_name, "node%d", &n) == 1 && n > max)
            max = n;
    }
    closedir(d);
    return max;
}

static int find_cxl_node(uint64_t base, uint64_t size)
{
    int nmax = max_numa_node(), n;

    for (n = 0; n <= nmax; n++) {
        void *p;
        uint64_t pa;
        int ok;

        p = mmap(NULL, PAGE_SZ, PROT_READ | PROT_WRITE,
                 MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        if (p == MAP_FAILED)
            continue;
        if (mbind_to_node(p, PAGE_SZ, n) != 0) {
            munmap(p, PAGE_SZ);
            continue;
        }
        *(volatile uint8_t *)p = 1;
        mlock(p, PAGE_SZ);
        pa = virt_to_phys(p);
        ok = (pa >= base && pa < base + size);
        munlock(p, PAGE_SZ);
        munmap(p, PAGE_SZ);
        if (ok)
            return n;
    }
    return -1;
}

/* ---------------- main ---------------- */

int main(int argc, char **argv)
{
    const char *bdf = "0000:40:00.1";
    uint64_t base = 0x8080000000ULL;
    uint64_t size = 0x400000000ULL;
    uint64_t buf_off = 0, hpa = 0, target_hpa;
    unsigned cycles = 8000;
    int hold = 0, do_disarm = 0;
    int node, i;
    void *buf;
    volatile uint8_t *target = NULL;
    uint64_t b_min, b_med, a_min, a_med, rb_addr;
    uint16_t rb_cyc;
    int rb_en;

    for (i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--bdf") && i + 1 < argc)
            bdf = argv[++i];
        else if (!strcmp(argv[i], "--base") && i + 1 < argc)
            base = strtoull(argv[++i], NULL, 16);
        else if (!strcmp(argv[i], "--size") && i + 1 < argc)
            size = strtoull(argv[++i], NULL, 16);
        else if (!strcmp(argv[i], "--cycles") && i + 1 < argc)
            cycles = (unsigned)strtoul(argv[++i], NULL, 0);
        else if (!strcmp(argv[i], "--offset") && i + 1 < argc)
            buf_off = strtoull(argv[++i], NULL, 16);
        else if (!strcmp(argv[i], "--hold"))
            hold = 1;
        else if (!strcmp(argv[i], "--disarm"))
            do_disarm = 1;
        else {
            fprintf(stderr, "unknown option: %s\n", argv[i]);
            return 1;
        }
    }

    if (cycles > 65535) {
        fprintf(stderr, "cycles must be <= 65535 (16-bit CSR field)\n");
        return 1;
    }

    g_csr = map_csr(bdf);
    if (!g_csr)
        return 1;
    signal(SIGINT, on_signal);
    signal(SIGTERM, on_signal);
    atexit(stall_disarm);

    if (do_disarm) {
        stall_disarm();
        printf("stall disarmed.\n");
        return 0;
    }

    if (geteuid() != 0) {
        fprintf(stderr, "must run as root (pagemap returns zeroed PFNs otherwise)\n");
        return 1;
    }

    /* Confirm the CSR is live before trusting anything downstream. */
    {
        uint64_t rb;
        *(volatile uint64_t *)(g_csr + CSR_STALL_ADDR) = 0x5A5AA5A5DEADBEEFULL;
        _mm_sfence();
        usleep(50);
        rb = *(volatile uint64_t *)(g_csr + CSR_STALL_ADDR);
        *(volatile uint64_t *)(g_csr + CSR_STALL_ADDR) = 0;
        _mm_sfence();
        if (rb != 0x5A5AA5A5DEADBEEFULL) {
            fprintf(stderr,
                "CSR 0x1000 did not read back (got 0x%llx).\n"
                "CSRs are on PF1 BAR2 -- check --bdf.\n",
                (unsigned long long)rb);
            return 1;
        }
    }
    printf("CSR alive on %s BAR2\n", bdf);

    node = find_cxl_node(base, size);
    if (node < 0) {
        fprintf(stderr, "no NUMA node backs [0x%llx, 0x%llx)\n",
                (unsigned long long)base,
                (unsigned long long)(base + size));
        return 1;
    }
    printf("CXL memory is NUMA node %d\n", node);

    buf = mmap(NULL, (size_t)BUF_PAGES * PAGE_SZ, PROT_READ | PROT_WRITE,
               MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (buf == MAP_FAILED) {
        perror("mmap");
        return 1;
    }
    if (mbind_to_node(buf, (size_t)BUF_PAGES * PAGE_SZ, node) != 0) {
        perror("mbind");
        return 1;
    }
    memset(buf, 0xA5, (size_t)BUF_PAGES * PAGE_SZ);
    if (mlock(buf, (size_t)BUF_PAGES * PAGE_SZ) != 0)
        perror("mlock (continuing, but pages may migrate)");

    /* Find a page that actually landed in CXL memory. */
    for (i = 0; i < BUF_PAGES; i++) {
        void *va = (uint8_t *)buf + (size_t)i * PAGE_SZ;
        uint64_t pa = virt_to_phys(va);

        if (pa >= base && pa < base + size) {
            target = (volatile uint8_t *)va + (buf_off % PAGE_SZ);
            hpa = pa + (buf_off % PAGE_SZ);
            break;
        }
    }
    if (!target) {
        fprintf(stderr, "no allocated page landed in CXL range\n");
        return 1;
    }

    target_hpa = hpa & LINE_MASK;
    printf("target: va %p  hpa 0x%llx  line 0x%llx\n",
           (void *)target, (unsigned long long)hpa,
           (unsigned long long)target_hpa);

    {
        cpu_set_t set;
        CPU_ZERO(&set);
        CPU_SET(0, &set);
        sched_setaffinity(0, sizeof(set), &set);
    }

    stall_disarm();
    usleep(2000);
    b_min = measure(target, &b_med);
    printf("\nbefore arming: min %llu  median %llu cycles\n",
           (unsigned long long)b_min, (unsigned long long)b_med);

    stall_arm(target_hpa, (uint16_t)cycles);
    stall_readback(&rb_addr, &rb_cyc, &rb_en);
    printf("armed: addr=0x%llx cycles=%u en=%d\n",
           (unsigned long long)rb_addr, rb_cyc, rb_en);
    if (rb_addr != target_hpa || !rb_en || rb_cyc != cycles)
        printf("WARNING: readback differs from what was written\n");

    a_min = measure(target, &a_med);
    printf("after arming:  min %llu  median %llu cycles\n",
           (unsigned long long)a_min, (unsigned long long)a_med);

    if (a_min > b_min * 3)
        printf("\nSTALL ACTIVE: %.1fx slower (+%llu cycles)\n",
               (double)a_min / (double)b_min,
               (unsigned long long)(a_min - b_min));
    else
        printf("\nNo stall detected. Check that --base matches "
               "region2/resource.\n");

    if (hold) {
        printf("\nHolding armed. The buffer stays allocated and locked.\n"
               "Press Enter to disarm and exit.\n");
        getchar();
    }

    stall_disarm();
    printf("disarmed.\n");
    return 0;
}