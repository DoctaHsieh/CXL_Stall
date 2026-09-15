/*
 * test_stall.c - drive two concurrent stalls and read the occupancy CSR.
 *
 * Build: gcc -O2 -pthread -o test_stall test_stall.c
 * Run:   sudo ./test_stall [options]
 *
 *   --bdf    <bdf>   CSR function            (default 0000:40:00.1)
 *   --base   <hex>   CXL HPA base            (default 8080000000)
 *   --size   <hex>   CXL window size         (default 400000000)
 *   --cycles <n>     stall cycles 1-65535    (default 8000)
 *   --ms     <n>     hammer duration per pair in ms (default 200)
 *   --pairs  <n>     how many address pairs to try   (default 8)
 *   --single         also run the single-address regression check first
 *   --disarm         clear the stall and exit
 *
 * Why two threads: a single thread issues one load at a time, so it can
 * never have two reads outstanding. Occupancy would cap at 1 no matter how
 * the addresses map. Two threads pinned to separate cores can.
 *
 * Why a pair sweep: the stall works by holding arready low, which is
 * backpressure on a whole AXI port. Two addresses on the SAME channel
 * cannot stall concurrently -- the first blocks the port and the second
 * request never reaches the comparator. Only a pair that lands on
 * DIFFERENT channels can produce occupancy 2. The channel mapping is
 * unknown, so we try several pairs and report which one works.
 *
 * CSR map (PF1 BAR2):
 *   0x1000 csr_stall_addr   RW
 *   0x1008 bit0 en, bits16:1 cycles   RW
 *   0x1010 csr_stall_addr1  RW   (new)
 *   0x1020 occupancy        RO   (new)
 *            [1:0]   per-channel stalling now
 *            [11:8]  max concurrent seen (sticky, clears when en=0)
 *            [31:16] ch0 stall events
 *            [47:32] ch1 stall events
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
#include <pthread.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <x86intrin.h>

#define CSR_ADDR0  0x1000
#define CSR_CTRL   0x1008
#define CSR_ADDR1  0x1010
#define CSR_OCC    0x1020
#define CSR_MAP    0x2000

#define PAGE_SZ    4096
#define BUF_PAGES  2048          /* 8 MB, gives plenty of distinct frames */
#define REPS       128

#define MPOL_BIND      2
#define MPOL_MF_MOVE   (1<<1)
#define MPOL_MF_STRICT (1<<0)

static volatile uint8_t *g_csr = NULL;

/* ---------------- CSR ---------------- */

static void stall_disarm(void)
{
    if (!g_csr)
        return;
    *(volatile uint64_t *)(g_csr + CSR_CTRL) = 0;
    _mm_sfence();
}

static void on_signal(int sig)
{
    stall_disarm();
    fprintf(stderr, "\nsignal %d: disarmed.\n", sig);
    _exit(128 + sig);
}

static void stall_arm2(uint64_t a0, uint64_t a1, uint16_t cycles)
{
    /* Addresses first, then the enable. Arming before the targets are
     * stable could briefly match the wrong line. */
    *(volatile uint64_t *)(g_csr + CSR_ADDR0) = a0;
    *(volatile uint64_t *)(g_csr + CSR_ADDR1) = a1;
    _mm_sfence();
    *(volatile uint64_t *)(g_csr + CSR_CTRL) = ((uint64_t)cycles << 1) | 1ULL;
    _mm_sfence();
    usleep(200);
}

static uint64_t read_occ(void)
{
    uint64_t v = *(volatile uint64_t *)(g_csr + CSR_OCC);
    _mm_lfence();
    return v;
}

static void print_occ(const char *tag, uint64_t occ)
{
    printf("  %s occ=0x%016llx  active=%llu%llu  max_concurrent=%llu  "
           "ch0_events=%llu  ch1_events=%llu\n",
           tag, (unsigned long long)occ,
           (unsigned long long)((occ >> 1) & 1),
           (unsigned long long)(occ & 1),
           (unsigned long long)((occ >> 8) & 0xF),
           (unsigned long long)((occ >> 16) & 0xFFFF),
           (unsigned long long)((occ >> 32) & 0xFFFF));
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
    p = mmap(NULL, CSR_MAP, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
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

static uint64_t measure(volatile uint8_t *p)
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
    return s[0];
}

/* ---------------- pagemap / NUMA ---------------- */

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
    while ((e = readdir(d)))
        { int n; if (sscanf(e->d_name, "node%d", &n) == 1 && n > max) max = n; }
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

/* ---------------- hammer threads ---------------- */

struct hammer {
    volatile uint8_t *addr;
    volatile int     *run;
    int               cpu;
    uint64_t          iters;
};

static void *hammer_fn(void *arg)
{
    struct hammer *h = (struct hammer *)arg;
    cpu_set_t set;

    CPU_ZERO(&set);
    CPU_SET(h->cpu, &set);
    pthread_setaffinity_np(pthread_self(), sizeof(set), &set);

    while (*h->run) {
        uint64_t v;
        _mm_clflush((const void *)h->addr);
        _mm_mfence();
        v = *(volatile uint64_t *)h->addr;
        __asm__ __volatile__("" :: "r"(v));
        h->iters++;
    }
    return NULL;
}

/* Run both threads against a0/a1 for ms milliseconds, return final occupancy. */
static uint64_t run_pair(volatile uint8_t *va0, volatile uint8_t *va1,
                         uint64_t pa0, uint64_t pa1,
                         uint16_t cycles, int ms)
{
    pthread_t t0, t1;
    struct hammer h0, h1;
    volatile int run = 1;
    uint64_t occ;

    /* Disarm first so the sticky counters clear, then arm on this pair. */
    stall_disarm();
    usleep(2000);
    stall_arm2(pa0, pa1, cycles);

    memset(&h0, 0, sizeof(h0));
    memset(&h1, 0, sizeof(h1));
    h0.addr = va0; h0.run = &run; h0.cpu = 0;
    h1.addr = va1; h1.run = &run; h1.cpu = 1;

    pthread_create(&t0, NULL, hammer_fn, &h0);
    pthread_create(&t1, NULL, hammer_fn, &h1);

    usleep((useconds_t)ms * 1000);
    run = 0;
    pthread_join(t0, NULL);
    pthread_join(t1, NULL);

    occ = read_occ();
    stall_disarm();
    return occ;
}

/* ---------------- main ---------------- */

int main(int argc, char **argv)
{
    const char *bdf = "0000:40:00.1";
    uint64_t base = 0x8080000000ULL, size = 0x400000000ULL;
    unsigned cycles = 8000, ms = 200, npairs = 8;
    int do_single = 0, do_disarm = 0;
    int node, i, found = -1;
    void *buf;
    volatile uint8_t **va;
    uint64_t *pa;
    int ncand = 0;

    for (i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--bdf") && i + 1 < argc) bdf = argv[++i];
        else if (!strcmp(argv[i], "--base") && i + 1 < argc)
            base = strtoull(argv[++i], NULL, 16);
        else if (!strcmp(argv[i], "--size") && i + 1 < argc)
            size = strtoull(argv[++i], NULL, 16);
        else if (!strcmp(argv[i], "--cycles") && i + 1 < argc)
            cycles = (unsigned)strtoul(argv[++i], NULL, 0);
        else if (!strcmp(argv[i], "--ms") && i + 1 < argc)
            ms = (unsigned)strtoul(argv[++i], NULL, 0);
        else if (!strcmp(argv[i], "--pairs") && i + 1 < argc)
            npairs = (unsigned)strtoul(argv[++i], NULL, 0);
        else if (!strcmp(argv[i], "--single")) do_single = 1;
        else if (!strcmp(argv[i], "--disarm")) do_disarm = 1;
        else { fprintf(stderr, "unknown option: %s\n", argv[i]); return 1; }
    }
    if (cycles > 65535) {
        fprintf(stderr, "cycles must be <= 65535\n");
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
        printf("disarmed.\n");
        return 0;
    }
    if (geteuid() != 0) {
        fprintf(stderr, "must run as root (pagemap)\n");
        return 1;
    }

    /* Verify both address registers exist. 0x1010 only responds on the
     * new bitstream; on the old one it reads back as zero. */
    {
        uint64_t r0, r1;
        *(volatile uint64_t *)(g_csr + CSR_ADDR0) = 0xA5A5DEADBEEF0000ULL;
        *(volatile uint64_t *)(g_csr + CSR_ADDR1) = 0x5A5AFEEDFACE1111ULL;
        _mm_sfence();
        usleep(100);
        r0 = *(volatile uint64_t *)(g_csr + CSR_ADDR0);
        r1 = *(volatile uint64_t *)(g_csr + CSR_ADDR1);
        *(volatile uint64_t *)(g_csr + CSR_ADDR0) = 0;
        *(volatile uint64_t *)(g_csr + CSR_ADDR1) = 0;
        _mm_sfence();

        if (r0 != 0xA5A5DEADBEEF0000ULL) {
            fprintf(stderr, "0x1000 did not read back -- check --bdf\n");
            return 1;
        }
        if (r1 != 0x5A5AFEEDFACE1111ULL) {
            fprintf(stderr,
                "0x1010 did not read back (got 0x%llx).\n"
                "This bitstream does not have the second address register.\n",
                (unsigned long long)r1);
            return 1;
        }
    }
    printf("CSR alive: 0x1000 and 0x1010 both read back on %s BAR2\n", bdf);

    node = find_cxl_node(base, size);
    if (node < 0) {
        fprintf(stderr, "no NUMA node backs the CXL window\n");
        return 1;
    }
    printf("CXL memory is NUMA node %d\n", node);

    buf = mmap(NULL, (size_t)BUF_PAGES * PAGE_SZ, PROT_READ | PROT_WRITE,
               MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (buf == MAP_FAILED) { perror("mmap"); return 1; }
    if (mbind_to_node(buf, (size_t)BUF_PAGES * PAGE_SZ, node) != 0) {
        perror("mbind"); return 1;
    }
    memset(buf, 0xA5, (size_t)BUF_PAGES * PAGE_SZ);
    if (mlock(buf, (size_t)BUF_PAGES * PAGE_SZ) != 0)
        perror("mlock (continuing)");

    /* Collect candidate lines that really landed in CXL memory. */
    va = calloc(BUF_PAGES, sizeof(*va));
    pa = calloc(BUF_PAGES, sizeof(*pa));
    if (!va || !pa) { perror("calloc"); return 1; }

    for (i = 0; i < BUF_PAGES; i++) {
        void *p = (uint8_t *)buf + (size_t)i * PAGE_SZ;
        uint64_t phys = virt_to_phys(p);
        if (phys >= base && phys < base + size) {
            va[ncand] = (volatile uint8_t *)p;
            pa[ncand] = phys;
            ncand++;
        }
    }
    printf("%d candidate pages in CXL range\n\n", ncand);
    if (ncand < 2) {
        fprintf(stderr, "need at least 2 pages in CXL range\n");
        return 1;
    }

    if (do_single) {
        uint64_t b, a;
        printf("=== single-address regression check ===\n");
        stall_disarm();
        usleep(2000);
        b = measure(va[0]);
        stall_arm2(pa[0], 0, (uint16_t)cycles);
        a = measure(va[0]);
        stall_disarm();
        printf("  before %llu  after %llu  -> %s\n\n",
               (unsigned long long)b, (unsigned long long)a,
               (a > b * 3) ? "STALL OK" : "NO STALL");
    }

    printf("=== sweeping %u address pairs, %u ms each, %u stall cycles ===\n",
           npairs, ms, cycles);
    printf("looking for max_concurrent = 2 (two channels stalling at once)\n\n");

    for (i = 0; i < (int)npairs && i + 1 < ncand; i++) {
        uint64_t occ;
        int idx0 = 0, idx1 = i + 1;
        unsigned maxc;

        occ = run_pair(va[idx0], va[idx1], pa[idx0], pa[idx1],
                       (uint16_t)cycles, (int)ms);
        maxc = (unsigned)((occ >> 8) & 0xF);

        printf("pair %d: pa0 0x%llx  pa1 0x%llx  (xor 0x%llx)\n", i,
               (unsigned long long)pa[idx0], (unsigned long long)pa[idx1],
               (unsigned long long)(pa[idx0] ^ pa[idx1]));
        print_occ("       ", occ);

        if (maxc >= 2) {
            printf("       *** TWO CONCURRENT STALLS ***\n");
            if (found < 0)
                found = i;
        }
        printf("\n");
    }

    stall_disarm();

    if (found >= 0) {
        printf("Success: pair %d produced two concurrent stalls.\n", found);
        printf("Those two addresses map to different AXI channels.\n");
    } else {
        printf("No pair reached max_concurrent = 2.\n"
               "Possible reasons:\n"
               "  - every pair tried landed on the same channel; raise --pairs\n"
               "  - the stall window is too short to overlap; raise --cycles\n"
               "  - occupancy is wired but never updated; check that\n"
               "    ch0/ch1 event counts above are nonzero. If events are\n"
               "    counting but max stays 1, that IS the head-of-line\n"
               "    result: one port at a time, which is the known limit.\n");
    }
    return 0;
}