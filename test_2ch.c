/*
 * test_2ch.c - two concurrent stalls using the bit-7 channel interleave.
 *
 * Build: gcc -O2 -pthread -o test_2ch test_2ch.c
 * Run:   sudo ./test_2ch [--bdf B] [--base HEX] [--size HEX]
 *                        [--cycles N] [--ms N]
 *
 * cxlip_top_pkg.sv:
 *   CXLIP_CHAN_ADDR_LSB = (MC_CHANNEL==4) ? 8 : ((MC_CHANNEL==2) ? 7 : 6)
 *
 * With MC_CHANNEL==2 the AXI channel is selected by address bit 7, i.e.
 * 128-byte interleave. Earlier tests only ever used page-aligned addresses,
 * where bit 7 is always 0, so every request went to channel 0 and only one
 * stall could ever be active.
 *
 * This sweeps pairs (base+0, base+delta) for several deltas. Only deltas
 * that flip bit 7 should put the two addresses on different channels and
 * allow max_concurrent to reach 2.
 *
 *   delta 0x40  -> bit7 same     -> expect 1
 *   delta 0x80  -> bit7 flipped  -> expect 2
 *   delta 0xC0  -> bit7 flipped  -> expect 2
 *   delta 0x100 -> bit7 same     -> expect 1
 *
 * That pattern, if it holds, confirms bit 7 is the channel select.
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

#define CSR_ADDR0 0x1000
#define CSR_CTRL  0x1008
#define CSR_ADDR1 0x1010
#define CSR_OCC   0x1020
#define CSR_MAP   0x2000

#define PAGE_SZ   4096
#define BUF_PAGES 256

#define MPOL_BIND      2
#define MPOL_MF_MOVE   (1<<1)
#define MPOL_MF_STRICT (1<<0)

static volatile uint8_t *g_csr;

static void disarm(void)
{
    if (g_csr) { *(volatile uint64_t *)(g_csr + CSR_CTRL) = 0; _mm_sfence(); }
}
static void on_sig(int s) { disarm(); _exit(128 + s); }

static void arm(uint64_t a0, uint64_t a1, uint16_t cyc)
{
    *(volatile uint64_t *)(g_csr + CSR_ADDR0) = a0;
    *(volatile uint64_t *)(g_csr + CSR_ADDR1) = a1;
    _mm_sfence();
    *(volatile uint64_t *)(g_csr + CSR_CTRL) = ((uint64_t)cyc << 1) | 1ULL;
    _mm_sfence();
    usleep(200);
}

static int pmfd = -1;
static uint64_t v2p(void *va)
{
    uint64_t e, pfn;
    if (pmfd < 0 && (pmfd = open("/proc/self/pagemap", O_RDONLY)) < 0) return 0;
    if (pread(pmfd, &e, 8, ((uintptr_t)va / PAGE_SZ) * 8) != 8) return 0;
    if (!(e & (1ULL << 63))) return 0;
    pfn = e & ((1ULL << 55) - 1);
    return pfn ? pfn * PAGE_SZ + ((uintptr_t)va % PAGE_SZ) : 0;
}

static int mbindn(void *a, size_t l, int n)
{
    unsigned long m[16];
    memset(m, 0, sizeof(m));
    m[n / (8 * sizeof(unsigned long))] |= 1UL << (n % (8 * sizeof(unsigned long)));
    return (int)syscall(__NR_mbind, a, l, MPOL_BIND, m,
                        16 * 8 * sizeof(unsigned long),
                        MPOL_MF_MOVE | MPOL_MF_STRICT);
}

static int find_node(uint64_t base, uint64_t size)
{
    DIR *d = opendir("/sys/devices/system/node");
    struct dirent *e; int nmax = -1, n;
    if (!d) return -1;
    while ((e = readdir(d)))
        { int k; if (sscanf(e->d_name,"node%d",&k)==1 && k>nmax) nmax=k; }
    closedir(d);
    for (n = 0; n <= nmax; n++) {
        void *p = mmap(NULL, PAGE_SZ, PROT_READ|PROT_WRITE,
                       MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
        uint64_t pa; int ok;
        if (p == MAP_FAILED) continue;
        if (mbindn(p, PAGE_SZ, n) != 0) { munmap(p, PAGE_SZ); continue; }
        *(volatile uint8_t *)p = 1; mlock(p, PAGE_SZ);
        pa = v2p(p); ok = (pa >= base && pa < base + size);
        munlock(p, PAGE_SZ); munmap(p, PAGE_SZ);
        if (ok) return n;
    }
    return -1;
}

struct hammer { volatile uint8_t *a; volatile int *run; int cpu; uint64_t n; };

static void *hammer_fn(void *arg)
{
    struct hammer *h = arg;
    cpu_set_t s;
    CPU_ZERO(&s); CPU_SET(h->cpu, &s);
    pthread_setaffinity_np(pthread_self(), sizeof(s), &s);
    while (*h->run) {
        uint64_t v;
        _mm_clflush((const void *)h->a);
        _mm_mfence();
        v = *(volatile uint64_t *)h->a;
        __asm__ __volatile__("" :: "r"(v));
        h->n++;
    }
    return NULL;
}

int main(int argc, char **argv)
{
    const char *bdf = "0000:40:00.1";
    uint64_t base = 0x8080000000ULL, size = 0x400000000ULL, pa = 0;
    unsigned cyc = 8000, ms = 300;
    const uint64_t deltas[] = { 0x40, 0x80, 0xC0, 0x100, 0x180, 0x200 };
    char path[512];
    void *buf; volatile uint8_t *page = NULL;
    int fd, node, i, best = -1;

    for (i = 1; i < argc; i++) {
        if (!strcmp(argv[i],"--bdf") && i+1<argc) bdf = argv[++i];
        else if (!strcmp(argv[i],"--base") && i+1<argc) base = strtoull(argv[++i],NULL,16);
        else if (!strcmp(argv[i],"--size") && i+1<argc) size = strtoull(argv[++i],NULL,16);
        else if (!strcmp(argv[i],"--cycles") && i+1<argc) cyc = (unsigned)strtoul(argv[++i],NULL,0);
        else if (!strcmp(argv[i],"--ms") && i+1<argc) ms = (unsigned)strtoul(argv[++i],NULL,0);
    }

    snprintf(path, sizeof(path), "/sys/bus/pci/devices/%s/resource2", bdf);
    fd = open(path, O_RDWR | O_SYNC);
    if (fd < 0) { perror("open BAR2"); return 1; }
    g_csr = mmap(NULL, CSR_MAP, PROT_READ|PROT_WRITE, MAP_SHARED, fd, 0);
    close(fd);
    if (g_csr == MAP_FAILED) { perror("mmap"); return 1; }
    signal(SIGINT,on_sig); signal(SIGTERM,on_sig); atexit(disarm);

    if (geteuid() != 0) { fprintf(stderr,"run as root\n"); return 1; }

    node = find_node(base, size);
    if (node < 0) { fprintf(stderr,"no CXL NUMA node\n"); return 1; }

    buf = mmap(NULL,(size_t)BUF_PAGES*PAGE_SZ,PROT_READ|PROT_WRITE,
               MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
    if (buf == MAP_FAILED) { perror("mmap"); return 1; }
    if (mbindn(buf,(size_t)BUF_PAGES*PAGE_SZ,node)!=0) { perror("mbind"); return 1; }
    memset(buf,0xA5,(size_t)BUF_PAGES*PAGE_SZ);
    mlock(buf,(size_t)BUF_PAGES*PAGE_SZ);

    for (i = 0; i < BUF_PAGES; i++) {
        void *p = (uint8_t*)buf + (size_t)i*PAGE_SZ;
        uint64_t q = v2p(p);
        if (q >= base && q < base + size) { page = p; pa = q; break; }
    }
    if (!page) { fprintf(stderr,"no CXL page\n"); return 1; }

    printf("page pa 0x%llx  (bit7 = %llu)\n",
           (unsigned long long)pa, (unsigned long long)((pa >> 7) & 1));
    printf("channel select is address bit 7 (MC_CHANNEL=2, 128B interleave)\n");
    printf("%u stall cycles, %u ms per pair\n\n", cyc, ms);
    printf("  delta   pa0             pa1             bit7  max  ch0      ch1\n");
    printf("  ------  --------------  --------------  ----  ---  -------  -------\n");

    for (i = 0; i < (int)(sizeof(deltas)/sizeof(deltas[0])); i++) {
        uint64_t d = deltas[i];
        uint64_t p0 = pa, p1 = pa + d;
        pthread_t t0, t1;
        struct hammer h0, h1;
        volatile int run = 1;
        uint64_t occ;
        unsigned maxc;
        int diff_ch = (int)(((p0 >> 7) & 1) ^ ((p1 >> 7) & 1));

        disarm(); usleep(2000);
        arm(p0, p1, (uint16_t)cyc);

        memset(&h0,0,sizeof(h0)); memset(&h1,0,sizeof(h1));
        h0.a = page;     h0.run = &run; h0.cpu = 0;
        h1.a = page + d; h1.run = &run; h1.cpu = 1;
        pthread_create(&t0,NULL,hammer_fn,&h0);
        pthread_create(&t1,NULL,hammer_fn,&h1);
        usleep((useconds_t)ms*1000);
        run = 0;
        pthread_join(t0,NULL); pthread_join(t1,NULL);

        occ = *(volatile uint64_t *)(g_csr + CSR_OCC);
        disarm();
        maxc = (unsigned)((occ >> 8) & 0xF);

        printf("  0x%04llx  0x%012llx  0x%012llx  %s  %2u   %7llu  %7llu %s\n",
               (unsigned long long)d,
               (unsigned long long)p0, (unsigned long long)p1,
               diff_ch ? "DIFF" : "same", maxc,
               (unsigned long long)((occ>>16)&0xFFFF),
               (unsigned long long)((occ>>32)&0xFFFF),
               (maxc >= 2) ? " *** 2 CONCURRENT ***" : "");

        if (maxc >= 2 && best < 0) best = i;
    }

    disarm();
    printf("\n");
    if (best >= 0)
        printf("Two concurrent stalls achieved at delta 0x%llx.\n"
               "Occupancy = 2 with both channels counting events.\n",
               (unsigned long long)deltas[best]);
    else
        printf("Still no pair reached 2. If ch1 events are now nonzero the\n"
               "channel split is working and only the overlap window is too\n"
               "short -- try --cycles 30000. If ch1 is still zero, check the\n"
               "MC_CHANNEL value in your project's cxlip_top_pkg.sv.\n");
    return 0;
}