/*
 * test_stall2ch.c - demonstrate two concurrent CXL read stalls.
 *
 * Build: gcc -O2 -pthread -o test_stall2ch test_stall2ch.c
 * Run:   sudo ./test_stall2ch [options]
 *
 *   --bdf    <bdf>  CSR function          (default 0000:40:00.1)
 *   --base   <hex>  CXL HPA base          (default 8080000000)
 *   --size   <hex>  CXL window size       (default 400000000)
 *   --cycles <n>    stall cycles 1-65535  (default 8000)
 *   --ms     <n>    hammer duration ms    (default 300)
 *   --delta  <hex>  offset of 2nd address (default 40)
 *   --table         sweep several deltas and print the channel table
 *   --disarm        clear the stall and exit
 *
 * MEASURED FACTS this is built on:
 *   - araddr carries the RAW host physical address. No HDM base subtract,
 *     no interleave transform. Established by sweeping nine candidate
 *     transforms; only the identity fired.
 *   - The AXI channel is selected by address BIT 6, i.e. 64-byte
 *     interleave: consecutive cache lines alternate between the two
 *     channels. Established by sweeping deltas and observing which
 *     produced two concurrent stalls.
 *
 * WHY TWO CHANNELS MATTER: the stall works by holding arready low, which
 * is backpressure on a whole AXI port, not on one address. Two addresses
 * on the SAME channel serialize -- the first blocks the port and the
 * second request never reaches the comparator. Only addresses on
 * different channels can stall at the same time.
 *
 * CSR map (PF1 BAR2):
 *   0x1000 csr_stall_addr    RW
 *   0x1008 bit0 en, bits16:1 cycles   RW
 *   0x1010 csr_stall_addr1   RW
 *   0x1020 occupancy         RO
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

#define CSR_ADDR0 0x1000
#define CSR_CTRL  0x1008
#define CSR_ADDR1 0x1010
#define CSR_OCC   0x1020
#define CSR_MAP   0x2000

#define CHAN_BIT  6              /* measured: 64B interleave */

#define PAGE_SZ   4096
#define BUF_PAGES 256
#define REPS      128

#define MPOL_BIND      2
#define MPOL_MF_MOVE   (1<<1)
#define MPOL_MF_STRICT (1<<0)

static volatile uint8_t *g_csr;

/* ---------------- CSR ---------------- */

static void disarm(void)
{
    if (g_csr) { *(volatile uint64_t *)(g_csr + CSR_CTRL) = 0; _mm_sfence(); }
}
static void on_sig(int s)
{
    disarm();
    fprintf(stderr, "\nsignal %d: disarmed.\n", s);
    _exit(128 + s);
}

static void arm2(uint64_t a0, uint64_t a1, uint16_t cyc)
{
    /* Addresses before the enable: arming while the targets are still
     * settling could briefly match the wrong line. */
    *(volatile uint64_t *)(g_csr + CSR_ADDR0) = a0;
    *(volatile uint64_t *)(g_csr + CSR_ADDR1) = a1;
    _mm_sfence();
    *(volatile uint64_t *)(g_csr + CSR_CTRL) = ((uint64_t)cyc << 1) | 1ULL;
    _mm_sfence();
    usleep(200);
}

static uint64_t read_occ(void)
{
    uint64_t v = *(volatile uint64_t *)(g_csr + CSR_OCC);
    _mm_lfence();
    return v;
}

#define OCC_ACTIVE(o) ((unsigned)((o) & 0x3))
#define OCC_MAX(o)    ((unsigned)(((o) >> 8) & 0xF))
#define OCC_CH0(o)    ((unsigned long long)(((o) >> 16) & 0xFFFF))
#define OCC_CH1(o)    ((unsigned long long)(((o) >> 32) & 0xFFFF))

/* ---------------- timing ---------------- */

static inline uint64_t t0_(void)
{ unsigned a,d; __asm__ __volatile__("lfence\n\trdtsc":"=a"(a),"=d"(d)::"memory");
  return ((uint64_t)d<<32)|a; }
static inline uint64_t t1_(void)
{ unsigned a,d,c; __asm__ __volatile__("rdtscp\n\tlfence":"=a"(a),"=d"(d),"=c"(c)::"memory");
  return ((uint64_t)d<<32)|a; }

static int cmpu(const void *x, const void *y)
{ uint64_t a=*(const uint64_t*)x,b=*(const uint64_t*)y; return (a>b)-(a<b); }

static uint64_t measure(volatile uint8_t *p)
{
    static uint64_t s[REPS];
    int i;
    for (i = 0; i < REPS; i++) {
        uint64_t a, b, v;
        _mm_clflush((const void *)p); _mm_mfence();
        a = t0_(); v = *(volatile uint64_t *)p; b = t1_();
        __asm__ __volatile__("" :: "r"(v));
        s[i] = b - a;
    }
    qsort(s, REPS, sizeof(s[0]), cmpu);
    return s[0];
}

/* ---------------- memory ---------------- */

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
    m[n / (8*sizeof(unsigned long))] |= 1UL << (n % (8*sizeof(unsigned long)));
    return (int)syscall(__NR_mbind, a, l, MPOL_BIND, m,
                        16*8*sizeof(unsigned long),
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

/* ---------------- hammer ---------------- */

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

/* Hammer both lines concurrently, return final occupancy. */
static uint64_t run_pair(volatile uint8_t *v0, volatile uint8_t *v1,
                         uint64_t p0, uint64_t p1, uint16_t cyc, int ms,
                         uint64_t *it0, uint64_t *it1)
{
    pthread_t t0, t1;
    struct hammer h0, h1;
    volatile int run = 1;
    uint64_t occ;

    disarm(); usleep(2000);          /* clears the sticky counters */
    arm2(p0, p1, cyc);

    memset(&h0,0,sizeof(h0)); memset(&h1,0,sizeof(h1));
    h0.a = v0; h0.run = &run; h0.cpu = 0;
    h1.a = v1; h1.run = &run; h1.cpu = 1;
    pthread_create(&t0,NULL,hammer_fn,&h0);
    pthread_create(&t1,NULL,hammer_fn,&h1);
    usleep((useconds_t)ms * 1000);
    run = 0;
    pthread_join(t0,NULL); pthread_join(t1,NULL);

    occ = read_occ();
    disarm();
    if (it0) *it0 = h0.n;
    if (it1) *it1 = h1.n;
    return occ;
}

/* ---------------- main ---------------- */

int main(int argc, char **argv)
{
    const char *bdf = "0000:40:00.1";
    uint64_t base = 0x8080000000ULL, size = 0x400000000ULL;
    uint64_t pa = 0, delta = 0x40;
    unsigned cyc = 8000, ms = 300;
    int table = 0, do_disarm = 0;
    char path[512];
    void *buf; volatile uint8_t *page = NULL;
    int fd, node, i;

    for (i = 1; i < argc; i++) {
        if (!strcmp(argv[i],"--bdf") && i+1<argc) bdf = argv[++i];
        else if (!strcmp(argv[i],"--base") && i+1<argc) base = strtoull(argv[++i],NULL,16);
        else if (!strcmp(argv[i],"--size") && i+1<argc) size = strtoull(argv[++i],NULL,16);
        else if (!strcmp(argv[i],"--cycles") && i+1<argc) cyc = (unsigned)strtoul(argv[++i],NULL,0);
        else if (!strcmp(argv[i],"--ms") && i+1<argc) ms = (unsigned)strtoul(argv[++i],NULL,0);
        else if (!strcmp(argv[i],"--delta") && i+1<argc) delta = strtoull(argv[++i],NULL,16);
        else if (!strcmp(argv[i],"--table")) table = 1;
        else if (!strcmp(argv[i],"--disarm")) do_disarm = 1;
        else { fprintf(stderr,"unknown option: %s\n", argv[i]); return 1; }
    }
    if (cyc > 65535) { fprintf(stderr,"cycles must be <= 65535\n"); return 1; }

    snprintf(path, sizeof(path), "/sys/bus/pci/devices/%s/resource2", bdf);
    fd = open(path, O_RDWR | O_SYNC);
    if (fd < 0) { perror("open BAR2"); return 1; }
    g_csr = mmap(NULL, CSR_MAP, PROT_READ|PROT_WRITE, MAP_SHARED, fd, 0);
    close(fd);
    if (g_csr == MAP_FAILED) { perror("mmap"); return 1; }
    signal(SIGINT,on_sig); signal(SIGTERM,on_sig); atexit(disarm);

    if (do_disarm) { disarm(); printf("disarmed.\n"); return 0; }
    if (geteuid() != 0) { fprintf(stderr,"must run as root (pagemap)\n"); return 1; }

    /* Both address registers must respond, or this is the old bitstream. */
    {
        uint64_t r0, r1;
        *(volatile uint64_t *)(g_csr + CSR_ADDR0) = 0xA5A5DEADBEEF0000ULL;
        *(volatile uint64_t *)(g_csr + CSR_ADDR1) = 0x5A5AFEEDFACE1111ULL;
        _mm_sfence(); usleep(100);
        r0 = *(volatile uint64_t *)(g_csr + CSR_ADDR0);
        r1 = *(volatile uint64_t *)(g_csr + CSR_ADDR1);
        *(volatile uint64_t *)(g_csr + CSR_ADDR0) = 0;
        *(volatile uint64_t *)(g_csr + CSR_ADDR1) = 0;
        _mm_sfence();
        if (r0 != 0xA5A5DEADBEEF0000ULL) {
            fprintf(stderr,"0x1000 did not read back -- check --bdf\n"); return 1;
        }
        if (r1 != 0x5A5AFEEDFACE1111ULL) {
            fprintf(stderr,"0x1010 did not read back -- old bitstream?\n"); return 1;
        }
    }
    printf("CSR alive: 0x1000 and 0x1010 both respond on %s BAR2\n", bdf);

    node = find_node(base, size);
    if (node < 0) { fprintf(stderr,"no NUMA node backs the CXL window\n"); return 1; }
    printf("CXL memory is NUMA node %d\n", node);

    buf = mmap(NULL,(size_t)BUF_PAGES*PAGE_SZ,PROT_READ|PROT_WRITE,
               MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
    if (buf == MAP_FAILED) { perror("mmap"); return 1; }
    if (mbindn(buf,(size_t)BUF_PAGES*PAGE_SZ,node)!=0) { perror("mbind"); return 1; }
    memset(buf,0xA5,(size_t)BUF_PAGES*PAGE_SZ);
    if (mlock(buf,(size_t)BUF_PAGES*PAGE_SZ) != 0) perror("mlock (continuing)");

    for (i = 0; i < BUF_PAGES; i++) {
        void *p = (uint8_t*)buf + (size_t)i*PAGE_SZ;
        uint64_t q = v2p(p);
        if (q >= base && q < base + size) { page = p; pa = q; break; }
    }
    if (!page) { fprintf(stderr,"no allocated page landed in CXL range\n"); return 1; }

    printf("page pa 0x%llx\n", (unsigned long long)pa);
    printf("channel select = address bit %d (64B interleave, measured)\n\n",
           CHAN_BIT);

    if (table) {
        const uint64_t ds[] = { 0x40, 0x80, 0xC0, 0x100, 0x140, 0x180,
                                0x1C0, 0x200 };
        printf("  delta   pa0             pa1             chan  max  ch0      ch1\n");
        printf("  ------  --------------  --------------  ----  ---  -------  -------\n");
        for (i = 0; i < (int)(sizeof(ds)/sizeof(ds[0])); i++) {
            uint64_t p0 = pa, p1 = pa + ds[i], occ;
            int diff = (int)(((p0 >> CHAN_BIT) & 1) ^ ((p1 >> CHAN_BIT) & 1));

            occ = run_pair(page, page + ds[i], p0, p1, (uint16_t)cyc,
                           (int)ms, NULL, NULL);
            printf("  0x%04llx  0x%012llx  0x%012llx  %s  %2u   %7llu  %7llu %s\n",
                   (unsigned long long)ds[i],
                   (unsigned long long)p0, (unsigned long long)p1,
                   diff ? "DIFF" : "same", OCC_MAX(occ),
                   OCC_CH0(occ), OCC_CH1(occ),
                   (OCC_MAX(occ) >= 2) ? " *** 2 CONCURRENT ***" : "");
        }
        printf("\nDIFF rows should reach 2; same rows should stay at 1.\n"
               "That is head-of-line blocking: arready backpressure stalls a\n"
               "PORT, so two addresses on one channel serialize.\n");
        return 0;
    }

    /* Single pair: baseline, then concurrent stall. */
    {
        uint64_t p0 = pa, p1 = pa + delta, occ, i0 = 0, i1 = 0;
        uint64_t b0, b1;
        int diff = (int)(((p0 >> CHAN_BIT) & 1) ^ ((p1 >> CHAN_BIT) & 1));

        printf("addr0 0x%llx  (channel %llu)\n",
               (unsigned long long)p0, (unsigned long long)((p0>>CHAN_BIT)&1));
        printf("addr1 0x%llx  (channel %llu)  delta 0x%llx  -> %s\n\n",
               (unsigned long long)p1, (unsigned long long)((p1>>CHAN_BIT)&1),
               (unsigned long long)delta,
               diff ? "different channels" : "SAME channel, will serialize");

        disarm(); usleep(2000);
        b0 = measure(page);
        b1 = measure(page + delta);
        printf("baseline: addr0 %llu cycles   addr1 %llu cycles\n",
               (unsigned long long)b0, (unsigned long long)b1);

        occ = run_pair(page, page + delta, p0, p1, (uint16_t)cyc,
                       (int)ms, &i0, &i1);

        printf("\nafter %u ms of concurrent hammering at %u stall cycles:\n", ms, cyc);
        printf("  occupancy raw   : 0x%016llx\n", (unsigned long long)occ);
        printf("  max concurrent  : %u\n", OCC_MAX(occ));
        printf("  ch0 stall events: %llu\n", OCC_CH0(occ));
        printf("  ch1 stall events: %llu\n", OCC_CH1(occ));
        printf("  thread0 reads   : %llu\n", (unsigned long long)i0);
        printf("  thread1 reads   : %llu\n", (unsigned long long)i1);

        if (OCC_MAX(occ) >= 2)
            printf("\nTWO CONCURRENT STALLS. Both channels stalled at the "
                   "same time.\n");
        else if (!diff)
            printf("\nOne at a time, as expected: both addresses are on the "
                   "same channel.\nTry --delta 40 for different channels.\n");
        else
            printf("\nExpected 2 but saw %u. Try --cycles 30000 to widen the "
                   "overlap window.\n", OCC_MAX(occ));
    }
    return 0;
}