/*
 * test_stall.c - exercise the queue-based CXL.mem read stall engine.
 *
 * Build: gcc -O2 -Wall -pthread -o test_stall test_stall.c
 * Run:   sudo ./test_stall [options]
 *
 *   --bdf    <bdf>  CSR function          (default 0000:40:00.1)
 *   --base   <hex>  CXL HPA base          (default 8080000000)
 *   --size   <hex>  CXL window size       (default 400000000)
 *   --cycles <n>    stall cycles          (default 2000)
 *   --ms     <n>    hammer duration, ms   (default 300, max 10000)
 *   --passes <n>    integrity passes      (default 3)
 *   --targets <n>   integrity armed lines (default 4). 2 = one per
 *                   channel, queue never full; 4 = two per channel
 *   --control       integrity: run the identical traffic with the stall
 *                   engine left disarmed (baseline for the design itself)
 *   --imode  <m>    integrity store mode  (default read)
 *                     read        no stores while stalls are armed
 *                     write-safe  rewrite while armed, skipping armed lines
 *                     write       rewrite everything while armed
 *   --test   <n>    arid | sanity | passthru | samechan | diffchan |
 *                   integrity | all | demo   (default all)
 *                   demo: one-screen narrated walk-through for showing
 *                   the engine to people; not part of "all"
 *   --disarm        clear the stall and exit
 *
 * Progress is appended to /var/tmp/test_stall.log with an fsync per
 * line; after a crash, its last line shows the step that was running.
 *
 * Recommended first run on a new bitstream:
 *   sudo ./test_stall --test sanity --cycles 200
 * then --test all. "all" stops at the first FAIL.
 *
 * CSR map:
 *   0x1008        bit0 en, bits16:1 cycles RW
 *   0x1018        target-enable bitmask   RW
 *   0x1020        channel 0 status        RO
 *   0x1028        channel 1 status        RO
 *   0x1100 + 8t   stall_addr[t]           RW
 *
 * status word:
 *   [7:0]   occupancy now
 *   [15:8]  max occupancy since last arm
 *   [31:16] stall events (diverted reads) since last arm, saturating
 *   [32]    queue-full sticky (every slot held; never blocks traffic)
 *   [33]    bypass sticky: a target was forwarded unstalled because
 *           every slot was already holding one
 *   [39:36] STALL_FIFO_DEPTH of the bitstream (0 = older bitstream)
 *   [47:40] sticky OR of every ARID accepted
 *   [63:48] cycles a same-ID request waited behind a held one, saturating
 *
 * Disarming (clearing bit0 of 0x1008) clears every counter except the
 * ARID OR, and releases all held reads within a few cycles.
 *
 * Channel is selected by address bit 6 (64B interleave): lines 0x40
 * apart are on opposite channels, 0x80 apart on the same one.
 *
 * Safety: the hardware force-releases any held read after
 * STALL_TIMEOUT (50000) afu_clk cycles, whatever this program does,
 * and this program disarms on exit and on SIGINT/SIGTERM. Always
 * disarm before changing targets; every test here does.
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
#include <stdarg.h>
#include <time.h>
#include <x86intrin.h>

#define CSR_CTRL    0x1008
#define CSR_TGT_EN  0x1018
#define CSR_ST_CH0  0x1020
#define CSR_ST_CH1  0x1028
#define CSR_ADDR_AR 0x1100
#define CSR_MAP     0x2000

#define NUM_TARGETS 4            /* must match afu_stall_pkg */
#define HW_TIMEOUT  50000        /* must match afu_stall_pkg */
#define CHAN_BIT    6
#define PAGE_SZ     4096
#define BUF_PAGES   2048         /* 8 MB */
#define REPS        256
#define NVERIFY     2            /* integrity verifier threads */
#define INTEGRITY_BYTES ((size_t)256 * PAGE_SZ)   /* 1 MB */

#define MPOL_BIND      2
#define MPOL_MF_MOVE   (1<<1)
#define MPOL_MF_STRICT (1<<0)

enum { PASS = 0, FAIL = 1, INCONCLUSIVE = 2 };
static const char *verdict_str[] = { "PASS", "FAIL", "INCONCLUSIVE" };

static volatile uint8_t *g_csr;
static int g_depth;              /* from status bits [39:36] */
static int g_ncpu;

/* ------------------------------------------------------------- CSR ---- */

static void disarm(void)
{
    if (g_csr) {
        *(volatile uint64_t *)(g_csr + CSR_CTRL) = 0;
        _mm_sfence();
    }
}
static void on_sig(int s)
{
    disarm();
    fprintf(stderr, "\nsignal %d: disarmed.\n", s);
    _exit(128 + s);
}

static uint64_t status(int ch)
{
    uint64_t v = *(volatile uint64_t *)(g_csr + (ch ? CSR_ST_CH1 : CSR_ST_CH0));
    _mm_lfence();
    return v;
}

#define ST_OCC(s)    ((unsigned)( (s)        & 0xFF))
#define ST_MAX(s)    ((unsigned)(((s) >>  8) & 0xFF))
#define ST_EVT(s)    ((unsigned)(((s) >> 16) & 0xFFFF))
#define ST_FULL(s)   ((unsigned)(((s) >> 32) & 0x1))
#define ST_BYP(s)    ((unsigned)(((s) >> 33) & 0x1))
#define ST_DEPTH(s)  ((unsigned)(((s) >> 36) & 0xF))
#define ST_ARID(s)   ((unsigned)(((s) >> 40) & 0xFF))
#define ST_CONFL(s)  ((unsigned)(((s) >> 48) & 0xFFFF))

static void print_st(const char *tag, uint64_t s0, uint64_t s1)
{
    printf("  %-8s ch0 occ=%u max=%u evt=%u%s full=%u byp=%u confl=%u | "
           "ch1 occ=%u max=%u evt=%u%s full=%u byp=%u confl=%u\n", tag,
           ST_OCC(s0), ST_MAX(s0), ST_EVT(s0), ST_EVT(s0) == 0xFFFF ? "+" : "",
           ST_FULL(s0), ST_BYP(s0), ST_CONFL(s0),
           ST_OCC(s1), ST_MAX(s1), ST_EVT(s1), ST_EVT(s1) == 0xFFFF ? "+" : "",
           ST_FULL(s1), ST_BYP(s1), ST_CONFL(s1));
}

/* Disarm, program up to NUM_TARGETS addresses (others zeroed and
 * disabled), then arm. Targets are never changed while armed. */
static void program_and_arm(const uint64_t *pa, int n, unsigned cyc)
{
    uint64_t mask = 0;
    disarm();
    usleep(1000);
    for (int t = 0; t < NUM_TARGETS; t++) {
        *(volatile uint64_t *)(g_csr + CSR_ADDR_AR + 8*t) = (t < n) ? pa[t] : 0;
        if (t < n) mask |= 1ULL << t;
    }
    _mm_sfence();
    *(volatile uint64_t *)(g_csr + CSR_TGT_EN) = mask;
    _mm_sfence();
    *(volatile uint64_t *)(g_csr + CSR_CTRL) = ((uint64_t)(cyc & 0xFFFF) << 1) | 1ULL;
    _mm_sfence();
    usleep(200);
}

/* After a disarm every held read must drain. If this ever fails the
 * engine is holding something it should not; stop testing. */
static int check_drained(void)
{
    for (int i = 0; i < 200; i++) {
        uint64_t s0 = status(0), s1 = status(1);
        if (ST_OCC(s0) == 0 && ST_OCC(s1) == 0) return 0;
        usleep(100);
    }
    printf("  FAIL: occupancy did not drain to 0 after disarm "
           "(ch0 occ=%u ch1 occ=%u).\n", ST_OCC(status(0)), ST_OCC(status(1)));
    return 1;
}

/* ---------------------------------------------------------- timing ---- */

static inline uint64_t tb(void)
{ unsigned a,d; __asm__ __volatile__("lfence\n\trdtsc":"=a"(a),"=d"(d)::"memory");
  return ((uint64_t)d<<32)|a; }
static inline uint64_t te(void)
{ unsigned a,d,c; __asm__ __volatile__("rdtscp\n\tlfence":"=a"(a),"=d"(d),"=c"(c)::"memory");
  return ((uint64_t)d<<32)|a; }

static int cmpu(const void *x, const void *y)
{ uint64_t a=*(const uint64_t*)x,b=*(const uint64_t*)y; return (a>b)-(a<b); }

struct lat { uint64_t min, med, p90, max; };

static struct lat measure(volatile uint8_t *p)
{
    static uint64_t s[REPS];
    struct lat r;
    for (int i = 0; i < REPS; i++) {
        uint64_t a, b, v;
        _mm_clflush((const void *)p); _mm_mfence();
        a = tb(); v = *(volatile uint64_t *)p; b = te();
        __asm__ __volatile__("" :: "r"(v));
        s[i] = b - a;
        usleep(20);              /* spread samples across stall phases */
    }
    qsort(s, REPS, sizeof(s[0]), cmpu);
    r.min = s[0]; r.med = s[REPS/2]; r.p90 = s[(REPS*9)/10]; r.max = s[REPS-1];
    return r;
}

static void print_lat(const char *tag, struct lat l)
{
    printf("  %-34s min %6llu  median %6llu  p90 %6llu  max %7llu\n", tag,
           (unsigned long long)l.min, (unsigned long long)l.med,
           (unsigned long long)l.p90, (unsigned long long)l.max);
}

/* ---------------------------------------------------- CPU pinning ---- */

static void pin_self(int cpu)
{
    cpu_set_t s;
    if (g_ncpu <= 0) return;
    CPU_ZERO(&s); CPU_SET(cpu % g_ncpu, &s);
    pthread_setaffinity_np(pthread_self(), sizeof(s), &s);
}

/* hammers use CPUs 0..3, verifiers 4..5, main thread 6 */
#define CPU_HAMMER(i) (i)
#define CPU_VERIFY(i) (NUM_TARGETS + (i))
#define CPU_MAIN      (NUM_TARGETS + NVERIFY)

/* ------------------------------------------------------- memory ------- */

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
    m[n/(8*sizeof(unsigned long))] |= 1UL << (n % (8*sizeof(unsigned long)));
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

/* ------------------------------------------------------- hammering ---- */

struct hammer {
    volatile uint8_t *a; volatile int *run; int cpu; uint64_t n;
    pthread_t th;
};

static void *hammer_fn(void *arg)
{
    struct hammer *h = arg;
    pin_self(h->cpu);
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

static void start_hammers(struct hammer *h, volatile uint8_t **addrs, int n,
                          volatile int *run)
{
    *run = 1;
    for (int i = 0; i < n; i++) {
        memset(&h[i], 0, sizeof(h[i]));
        h[i].a = addrs[i]; h[i].run = run; h[i].cpu = CPU_HAMMER(i);
        pthread_create(&h[i].th, NULL, hammer_fn, &h[i]);
    }
}

static void stop_hammers(struct hammer *h, int n, volatile int *run)
{
    *run = 0;
    for (int i = 0; i < n; i++) pthread_join(h[i].th, NULL);
}

/* ------------------------------------------------------------ tests --- */

static volatile uint8_t *g_page;
static uint64_t          g_pa;

/* Stage 0: the engine must do nothing when no target is enabled, and
 * exactly what it is told with one target and a short stall. Run this
 * first on any new bitstream. */
static int test_sanity(unsigned cyc, unsigned ms)
{
    struct hammer h[1]; volatile int run;
    volatile uint8_t *a[1] = { g_page };
    uint64_t pa[1] = { g_pa };
    uint64_t s0, s1;
    unsigned short_cyc = cyc < 200 ? cyc : 200;
    int rc = PASS;

    printf("\n=== sanity ===\n");

    /* armed, but no targets enabled */
    program_and_arm(pa, 0, short_cyc);
    start_hammers(h, a, 1, &run);
    usleep(50000);
    stop_hammers(h, 1, &run);
    s0 = status(0); s1 = status(1);
    print_st("no tgt", s0, s1);
    disarm();
    if (check_drained()) return FAIL;
    if (ST_EVT(s0) || ST_EVT(s1) || ST_OCC(s0) || ST_OCC(s1)) {
        printf("  FAIL: reads were diverted with no target enabled.\n");
        return FAIL;
    }

    /* one target, short stall */
    program_and_arm(pa, 1, short_cyc);
    start_hammers(h, a, 1, &run);
    usleep(ms * 1000 < 100000 ? ms * 1000 : 100000);
    stop_hammers(h, 1, &run);
    s0 = status(0); s1 = status(1);
    print_st("1 tgt", s0, s1);
    disarm();
    if (check_drained()) return FAIL;
    printf("  hammer completed %llu loads\n", (unsigned long long)h[0].n);

    if (ST_EVT(s0) == 0) {
        printf("  FAIL: target on channel 0 was never stalled.\n");
        rc = FAIL;
    }
    if (ST_EVT(s1) != 0) {
        printf("  FAIL: channel 1 stalled reads for a channel-0 target.\n");
        rc = FAIL;
    }
    if (ST_MAX(s0) > 1) {
        printf("  FAIL: occupancy %u with one target and one thread.\n", ST_MAX(s0));
        rc = FAIL;
    }
    if (rc == PASS) printf("  PASS: engine is idle when unarmed and stalls only its target.\n");
    return rc;
}

/* Non-matching traffic must not be blocked while ONE line is held.
 * Uses the median, not the minimum: with the old depth-1 engine the
 * minimum always found an unblocked sample and gave a false PASS. */
static int test_passthru(unsigned cyc, unsigned ms)
{
    const uint64_t off_target = 0x000;   /* armed */
    const uint64_t off_victim = 0x080;   /* NOT armed, same channel */
    struct hammer h[1]; volatile int run;
    volatile uint8_t *a[1] = { g_page + off_target };
    uint64_t pa[1] = { g_pa + off_target };
    struct lat idle, tgt, loaded;
    uint64_t s0, s1;
    int rc;
    (void)ms;

    printf("\n=== passthrough: does one held line block other traffic? ===\n");
    printf("  target 0x%llx (armed)   victim 0x%llx (not armed, same channel)\n",
           (unsigned long long)(g_pa + off_target),
           (unsigned long long)(g_pa + off_victim));

    disarm(); usleep(2000);
    idle = measure(g_page + off_victim);
    print_lat("victim, nothing armed", idle);

    program_and_arm(pa, 1, cyc);
    tgt = measure(g_page + off_target);
    print_lat("target, armed (shows stall size)", tgt);

    start_hammers(h, a, 1, &run);
    usleep(20000);
    loaded = measure(g_page + off_victim);
    stop_hammers(h, 1, &run);
    s0 = status(0); s1 = status(1);
    print_lat("victim, target being held", loaded);
    print_st("status", s0, s1);
    disarm();
    if (check_drained()) return FAIL;

    if (tgt.med < idle.med + idle.med / 4) {
        printf("  INCONCLUSIVE: the armed target is not measurably slower, so the\n"
               "  stall is too short to see. Rerun with a larger --cycles.\n");
        return INCONCLUSIVE;
    }
    if (loaded.med < idle.med + idle.med / 2) {
        printf("  PASS: victim median unaffected while a line is held.\n");
        rc = PASS;
    } else {
        printf("  FAIL: victim median %.2fx idle.\n", (double)loaded.med / idle.med);
        if (g_depth < 2)
            printf("        Expected on a depth-%d bitstream: one held line fills\n"
                   "        the queue and backpressures the whole channel.\n", g_depth);
        else if (ST_CONFL(s0))
            printf("        confl=%u: some victim reads shared an ARID with the\n"
                   "        held line and correctly waited behind it. If the IP\n"
                   "        reuses IDs heavily this slowdown is legal.\n", ST_CONFL(s0));
        rc = FAIL;
    }
    if (loaded.p90 > idle.p90 * 2)
        printf("  note: victim p90 %llu vs idle %llu -- some samples waited.\n",
               (unsigned long long)loaded.p90, (unsigned long long)idle.p90);
    return rc;
}

/* Several lines on ONE channel held simultaneously. */
static int test_samechan(unsigned cyc, unsigned ms)
{
    const uint64_t offs[NUM_TARGETS] = { 0x000, 0x080, 0x100, 0x180 }; /* all ch0 */
    int n = g_depth < 2 ? 2 : (g_depth > NUM_TARGETS ? NUM_TARGETS : g_depth);
    struct hammer h[NUM_TARGETS]; volatile int run;
    volatile uint8_t *a[NUM_TARGETS];
    uint64_t pa[NUM_TARGETS], s0, s1;

    printf("\n=== same-channel concurrency: %d targets, all channel 0 ===\n", n);
    for (int t = 0; t < n; t++) {
        a[t] = g_page + offs[t]; pa[t] = g_pa + offs[t];
        printf("  target %d: 0x%llx (bit6=%llu)\n", t, (unsigned long long)pa[t],
               (unsigned long long)((pa[t] >> CHAN_BIT) & 1));
    }
    if (cyc < 1000)
        printf("  note: --cycles %u is short; holds may not overlap. 2000+ is safer.\n", cyc);

    program_and_arm(pa, n, cyc);
    start_hammers(h, a, n, &run);
    usleep(ms * 1000);
    stop_hammers(h, n, &run);
    s0 = status(0); s1 = status(1);
    print_st("status", s0, s1);
    disarm();
    if (check_drained()) return FAIL;

    printf("  max concurrent on channel 0: %u (bitstream depth %d)\n", ST_MAX(s0), g_depth);
    if (ST_EVT(s1) != 0)
        printf("  note: channel 1 saw stalls; check the bit-6 channel mapping.\n");
    if (ST_MAX(s0) >= 2) {
        printf("  PASS: %u lines held simultaneously on one channel.\n", ST_MAX(s0));
        return PASS;
    }
    if (g_depth < 2) {
        printf("  FAIL (expected): this bitstream has depth %d.\n", g_depth);
        return FAIL;
    }
    printf("  INCONCLUSIVE: holds never overlapped. Raise --cycles.\n");
    return INCONCLUSIVE;
}

/* One target per channel at the same time. */
static int test_diffchan(unsigned cyc, unsigned ms)
{
    const uint64_t offs[2] = { 0x000, 0x040 };   /* bit 6 differs */
    struct hammer h[2]; volatile int run;
    volatile uint8_t *a[2] = { g_page + offs[0], g_page + offs[1] };
    uint64_t pa[2] = { g_pa + offs[0], g_pa + offs[1] }, s0, s1;

    printf("\n=== cross-channel: one target per channel ===\n");
    program_and_arm(pa, 2, cyc);
    start_hammers(h, a, 2, &run);
    usleep(ms * 1000);
    stop_hammers(h, 2, &run);
    s0 = status(0); s1 = status(1);
    print_st("status", s0, s1);
    disarm();
    if (check_drained()) return FAIL;

    if (ST_EVT(s0) && ST_EVT(s1) && ST_MAX(s0) == 1 && ST_MAX(s1) == 1) {
        printf("  PASS: each channel stalled its own target, one at a time.\n");
        return PASS;
    }
    printf("  FAIL: expected evt>0 and max=1 on both channels.\n");
    return FAIL;
}

/* ------------------------------------------------------- progress ---- */

/* Progress markers go to stdout and to a local log file that is
 * fsync'd after every line, so after a crash or reset the last line of
 * /var/tmp/test_stall.log says exactly which step was running. */
static int g_logfd = -1;
static int g_quiet;        /* demo: progress markers go to the log file only */

static void mark(const char *fmt, ...)
{
    char b[320], ts[32];
    time_t t = time(NULL);
    struct tm tm;
    va_list ap;
    int n;

    localtime_r(&t, &tm);
    strftime(ts, sizeof(ts), "%H:%M:%S", &tm);
    n = snprintf(b, sizeof(b), "[%s] ", ts);
    va_start(ap, fmt);
    n += vsnprintf(b + n, sizeof(b) - n, fmt, ap);
    va_end(ap);
    if (n >= (int)sizeof(b)) n = sizeof(b) - 1;
    if (!g_quiet) { fputs(b, stdout); fflush(stdout); }
    if (g_logfd >= 0 && write(g_logfd, b, n) == n) fsync(g_logfd);
}

/* ------------------------------------------------------- integrity ---- */

/* How integrity treats stores while stalls are armed:
 *   read        no stores while armed; verify twice (default, safest)
 *   write-safe  rewrite the buffer while armed, EXCEPT the armed lines
 *   write       rewrite everything, including lines whose reads are held
 *
 * Bisection modes (both skip the armed lines, like write-safe):
 *   write-disarmed   disarm, rewrite, re-arm, then verify 2 with stalls
 *                    active: fresh data is read back while stalling, but
 *                    no write ever happens while armed
 *   verify-disarmed  rewrite while armed, then disarm and verify 2: writes
 *                    happen while stalling, the read-back does not
 */
enum { IM_READ, IM_WSAFE, IM_WRITE, IM_WDIS, IM_VDIS };
static int g_imode = IM_READ;
static int g_itargets = NUM_TARGETS;   /* --targets: armed lines in integrity */
static int g_control;                  /* --control: same traffic, engine never armed */
static const char *imode_str[] = { "read", "write-safe", "write",
                                   "write-disarmed", "verify-disarmed" };

struct verifier {
    volatile uint64_t *q; size_t lo, hi, split; uint64_t seed_lo, seed;
    uint64_t bad, first_bad; pthread_t th; int cpu;
};

static inline uint64_t pattern(size_t i, uint64_t seed)
{ return seed ^ ((uint64_t)i * 0x9E3779B97F4A7C15ULL); }

static void *verify_fn(void *arg)
{
    struct verifier *v = arg;
    pin_self(v->cpu);
    for (size_t i = v->lo; i < v->hi; i++) {
        uint64_t got, want = pattern(i, i < v->split ? v->seed_lo : v->seed);
        _mm_clflush((const void *)&v->q[i]);   /* force the read to the device */
        _mm_mfence();
        got = v->q[i];
        if (got != want) {
            if (!v->bad) v->first_bad = i;
            v->bad++;
        }
    }
    return NULL;
}

/* qwords [0, split) are expected to hold seed_lo, the rest seed */
static uint64_t verify_all(volatile uint64_t *q, size_t nq, size_t split,
                           uint64_t seed_lo, uint64_t seed, size_t *first_bad)
{
    struct verifier v[NVERIFY];
    uint64_t bad = 0;
    *first_bad = (size_t)-1;
    for (int k = 0; k < NVERIFY; k++) {
        v[k] = (struct verifier){ .q = q, .lo = nq * k / NVERIFY,
                                  .hi = nq * (k + 1) / NVERIFY, .split = split,
                                  .seed_lo = seed_lo, .seed = seed,
                                  .cpu = CPU_VERIFY(k) };
        pthread_create(&v[k].th, NULL, verify_fn, &v[k]);
    }
    for (int k = 0; k < NVERIFY; k++) {
        pthread_join(v[k].th, NULL);
        if (v[k].bad && v[k].first_bad < *first_bad) *first_bad = v[k].first_bad;
        bad += v[k].bad;
    }
    return bad;
}

/* write qwords [from, nq) and push them to the device */
static void write_range(volatile uint64_t *q, size_t from, size_t nq, uint64_t seed)
{
    for (size_t i = from; i < nq; i++) q[i] = pattern(i, seed);
    for (size_t i = from & ~(size_t)7; i < nq; i += 8) _mm_clflush((const void *)&q[i]);
    _mm_mfence();
}

/* With 4 targets (two per channel) each channel spends time at
 * occupancy 1 (unrelated reads pass the held one -- the reorder case)
 * and at 2 (queue full; further target reads bypass). The pattern is
 * always seeded with stalls DISARMED. */
static int test_integrity(volatile uint8_t *buf, size_t len,
                          unsigned cyc, unsigned passes)
{
    /* ordered so n=2 is one line per channel (never fills a depth-2
     * queue) and n=4 is two per channel (fills both) */
    const uint64_t offs[NUM_TARGETS] = { 0x000, 0x040, 0x080, 0x0C0 };
    const int n = g_itargets;
    /* the armed lines are the first 4 lines of buf: qwords [0, 32) */
    const size_t armed_qwords = 4 * 64 / 8;
    struct hammer h[NUM_TARGETS]; volatile int run;
    volatile uint8_t *a[NUM_TARGETS];
    uint64_t pa[NUM_TARGETS], s0 = 0, s1 = 0;
    volatile uint64_t *q = (volatile uint64_t *)buf;
    size_t nq = len / 8, first_bad;
    uint64_t bad_total = 0, evt0 = 0, evt1 = 0;
    unsigned max0 = 0, max1 = 0;

    printf("\n=== data integrity under concurrent stalls (mode %s) ===\n",
           imode_str[g_imode]);
    printf("  %zu MB, %u passes, %d verifier threads, targets:",
           len >> 20, passes, NVERIFY);
    for (int t = 0; t < n; t++) {
        a[t] = g_page + offs[t]; pa[t] = g_pa + offs[t];
        printf(" 0x%llx(ch%llu)", (unsigned long long)pa[t],
               (unsigned long long)((pa[t] >> CHAN_BIT) & 1));
    }
    printf("\n");
    if (g_imode == IM_WRITE)
        printf("  WARNING: mode 'write' stores to lines whose reads are held.\n");
    if (g_control)
        printf("  CONTROL RUN: identical traffic, stall engine left DISARMED.\n");

    for (unsigned p = 0; p < passes; p++) {
        uint64_t seedA = 0xA5A5000000000000ULL ^ ((uint64_t)p << 32);
        uint64_t seedB = 0x5A5A000000000000ULL ^ ((uint64_t)p << 32);
        uint64_t bad1, bad2;

        disarm(); usleep(2000);
        mark("integrity pass %u: seeding (disarmed)\n", p);
        write_range(q, 0, nq, seedA);

        if (g_control) {
            mark("integrity pass %u: CONTROL, engine disarmed, starting hammers\n", p);
        } else {
            mark("integrity pass %u: arming %d targets, %u cycles, starting hammers\n",
                 p, n, cyc);
            program_and_arm(pa, n, cyc);
        }
        start_hammers(h, a, n, &run);
        usleep(20000);

        mark("integrity pass %u: verify 1 (read-only)\n", p);
        bad1 = verify_all(q, nq, 0, seedA, seedA, &first_bad);
        if (bad1) printf("  verify 1: %llu bad, first at qword %zu\n",
                         (unsigned long long)bad1, first_bad);

        if (g_imode == IM_READ) {
            mark("integrity pass %u: verify 2 (read-only)\n", p);
            bad2 = verify_all(q, nq, 0, seedA, seedA, &first_bad);
        } else {
            size_t from = (g_imode == IM_WRITE) ? 0 : armed_qwords;
            if (g_imode == IM_WDIS) {
                mark("integrity pass %u: disarming before rewrite\n", p);
                disarm();
                if (check_drained()) { stop_hammers(h, n, &run); return FAIL; }
            }
            mark("integrity pass %u: rewriting qwords [%zu, %zu) %s\n", p, from, nq,
                 g_imode == IM_WDIS ? "while DISARMED" : "while armed");
            write_range(q, from, nq, seedB);
            if (g_imode == IM_WDIS && !g_control) {
                mark("integrity pass %u: re-arming\n", p);
                program_and_arm(pa, n, cyc);
            }
            if (g_imode == IM_VDIS) {
                mark("integrity pass %u: disarming before verify\n", p);
                disarm();
                if (check_drained()) { stop_hammers(h, n, &run); return FAIL; }
            }
            mark("integrity pass %u: verify 2 (after rewrite, engine %s)\n", p,
                 (g_imode == IM_VDIS || g_control) ? "disarmed" : "armed");
            bad2 = verify_all(q, nq, from, seedA, seedB, &first_bad);
        }
        if (bad2) printf("  verify 2: %llu bad, first at qword %zu\n",
                         (unsigned long long)bad2, first_bad);

        stop_hammers(h, n, &run);
        s0 = status(0); s1 = status(1);
        disarm();
        if (check_drained()) return FAIL;
        mark("integrity pass %u: done, disarmed and drained\n", p);

        evt0 += ST_EVT(s0); evt1 += ST_EVT(s1);
        if (ST_MAX(s0) > max0) max0 = ST_MAX(s0);
        if (ST_MAX(s1) > max1) max1 = ST_MAX(s1);
        bad_total += bad1 + bad2;
        print_st("status", s0, s1);
    }

    if (bad_total) {
        printf("  FAIL: %llu mismatched qwords. Reads are returning wrong data\n"
               "        under stalls. Do not use this bitstream.\n",
               (unsigned long long)bad_total);
        return FAIL;
    }
    if (!g_control && (evt0 == 0 || (n >= 2 && evt1 == 0))) {
        printf("  INCONCLUSIVE: no data errors, but a channel never stalled "
               "(evt ch0=%llu ch1=%llu).\n",
               (unsigned long long)evt0, (unsigned long long)evt1);
        return INCONCLUSIVE;
    }
    printf("  PASS: %zu qwords x 2 verifies x %u passes, no corruption.\n",
           nq, passes);
    printf("        max held ch0=%u ch1=%u%s\n", max0, max1,
           (max0 >= 2 && max1 >= 2) ? " (two lines held per channel)" : "");
    return PASS;
}

/* ------------------------------------------------------------- demo ---- */

/* A narrated walk-through for showing the engine to people: one screen,
 * times in ns/us instead of TSC ticks, each claim measured directly and
 * marked ok/FAIL, and a summary table at the end. */

static double g_tsc_per_ns;

static void calibrate_tsc(void)
{
    struct timespec a, b;
    uint64_t t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &a); t0 = __rdtsc();
    usleep(50000);
    clock_gettime(CLOCK_MONOTONIC, &b); t1 = __rdtsc();
    g_tsc_per_ns = (double)(t1 - t0) /
                   ((b.tv_sec - a.tv_sec) * 1e9 + (b.tv_nsec - a.tv_nsec));
}

static const char *fmt_t(uint64_t ticks, char *buf, size_t n)
{
    double ns = ticks / g_tsc_per_ns;
    if (ns < 1000) snprintf(buf, n, "%4.0f ns", ns);
    else           snprintf(buf, n, "%4.1f us", ns / 1000);
    return buf;
}

/* Median load latency of p, counting only samples where the channel's
 * occupancy, read just before the load, was at least min_occ. With
 * min_occ = 2 this measures a bystander while BOTH slots are held. */
static uint64_t median_when(volatile uint8_t *p, int ch, unsigned min_occ, int *got)
{
    static uint64_t s[REPS];
    int k = 0;
    for (int tries = 0; tries < 200000 && k < 101; tries++) {
        uint64_t a, b, v;
        _mm_clflush((const void *)p); _mm_mfence();
        if (min_occ && ST_OCC(status(ch)) < min_occ) continue;
        a = tb(); v = *(volatile uint64_t *)p; b = te();
        __asm__ __volatile__("" :: "r"(v));
        s[k++] = b - a;
    }
    *got = k;
    if (!k) return 0;
    qsort(s, k, sizeof(s[0]), cmpu);
    return s[k / 2];
}

/* Fraction of time each channel holds 0, 1, 2 lines, by polling the
 * live occupancy while traffic runs. */
static void occ_hist(unsigned ms, double h0[3], double h1[3])
{
    unsigned long c0[3] = {0}, c1[3] = {0}, n = 0;
    uint64_t end = __rdtsc() + (uint64_t)(ms * 1e6 * g_tsc_per_ns);
    while (__rdtsc() < end) {
        unsigned o0 = ST_OCC(status(0)), o1 = ST_OCC(status(1));
        c0[o0 > 2 ? 2 : o0]++; c1[o1 > 2 ? 2 : o1]++; n++;
    }
    for (int i = 0; i < 3; i++) {
        h0[i] = n ? 100.0 * c0[i] / n : 0;
        h1[i] = n ? 100.0 * c1[i] / n : 0;
    }
}

static int demo_ok(int cond, int *fails)
{
    if (!cond) (*fails)++;
    return cond;
}
#define OKS(c) ((c) ? " ok " : "FAIL")

static int test_demo(unsigned cyc)
{
    /* A, B, C on channel 0; D, E on channel 1. C is never armed. */
    volatile uint8_t *A = g_page + 0x000, *B = g_page + 0x080,
                     *C = g_page + 0x100, *D = g_page + 0x040,
                     *E = g_page + 0x0C0;
    uint64_t pA = g_pa + 0x000, pB = g_pa + 0x080,
             pD = g_pa + 0x040, pE = g_pa + 0x0C0;
    struct hammer h[NUM_TARGETS]; volatile int run;
    char t1[32], t2[32];
    int fails = 0, got;
    uint64_t base_A, base_C, st_A, byst1, byst2, after_A;
    double h0[3], h1[3], full_ch0, full2_ch0, full2_ch1;
    uint64_t bad;
    size_t first_bad;
    volatile uint64_t *q = (volatile uint64_t *)g_page;
    size_t nq = INTEGRITY_BYTES / 8;
    int ok_stall, ok_b1, ok_two, ok_b2, ok_both, ok_data, ok_after;

    calibrate_tsc();
    printf("\n================ CXL read-stall engine demo ================\n");
    printf("  %d slots per channel, stall length %u cycles\n", g_depth, cyc);
    printf("  lines A, B, C on channel 0 (C is never stalled)\n");
    printf("  lines D, E    on channel 1\n");

    /* 1 */
    disarm(); usleep(2000);
    base_A = measure(A).med;
    base_C = measure(C).med;
    printf("\n[1] Baseline, nothing armed\n");
    printf("      read A: %s    read C: %s\n",
           fmt_t(base_A, t1, sizeof t1), fmt_t(base_C, t2, sizeof t2));

    /* 2 */
    {
        uint64_t pa[1] = { pA };
        volatile uint8_t *a[1] = { A };
        program_and_arm(pa, 1, cyc);
        st_A = measure(A).med;
        start_hammers(h, a, 1, &run);
        usleep(20000);
        byst1 = median_when(C, 0, 1, &got);
        stop_hammers(h, 1, &run);
        disarm();
        if (check_drained()) return FAIL;
    }
    ok_stall = demo_ok(st_A > 2 * base_A, &fails);
    ok_b1    = demo_ok(got >= 20 && byst1 < base_C + base_C / 2, &fails);
    printf("\n[2] Stall one line (A)\n");
    printf("      read A: %s -> %s                       [%s]\n",
           fmt_t(base_A, t1, sizeof t1), fmt_t(st_A, t2, sizeof t2), OKS(ok_stall));
    printf("      read C while A is held: %s -> %s     [%s]\n",
           fmt_t(base_C, t1, sizeof t1), fmt_t(byst1, t2, sizeof t2), OKS(ok_b1));

    /* 3 */
    {
        uint64_t pa[2] = { pA, pB };
        volatile uint8_t *a[2] = { A, B };
        program_and_arm(pa, 2, cyc);
        start_hammers(h, a, 2, &run);
        usleep(20000);
        occ_hist(200, h0, h1);
        byst2 = median_when(C, 0, 2, &got);
        stop_hammers(h, 2, &run);
        disarm();
        if (check_drained()) return FAIL;
    }
    full_ch0 = h0[2];
    ok_two = demo_ok(full_ch0 > 0, &fails);
    ok_b2  = demo_ok(got >= 20 && byst2 < base_C + base_C / 2, &fails);
    printf("\n[3] Stall two lines on the same channel (A and B)\n");
    printf("      channel 0 holding 0 / 1 / 2 lines: %3.0f%% / %3.0f%% / %3.0f%% of the time  [%s]\n",
           h0[0], h0[1], h0[2], OKS(ok_two));
    printf("      read C while BOTH are held: %s -> %s [%s]\n",
           fmt_t(base_C, t1, sizeof t1), fmt_t(byst2, t2, sizeof t2), OKS(ok_b2));
    if (got < 20)
        printf("      (only %d samples caught both slots held; raise --cycles)\n", got);

    /* 4 */
    {
        uint64_t pa[4] = { pA, pB, pD, pE };
        volatile uint8_t *a[4] = { A, B, D, E };
        write_range(q, 0, nq, 0xC0FFEE0000000000ULL);   /* seeded while disarmed */
        program_and_arm(pa, 4, cyc);
        start_hammers(h, a, 4, &run);
        usleep(20000);
        occ_hist(200, h0, h1);
        bad = verify_all(q, nq, 0, 0, 0xC0FFEE0000000000ULL, &first_bad);
        stop_hammers(h, 4, &run);
        disarm();
        if (check_drained()) return FAIL;
    }
    full2_ch0 = h0[2]; full2_ch1 = h1[2];
    ok_both = demo_ok(full2_ch0 > 0 && full2_ch1 > 0, &fails);
    ok_data = demo_ok(bad == 0, &fails);
    printf("\n[4] Two lines stalled on EACH channel (A, B and D, E)\n");
    printf("      both slots held: channel 0 %3.0f%%, channel 1 %3.0f%% of the time  [%s]\n",
           full2_ch0, full2_ch1, OKS(ok_both));
    printf("      read back %zu MB under stalls: %llu wrong values                [%s]\n",
           INTEGRITY_BYTES >> 20, (unsigned long long)bad, OKS(ok_data));

    /* 5 */
    usleep(2000);
    after_A = measure(A).med;
    ok_after = demo_ok(after_A < base_A + base_A / 2, &fails);
    printf("\n[5] Disarm\n");
    printf("      nothing left held; read A back to %s                  [%s]\n",
           fmt_t(after_A, t1, sizeof t1), OKS(ok_after));

    printf("\n------------------------------------------------------------\n");
    printf("  %-44s %s\n", "stalls a chosen line",                    OKS(ok_stall));
    printf("  %-44s %s\n", "other reads flow while one line is held",  OKS(ok_b1));
    printf("  %-44s %s\n", "holds two lines on one channel at once",   OKS(ok_two));
    printf("  %-44s %s\n", "other reads flow while two are held",      OKS(ok_b2));
    printf("  %-44s %s\n", "two per channel on both channels at once", OKS(ok_both));
    printf("  %-44s %s\n", "no data corruption",                      OKS(ok_data));
    printf("  %-44s %s\n", "fully released on disarm",                 OKS(ok_after));
    printf("------------------------------------------------------------\n");
    printf("  %s\n", fails ? "DEMO: some checks FAILED" : "DEMO: all checks passed");
    return fails ? FAIL : PASS;
}
#undef OKS

/* ------------------------------------------------------------ ARID ---- */

static int test_arid(unsigned cyc)
{
    struct hammer h[1]; volatile int run;
    volatile uint8_t *a[1] = { g_page };
    uint64_t pa[1] = { g_pa }, s0, s1;

    printf("\n=== ARID survey ===\n");
    program_and_arm(pa, 1, cyc);
    start_hammers(h, a, 1, &run);
    usleep(100000);
    stop_hammers(h, 1, &run);
    s0 = status(0); s1 = status(1);
    disarm();
    if (check_drained()) return FAIL;
    printf("  ARID sticky OR: ch0 = 0x%02x, ch1 = 0x%02x\n", ST_ARID(s0), ST_ARID(s1));
    if (ST_ARID(s0) == 0 && ST_ARID(s1) == 0)
        printf("  Every request carries ARID 0. The engine stays correct (same-ID\n"
               "  requests wait behind a held line), but then any held line\n"
               "  blocks its whole channel.\n");
    else
        printf("  Multiple IDs in use; requests with other IDs can pass a held line.\n");
    return PASS;
}

/* --------------------------------------------------------------- main -- */

static int want(const char *test, const char *name)
{ return !strcmp(test, name) || !strcmp(test, "all"); }

int main(int argc, char **argv)
{
    const char *bdf = "0000:40:00.1", *test = "all";
    uint64_t base = 0x8080000000ULL, size = 0x400000000ULL;
    unsigned cyc = 2000, ms = 300, passes = 3;
    int do_disarm = 0, node, i, rc = 0, all;
    char path[512];
    void *buf;
    size_t buflen = (size_t)BUF_PAGES * PAGE_SZ;
    int fd;

    for (i = 1; i < argc; i++) {
        if (!strcmp(argv[i],"--bdf") && i+1<argc) bdf = argv[++i];
        else if (!strcmp(argv[i],"--base") && i+1<argc) base = strtoull(argv[++i],NULL,16);
        else if (!strcmp(argv[i],"--size") && i+1<argc) size = strtoull(argv[++i],NULL,16);
        else if (!strcmp(argv[i],"--cycles") && i+1<argc) cyc = (unsigned)strtoul(argv[++i],NULL,0);
        else if (!strcmp(argv[i],"--ms") && i+1<argc) ms = (unsigned)strtoul(argv[++i],NULL,0);
        else if (!strcmp(argv[i],"--passes") && i+1<argc) passes = (unsigned)strtoul(argv[++i],NULL,0);
        else if (!strcmp(argv[i],"--test") && i+1<argc) test = argv[++i];
        else if (!strcmp(argv[i],"--imode") && i+1<argc) {
            const char *m = argv[++i];
            if      (!strcmp(m, "read"))       g_imode = IM_READ;
            else if (!strcmp(m, "write-safe")) g_imode = IM_WSAFE;
            else if (!strcmp(m, "write"))      g_imode = IM_WRITE;
            else if (!strcmp(m, "write-disarmed"))  g_imode = IM_WDIS;
            else if (!strcmp(m, "verify-disarmed")) g_imode = IM_VDIS;
            else { fprintf(stderr,"--imode must be read|write-safe|write|"
                                  "write-disarmed|verify-disarmed\n"); return 1; }
        }
        else if (!strcmp(argv[i],"--targets") && i+1<argc) {
            g_itargets = atoi(argv[++i]);
            if (g_itargets < 1 || g_itargets > NUM_TARGETS) {
                fprintf(stderr,"--targets must be 1..%d\n", NUM_TARGETS); return 1;
            }
        }
        else if (!strcmp(argv[i],"--control")) g_control = 1;
        else if (!strcmp(argv[i],"--disarm")) do_disarm = 1;
        else { fprintf(stderr,"unknown option: %s\n", argv[i]); return 1; }
    }
    if (cyc > 65535) { fprintf(stderr,"cycles must be <= 65535\n"); return 1; }
    if (ms == 0 || ms > 10000) { fprintf(stderr,"--ms must be 1..10000\n"); return 1; }
    if (passes == 0 || passes > 100) { fprintf(stderr,"--passes must be 1..100\n"); return 1; }
    if (cyc > HW_TIMEOUT)
        printf("note: --cycles %u exceeds the hardware timeout; holds will be "
               "capped at %d cycles.\n", cyc, HW_TIMEOUT);

    snprintf(path, sizeof(path), "/sys/bus/pci/devices/%s/resource2", bdf);
    fd = open(path, O_RDWR | O_SYNC);
    if (fd < 0) { perror("open BAR2"); return 1; }
    g_csr = mmap(NULL, CSR_MAP, PROT_READ|PROT_WRITE, MAP_SHARED, fd, 0);
    close(fd);
    if (g_csr == MAP_FAILED) { g_csr = NULL; perror("mmap"); return 1; }
    signal(SIGINT,on_sig); signal(SIGTERM,on_sig); atexit(disarm);

    if (do_disarm) { disarm(); printf("disarmed.\n"); return 0; }
    if (geteuid() != 0) { fprintf(stderr,"must run as root (pagemap)\n"); return 1; }

    g_quiet = !strcmp(test, "demo");
    g_logfd = open("/var/tmp/test_stall.log", O_WRONLY | O_CREAT | O_APPEND, 0644);
    if (g_logfd < 0) perror("open /var/tmp/test_stall.log (continuing)");
    mark("---- start: test=%s cycles=%u ms=%u passes=%u imode=%s targets=%d%s\n",
         test, cyc, ms, passes, imode_str[g_imode], g_itargets,
         g_control ? " CONTROL" : "");

    /* the target array must respond, or this is the wrong bitstream */
    {
        uint64_t rb;
        disarm();
        *(volatile uint64_t *)(g_csr + CSR_ADDR_AR + 8*3) = 0xABCD000012345678ULL;
        _mm_sfence(); usleep(100);
        rb = *(volatile uint64_t *)(g_csr + CSR_ADDR_AR + 8*3);
        *(volatile uint64_t *)(g_csr + CSR_ADDR_AR + 8*3) = 0;
        _mm_sfence();
        if (rb != 0xABCD000012345678ULL) {
            fprintf(stderr,
              "target array at 0x1100 did not read back (got 0x%llx).\n"
              "This bitstream does not have the queue engine.\n",
              (unsigned long long)rb);
            return 1;
        }
    }
    g_depth = (int)ST_DEPTH(status(0));
    if (g_depth == 0) {
        printf("CSR alive on %s BAR2; depth field reads 0 -- older bitstream,\n"
               "assuming depth 1. Same-channel concurrency is not available.\n", bdf);
        g_depth = 1;
    } else
        printf("CSR alive on %s BAR2; engine depth %d per channel\n", bdf, g_depth);
    if (check_drained()) return 1;

    g_ncpu = (int)sysconf(_SC_NPROCESSORS_ONLN);
    pin_self(CPU_MAIN);

    node = find_node(base, size);
    if (node < 0) { fprintf(stderr,"no NUMA node backs the CXL window\n"); return 1; }
    printf("CXL memory is NUMA node %d\n", node);

    buf = mmap(NULL, buflen, PROT_READ|PROT_WRITE,
               MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
    if (buf == MAP_FAILED) { perror("mmap"); return 1; }
    if (mbindn(buf, buflen, node) != 0) { perror("mbind"); return 1; }
    memset(buf, 0xA5, buflen);
    if (mlock(buf, buflen) != 0) perror("mlock (continuing)");

    /* test page: first CXL-backed page of buf; page-aligned, so
     * offset 0x000 is channel 0 */
    for (i = 0; i < BUF_PAGES; i++) {
        void *p = (uint8_t*)buf + (size_t)i*PAGE_SZ;
        uint64_t q = v2p(p);
        if (q >= base && q < base + size) {
            g_page = (volatile uint8_t *)p;
            g_pa   = q;
            break;
        }
    }
    if (!g_page) { fprintf(stderr,"no suitable CXL page\n"); return 1; }
    if ((size_t)((uint8_t *)g_page - (uint8_t *)buf) + INTEGRITY_BYTES > buflen) {
        fprintf(stderr,"test page too close to the end of the buffer\n");
        return 1;
    }
    printf("test page pa 0x%llx, %u stall cycles\n",
           (unsigned long long)g_pa, cyc);

    all = !strcmp(test, "all");
    {
        struct { const char *name; int r; } res[7];
        int nres = 0, r;
#define RUN(nm, call) \
        if (want(test, nm)) { \
            mark("test %s: start\n", nm); \
            r = (call); \
            mark("test %s: %s\n", nm, verdict_str[r]); res[nres].name = nm; res[nres++].r = r; \
            if (r == FAIL) rc = 1; \
            if (all && r == FAIL) { printf("\nstopping: %s failed.\n", nm); goto summary; } \
        }
        RUN("arid",      test_arid(cyc));
        RUN("sanity",    test_sanity(cyc, ms));
        RUN("passthru",  test_passthru(cyc, ms));
        RUN("samechan",  test_samechan(cyc, ms));
        RUN("diffchan",  test_diffchan(cyc, ms));
        RUN("integrity", test_integrity(g_page, INTEGRITY_BYTES, cyc, passes));
        if (!strcmp(test, "demo")) {
            mark("test demo: start\n");
            r = test_demo(cyc);
            mark("test demo: %s\n", verdict_str[r]);
            res[nres].name = "demo"; res[nres++].r = r;
            if (r == FAIL) rc = 1;
        }
#undef RUN
summary:
        if (nres == 0) { fprintf(stderr, "unknown test: %s\n", test); rc = 1; }
        if (nres > 1) {
            printf("\nsummary:\n");
            for (i = 0; i < nres; i++)
                printf("  %-10s %s\n", res[i].name, verdict_str[res[i].r]);
        }
    }

    disarm();
    mark("---- end, rc=%d\n", rc);
    printf("\ndone.\n");
    return rc;
}