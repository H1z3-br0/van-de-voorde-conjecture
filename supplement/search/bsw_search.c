#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int p, k, q;
static int modpoly[16];
static int *lg, *ex;
static int8_t *chi;
static int8_t *chi_ext;
static int8_t *chid;
static int primefield;

static inline int CHID(int x, int y) {
    return primefield ? chi_ext[x - y + q] : chid[(size_t)x * q + y];
}

static int fsub(int x, int y) {
    int r = 0, m = 1;
    for (int i = 0; i < k; i++) {
        int a = x % p, b = y % p;
        x /= p; y /= p;
        r += ((a - b + p) % p) * m;
        m *= p;
    }
    return r;
}

static int fmul_slow(int x, int y) {
    if (k == 1) return (int)((long)x * y % p);
    int a[16], b[16], c[32];
    for (int i = 0; i < k; i++) { a[i] = x % p; x /= p; b[i] = y % p; y /= p; }
    memset(c, 0, sizeof c);
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++) c[i + j] = (c[i + j] + a[i] * b[j]) % p;
    for (int d = 2 * k - 2; d >= k; d--) {
        int co = c[d];
        if (!co) continue;
        c[d] = 0;
        for (int i = 0; i < k; i++) c[d - k + i] = ((c[d - k + i] - co * modpoly[i]) % p + p) % p;
    }
    int r = 0, m = 1;
    for (int i = 0; i < k; i++) { r += c[i] * m; m *= p; }
    return r;
}

static inline int fmul(int x, int y) {
    if (!x || !y) return 0;
    int e = lg[x] + lg[y];
    if (e >= q - 1) e -= q - 1;
    return ex[e];
}

static int *psi;
static int cur_n;
static long long nsol = 0, nsol_nonell = 0, nforced = 0, nforced_fail = 0;
static long long *nodes_at_depth;
static int verbose = 0, noshort = 0, fullcheck = 0;
static int maxdepth_branch = 0;

static int **PT_, **CL_, **CS_, **MI_, **MAP_;
static void ensure_depth(int d);

static int check_full(void) {
    for (int x = 1; x < q; x++) {
        int y = psi[x];
        if (y < 1 || y >= q || y == x || psi[y] != x) return 0;
        if (chi[x] != -chi[y]) return 0;
    }
    for (int x = 1; x < q; x++) {
        int px = psi[x];
        for (int y = 1; y < q; y++) {
            if (y == x || y == px) continue;
            int py = psi[y];
            if (CHID(x, y) * CHID(x, py) * CHID(px, y) * CHID(px, py) != -1) return 0;
        }
    }
    return 1;
}

static int is_elliptic(void) {
    for (int x = 1; x < q; x++) if (fmul(x, psi[x]) != cur_n) return 0;
    return 1;
}

static void finish(void) {
    if (is_elliptic()) {

        if (fullcheck && !check_full()) { fprintf(stderr, "INTERNAL ERROR: n/x fails check\n"); exit(2); }
        nsol++;
        if (verbose) printf("elliptic psi = %d/x\n", cur_n);
        return;
    }
    if (!check_full()) { nforced_fail++; return; }
    nsol++; nsol_nonell++;
    printf("NON-ELLIPTIC psi:");
    for (int x = 1; x < q; x++) if (x < psi[x]) printf(" {%d,%d}", x, psi[x]);
    printf("\n");
    fflush(stdout);
}

static void rec(int d, int npt, int ncls) {
    nodes_at_depth[d]++;
    int *pt = PT_[d], *cl = CL_[d], *cs = CS_[d], *mi = MI_[d];
    if (npt == 0) { finish(); return; }
    int best = -1, maxsz = 0;
    for (int c = 0; c < ncls; c++) {
        if (cs[c] > maxsz) maxsz = cs[c];
        if (cs[c] > 0 && (best < 0 || cs[c] < cs[best])) best = c;
    }
    if (maxsz == 1 && !noshort) {

        int *rep = MAP_[d];
        for (int i = 0; i < npt; i++) rep[cl[i]] = pt[i];
        for (int i = 0; i < npt; i++) psi[pt[i]] = rep[mi[cl[i]]];
        nforced++;
        finish();
        for (int i = 0; i < npt; i++) psi[pt[i]] = 0;
        return;
    }
    if (d > maxdepth_branch) maxdepth_branch = d;
    int u = -1;
    for (int i = 0; i < npt; i++) if (cl[i] == best) { u = pt[i]; break; }
    int m = mi[best];
    ensure_depth(d + 1);
    int *npt_ = PT_[d + 1], *ncl = CL_[d + 1], *ncs = CS_[d + 1], *nmi = MI_[d + 1], *map = MAP_[d];
    for (int j = 0; j < npt; j++) {
        if (cl[j] != m) continue;
        int v = pt[j];
        for (int c = 0; c < 2 * ncls; c++) map[c] = -1;
        int nn = 0, nc = 0;
        for (int i = 0; i < npt; i++) {
            int w = pt[i];
            if (w == u || w == v) continue;
            int bit = (CHID(w, u) * CHID(w, v) == 1) ? 0 : 1;
            int key = 2 * cl[i] + bit;
            if (map[key] < 0) { map[key] = nc; ncs[nc] = 0; nc++; }
            npt_[nn] = w; ncl[nn] = map[key]; ncs[map[key]]++; nn++;
        }
        int ok = 1;
        for (int key = 0; key < 2 * ncls && ok; key++) {
            if (map[key] < 0) continue;
            int mkey = 2 * mi[key >> 1] + (1 - (key & 1));
            if (map[mkey] < 0 || ncs[map[mkey]] != ncs[map[key]]) ok = 0;
            else nmi[map[key]] = map[mkey];
        }
        if (!ok) continue;
        psi[u] = v; psi[v] = u;
        rec(d + 1, nn, nc);
        psi[u] = psi[v] = 0;
    }
}

static void ensure_depth(int d) {
    if (PT_[d]) return;
    PT_[d] = malloc(sizeof(int) * q); CL_[d] = malloc(sizeof(int) * q);
    CS_[d] = malloc(sizeof(int) * q); MI_[d] = malloc(sizeof(int) * q);
    MAP_[d] = malloc(sizeof(int) * 2 * q);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s p k [c0..c_{k-1}] [-w i W] [-v] [-noshort] [-fullcheck]\n", argv[0]); return 1; }
    p = atoi(argv[1]); k = atoi(argv[2]);
    int ai = 3;
    if (k > 1) for (int i = 0; i < k; i++) modpoly[i] = atoi(argv[ai++]);
    int worker = 0, nworkers = 1;
    for (; ai < argc; ai++) {
        if (!strcmp(argv[ai], "-w")) { worker = atoi(argv[ai + 1]); nworkers = atoi(argv[ai + 2]); ai += 2; }
        else if (!strcmp(argv[ai], "-v")) verbose = 1;
        else if (!strcmp(argv[ai], "-noshort")) noshort = 1;
        else if (!strcmp(argv[ai], "-fullcheck")) fullcheck = 1;
    }
    q = 1; for (int i = 0; i < k; i++) q *= p;
    primefield = (k == 1);

    lg = malloc(sizeof(int) * q); ex = malloc(sizeof(int) * q);
    int gen = -1;
    for (int g = 2; g < q + 1 && gen < 0; g++) {
        int gg = (g == q) ? 1 : g;
        for (int i = 0; i < q; i++) lg[i] = -1;
        int x = 1, e = 0, ok = 1;
        while (e < q - 1) {
            if (lg[x] >= 0) { ok = 0; break; }
            lg[x] = e; ex[e] = x; x = fmul_slow(x, gg); e++;
        }
        if (ok && x == 1) gen = gg;
    }
    if (gen < 0) { fprintf(stderr, "modulus is not irreducible / not a field\n"); return 1; }
    lg[0] = -1;

    chi = calloc(q, 1);
    for (int x = 1; x < q; x++) chi[x] = (lg[x] % 2 == 0) ? 1 : -1;
    if (primefield) {
        chi_ext = malloc(2 * q);
        for (int d = -q + 1; d < q; d++) chi_ext[d + q] = chi[((d % q) + q) % q];
    } else {
        chid = malloc((size_t)q * q);
        for (int x = 0; x < q; x++)
            for (int y = 0; y < q; y++) chid[(size_t)x * q + y] = chi[fsub(x, y)];
    }

    {
        int ns = 0;
        for (int x = 1; x < q; x++) ns += (chi[x] == 1);
        if (ns != (q - 1) / 2) { fprintf(stderr, "chi sanity failed\n"); return 1; }
        for (int t = 0; t < 1000; t++) {
            int x = 1 + rand() % (q - 1), y = 1 + rand() % (q - 1);
            if (chi[fmul(x, y)] != chi[x] * chi[y] || fmul(x, y) != fmul_slow(x, y)) { fprintf(stderr, "field sanity failed\n"); return 1; }
            int s = primefield ? ((x - y) % q + q) % q : fsub(x, y);
            if (CHID(x, y) != (s ? chi[s] : 0)) { fprintf(stderr, "chid sanity failed\n"); return 1; }
        }
    }

    psi = calloc(q, sizeof(int));
    int D = q / 2 + 3;
    nodes_at_depth = calloc(D + 1, sizeof(long long));
    PT_ = calloc(D + 1, sizeof(int *)); CL_ = calloc(D + 1, sizeof(int *));
    CS_ = calloc(D + 1, sizeof(int *)); MI_ = calloc(D + 1, sizeof(int *));
    MAP_ = calloc(D + 1, sizeof(int *));
    ensure_depth(0); ensure_depth(1);
    clock_t t0 = clock();

    int idx = 0, nroots = 0;
    for (int n = 1; n < q; n++) {
        if (chi[n] != -1) continue;
        if ((idx++) % nworkers != worker) continue;
        nroots++;
        cur_n = n;
        int npt = 0, nc = 0, map[4] = {-1, -1, -1, -1};
        int *pt = PT_[1], *cl = CL_[1], *cs = CS_[1], *mi = MI_[1];
        for (int w = 2; w < q; w++) {
            if (w == n) continue;
            int key = 2 * (chi[w] == 1 ? 0 : 1) + ((CHID(w, 1) * CHID(w, n) == 1) ? 0 : 1);
            if (map[key] < 0) { map[key] = nc; cs[nc] = 0; nc++; }
            pt[npt] = w; cl[npt] = map[key]; cs[map[key]]++; npt++;
        }
        int ok = 1;
        for (int key = 0; key < 4; key++) {
            if (map[key] < 0) continue;
            int mkey = 3 - key;
            if (map[mkey] < 0 || cs[map[mkey]] != cs[map[key]]) ok = 0;
            else mi[map[key]] = map[mkey];
        }
        nodes_at_depth[0]++;
        if (!ok) continue;
        psi[1] = n; psi[n] = 1;
        rec(1, npt, nc);
        psi[1] = psi[n] = 0;
    }
    double secs = (double)(clock() - t0) / CLOCKS_PER_SEC;
    long long tot = 0;
    for (int d = 0; d <= D; d++) tot += nodes_at_depth[d];
    printf("q=%d p=%d k=%d worker=%d/%d roots=%d solutions=%lld elliptic=%lld non_elliptic=%lld "
           "nodes=%lld forced_leaves=%lld forced_rejected=%lld max_branch_depth=%d time=%.2fs\n",
           q, p, k, worker, nworkers, nroots, nsol, nsol - nsol_nonell, nsol_nonell, tot, nforced,
           nforced_fail, maxdepth_branch, secs);
    printf("nodes per depth:");
    for (int d = 0; d <= D; d++) if (nodes_at_depth[d]) printf(" %d:%lld", d, nodes_at_depth[d]);
    printf("\n");
    return 0;
}
