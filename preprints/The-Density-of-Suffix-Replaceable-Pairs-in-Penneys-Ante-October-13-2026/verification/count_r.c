/*
 * Counts |R_n|, the ordered pairs (v,w) of binary words of length n with
 * property R, for n = 1, ..., N (default N = 15), and prints Table 1 of
 * "The density of suffix-replaceable pairs in Penney's ante".
 *
 * Author: Knowledge Sense
 *
 * Method: diagonal pairs (v,v) have property R (Remark 2.3). For v != w,
 * the program tests condition (2.3) of Proposition 2.2: every element of
 * B_v has a suffix in B_w and vice versa, where
 *   B_v = D(v,v) u D(w,v),  B_w = D(v,w) u D(w,w),
 *   D(s,t) = { pre_{n-k}(s) : 1 <= k <= n-1, suf_k(s) = pre_k(t) }.
 * Words are stored as integers with letter a_i in bit i-1, so that
 * pre_j(a) = a & mask(j) and suf_k(a) = a >> (n-k).
 */
#include <stdio.h>
#include <stdlib.h>

typedef unsigned long long u64;

static int n;

static u64 mask(int j) { return (1ULL << j) - 1; }

/* The generator pre_{n-k}(A) is stored as the pair (A, k). */
typedef struct { u64 word; int k; } gen;

/* Is pre_{n-l}(b) a suffix of pre_{n-k}(a)?  Requires l >= k. */
static int is_suffix(gen y, gen x)
{
    if (y.k < x.k) return 0;
    return (y.word & mask(n - y.k)) == ((x.word >> (y.k - x.k)) & mask(n - y.k));
}

/* Does every element of X have a suffix in Y? */
static int dominated(const gen *X, int nx, const gen *Y, int ny)
{
    for (int i = 0; i < nx; i++) {
        int found = 0;
        for (int j = 0; j < ny && !found; j++)
            found = is_suffix(Y[j], X[i]);
        if (!found) return 0;
    }
    return 1;
}

static int has_property_R(u64 v, u64 w)
{
    if (v == w) return 1;
    gen Bv[64], Bw[64];
    int nv = 0, nw = 0;
    u64 words[2] = { v, w };
    for (int c = 0; c < 2; c++)
        for (int k = 1; k < n; k++) {
            u64 s = words[c] >> (n - k);              /* suf_k */
            if (s == (v & mask(k))) Bv[nv++] = (gen){ words[c], k };
            if (s == (w & mask(k))) Bw[nw++] = (gen){ words[c], k };
        }
    return dominated(Bv, nv, Bw, nw) && dominated(Bw, nw, Bv, nv);
}

int main(int argc, char **argv)
{
    int N = argc > 1 ? atoi(argv[1]) : 15;
    if (N < 1 || N > 20) { fprintf(stderr, "N must be between 1 and 20\n"); return 1; }
    printf("%3s %12s %9s\n", "n", "|R_n|", "p_n");
    for (n = 1; n <= N; n++) {
        u64 total = 1ULL << n, count = 0;
        for (u64 v = 0; v < total; v++)
            for (u64 w = 0; w < total; w++)
                count += has_property_R(v, w);
        printf("%3d %12llu %9.5f\n", n, count, (double)count / (double)(total * total));
        fflush(stdout);
    }
    return 0;
}
