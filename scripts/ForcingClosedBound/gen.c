/* Untrusted helper program for the OddPerfect Lean library.
   Step 2 for OddPerfect/ForcingClosedBound.lean: candidate generator (see the comment below).
   Used by: OddPerfect/ForcingClosedBound.lean as an independent derivation of the deletion
   rounds (see solve.py); the Lean lemmas themselves are written by mkrounds.py.
   Build: cc -O2 -o gen gen.c -lm
   Run: ./gen 1000 small_l_1000.txt > cand_1000.txt
   Requires: a C compiler. Running time: under a second for P = 1000.
   Untrusted: every result is checked again by the Lean kernel.
   Paths: input and output files are read from and written to the current folder;
   sibling helper files are found next to this script.
   License: GPL 3, same as the repository. */

/* Candidate generator for P-smooth cyclotomic rows Phi_l(p), p, l odd primes, 2l+1 <= P.
   Every prime factor r != l of Phi_l(p) has ord_r(p) = l, so r = 1 (mod 2l); r <= P means r in R_l.
   Output lines:
     C p l r1 r2 ...   (small l) p passed the size filter or has a Wieferich hit; r_i are all
                       r in R_l with ord_r(p) = l (each appears once; exact valuations later)
     W p l             (big l) some r in R_l has p^l = 1 mod r^2 (and p != 1 mod r)
   Size filter (small l): with no r^2 | p^l - 1, the P-smooth part M of Phi_l(p) is at most
   l * prod(hits); M < p^(l-1) forces M != Phi_l(p). Logs are fixed point upper / lower bounds.
   usage: gen P small_l_file > out */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

typedef unsigned __int128 u128;
static int P;
static int *spf;

static uint64_t powmod(uint64_t a, uint64_t e, uint64_t m) {
  uint64_t r = 1 % m; a %= m;
  while (e) { if (e & 1) r = (uint64_t)((u128)r * a % m); a = (uint64_t)((u128)a * a % m); e >>= 1; }
  return r;
}

static int odd_prime_factors(int n, int *out) {
  int k = 0;
  while (n > 1) { int q = spf[n]; if (q != 2) out[k++] = q; while (n % q == 0) n /= q; }
  return k;
}

static uint64_t primroot(int r) {
  int fs[32], k = 0, n = r - 1;
  while (n > 1) { int q = spf[n]; fs[k++] = q; while (n % q == 0) n /= q; }
  for (uint64_t g = 2;; g++) {
    int ok = 1;
    for (int i = 0; i < k; i++) if (powmod(g, (r - 1) / fs[i], r) == 1) { ok = 0; break; }
    if (ok) return g;
  }
}

static uint64_t *proot;

/* order-l roots mod r^2: Teichmueller lift of zeta mod r is zeta^r mod r^2 */
static uint64_t lift2(uint64_t zeta, uint64_t r) {
  uint64_t m = r * r, w = powmod(zeta, r, m);
  if (w % r != zeta) abort();
  return w;
}

int main(int argc, char **argv) {
  P = atoi(argv[1]);
  spf = calloc(P + 1, sizeof(int));
  for (int i = 2; i <= P; i++) if (!spf[i]) for (int j = i; j <= P; j += i) if (!spf[j]) spf[j] = i;
  char *isp = calloc(P + 1, 1);
  for (int i = 3; i <= P; i++) if (spf[i] == i) isp[i] = 1;
  char *small = calloc(P + 1, 1);
  FILE *f = fopen(argv[2], "r"); int x;
  while (fscanf(f, "%d", &x) == 1) small[x] = 1;
  fclose(f);
  proot = calloc(P + 1, sizeof(uint64_t));
  for (int r = 3; r <= P; r++) if (isp[r]) proot[r] = primroot(r);
  uint64_t *LG = calloc(P + 1, sizeof(uint64_t)), *LGF = calloc(P + 1, sizeof(uint64_t));
  for (int i = 3; i <= P; i++) if (isp[i]) {
    double v = log2((double)i) * 16777216.0;
    LG[i] = (uint64_t)ceil(v) + 2; LGF[i] = (uint64_t)floor(v) - 2;
  }
  /* big l: Wieferich enumeration, one pass over r */
  int fs[32];
  long wcount = 0;
  for (int r = 3; r <= P; r++) if (isp[r]) {
    int k = odd_prime_factors(r - 1, fs);
    for (int i = 0; i < k; i++) {
      int l = fs[i];
      if (small[l]) continue;
      uint64_t m = (uint64_t)r * r;
      uint64_t zeta = powmod(proot[r], (r - 1) / l, r);
      uint64_t w = lift2(zeta, r);
      if (powmod(w, l, m) != 1) abort();
      uint64_t y = 1;
      for (int j = 1; j < l; j++) {
        y = (uint64_t)((u128)y * w % m);
        for (uint64_t p = y; p <= (uint64_t)P; p += m)
          if (isp[p] && p % r != 1) { printf("W %llu %d\n", (unsigned long long)p, l); wcount++; }
      }
    }
  }
  fprintf(stderr, "big-l Wieferich pairs: %ld\n", wcount);
  /* small l: level-1 sieve with hit lists, level-2 flags */
  uint64_t *acc = calloc(P + 1, sizeof(uint64_t));
  char *wf = calloc(P + 1, 1);
  int *head = malloc((P + 1) * sizeof(int));
  size_t cap = 1 << 22, n = 0;
  int *nr = malloc(cap * sizeof(int)), *nx = malloc(cap * sizeof(int));
  long ccount = 0;
  for (int l = 3; 2 * l + 1 <= P; l++) if (isp[l] && small[l]) {
    memset(acc, 0, (P + 1) * sizeof(uint64_t)); memset(wf, 0, P + 1);
    for (int i = 0; i <= P; i++) head[i] = -1;
    n = 0;
    for (int r = 2 * l + 1; r <= P; r += 2 * l) if (isp[r]) {
      uint64_t zeta = powmod(proot[r], (r - 1) / l, r), y = 1;
      uint64_t m = (uint64_t)r * r, w = lift2(zeta, r), y2 = 1;
      if (powmod(zeta, l, r) != 1 || zeta == 1) abort();
      for (int j = 1; j < l; j++) {
        y = y * zeta % r;
        for (uint64_t p = y; p <= (uint64_t)P; p += r) if (isp[p]) {
          acc[p] += LG[r];
          if (n == cap) { cap *= 2; nr = realloc(nr, cap * sizeof(int)); nx = realloc(nx, cap * sizeof(int)); }
          nr[n] = r; nx[n] = head[p]; head[p] = (int)n; n++;
        }
        y2 = (uint64_t)((u128)y2 * w % m);
        if (y2 % r != y) abort();
        for (uint64_t p = y2; p <= (uint64_t)P; p += m) if (isp[p]) wf[p] = 1;
      }
    }
    for (int p = 3; p <= P; p++) if (isp[p]) {
      uint64_t s = acc[p] + (p % l == 1 ? LG[l] : 0);
      if (wf[p] || s >= (uint64_t)(l - 1) * LGF[p]) {
        printf("C %d %d", p, l);
        for (int t = head[p]; t >= 0; t = nx[t]) printf(" %d", nr[t]);
        printf("\n"); ccount++;
      }
    }
  }
  fprintf(stderr, "small-l candidates: %ld\n", ccount);
  return 0;
}
