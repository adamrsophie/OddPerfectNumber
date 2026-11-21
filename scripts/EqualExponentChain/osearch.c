/* Untrusted helper program for the OddPerfect Lean library.
   Helper for gen2.py: prints the r in an arithmetic progression up to B with p^e = 1 (mod r)
   and p != 1 (mod r), for a decimal p of any size.
   Build: cc -O2 -o osearch osearch.c   (gen2.py looks for it next to itself or in OSEARCH)
   Requires: a C compiler with unsigned __int128.
   Untrusted: every result is checked again by the Lean kernel.
   Paths: input and output files are read from and written to the current folder;
   sibling helper files are found next to this script.
   License: GPL 3, same as the repository. */

/* osearch p e step start B: print r in arithmetic progression start, start+step, ... <= B
   with p^e = 1 (mod r) and p != 1 (mod r). p is decimal (any size). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
typedef unsigned long long u64;
static u64 mulmod(u64 a, u64 b, u64 m) { return (u64)((u128)a * b % m); }
static u64 powmod(u64 a, u64 e, u64 m) { u64 r = 1 % m; while (e) { if (e & 1) r = mulmod(r, a, m); a = mulmod(a, a, m); e >>= 1; } return r; }
int main(int argc, char **argv) {
  const char *ps = argv[1]; u64 e = strtoull(argv[2], 0, 10), step = strtoull(argv[3], 0, 10);
  u64 r = strtoull(argv[4], 0, 10), B = strtoull(argv[5], 0, 10);
  size_t n = strlen(ps);
  for (; r <= B; r += step) {
    u64 pm = 0;
    for (size_t i = 0; i < n; i++) pm = (u64)(((u128)pm * 10 + (ps[i] - '0')) % r);
    if (pm == 1 % r || pm == 0) continue;
    if (powmod(pm, e, r) == 1) printf("%llu\n", r);
  }
  return 0;
}
