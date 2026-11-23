# Certificate format of the excess four search

The three certificates of this folder are written by `search.py` and use the format of
`../TwoExceptionTwo/FORMAT.md`. This file lists only what differs. The Lean checker
`TwoExcEngine.checkV` reads a term translated from them (`../TwoExceptionTwo/engine.py`,
`gen_excess.py`) and checks it in the kernel; the text below is a specification, not a proof.

| file | family | V3 | EMAX | lines | leaves |
|---|---|---|---|---|---|
| `cert_ex_S1_100000_nojump_nolanded.jsonl` | S1 | 6 | 1 | 398 | 119 |
| `cert_ex_S2a_100000_nojump_nolanded.jsonl` | S2a | 4 | 2 | 362 | 158 |
| `cert_ex_S2b_100000_nolanded_ruleL.jsonl` | S2b | 2 | 3 | 235 | 113 |

## 1. The statement

N is an odd perfect number with special prime q (q ≡ 1 mod 4, odd exponent), v_3(N) = V3, and
at most EMAX prime factors other than 3 and q have exponent 4; every other prime factor except q
has exponent exactly 2. The tree claims that no such N exists.

## 2. Header

The header has three more fields: `FAM` (`S1`, `S2a` or `S2b`), `V3` and `EMAX` (the number of
primes of exponent 4 other than 3). `flags` holds `nolanded` always, `ruleL` for S2b, `cert`,
and `nojump` for S1 and S2a (a name only: `search.py` has no step that this flag switches off).
A run with the flag `pade` (no published certificate) also records `pade`: the search may then
close a deficient leaf by the Padé path of the tail test (`../TwoExceptionTwo/FORMAT.md`,
rule 6); the pure q bound keeps 1/(1 − S).
`MHIT`, `DMAX` and `KCAP` are as in the two exception format.

## 3. The prime 3 and the root

* The root record has the single value `["sig", 3, V3]`, the number σ(3^V3) (13, 121 or 1093).
* 3 is a key of `S` with budget V3 instead of 2 (leaf `cap3` when its contributions exceed V3),
  its least and upper ratio is σ(3^V3)/3^V3, and an abundant divisor lists it as `[3, V3]`.
* In the tail bound, c = V3 − (sum of S[3]) and the term 2c of d use this budget.

## 4. Roles

* **Exception.** One class `e4`, for every f, while there are fewer than EMAX exceptions:
  F[f] = [5, true, 4, true] (exponent exactly 4), its value is Φ_5(f) = σ(f^4)
  (`["cyc", 5, f]`), and its budget is 4. The action is
  `{role: e4, prime, D: 5, no3: true, kmin: 4}`. The classes `e` and `e3` do not occur.
* **q.** No facts on q are used: f = 5 and f ≡ 8 (mod 9) may be q, and the class `q` of a prime
  f ≡ 2 (mod 3) has no3 false. The classes `q0` and `q3` are as before.
* **Rule L** is applied only with the flag `ruleL` (S2b); no certificate has a `landedL` leaf.

## 5. Deficient leaves

In the search, each undecided exception adds 4 to d (a budget of 4 each), u = a, and when q is
undecided and K is empty the rows of type (e) are powers of q: one more slot of type (d) for the
row Φ_3(t) = q, and S = ((x+1)/x)² · s^−3/(1 − 1/s) with s = ⌊√x⌋ (proof field `pureq`). A
generator set K with q undecided stops the search.

Only two leaves of the three certificates are deficient: record 342 of S1 (x = 251, c = 4,
d = 12) and record 359 of S2a (x = 877, c = 3, d = 9). In both q is decided, there is no
undecided exception (a = b = 0), K is empty, there are no hits, `pureq` is false and S = 0, so
the leaf states U = H · ((x²+x+1)/x²)^{c+d} < 2 and has no field `rankin`. S2b has no
deficient leaf.

## 6. What the checker does not use

* The checker reads the items of each record, sorted by prime within the record, so the order
  in which the factoring library lists the factors of a value does not reach the Lean term; it
  does not read the stored states, contribution lists, `factors`, `d_items`, `H`, `a`, `b`, `c`,
  `d`, `S`, `U` or `pureq`, and recomputes what it needs.
* For V3 ≠ 2 the checker makes 3 an exact free key, a class with D = V3 + 1, no3 false and
  kmin = V3, that counts as one exception, so its exception bound is EMAX + 1; for S2b 3 is a
  square key and the bound is EMAX.
* For a deficient leaf without `rankin` the translator supplies witnesses that meet the checks
  of the Rankin part trivially (k = 24, B = 10^6, r_x = B + 1, m_L = 1, m_M = 10^−13), so S is
  below 10^−12 in the checker. Its d has no term for undecided exceptions; none exists in these
  leaves.
* The flags `nojump`, `ruleL` and `pade` are only checked for being allowed: the checker runs with the
  landed facts off and would reject a `landedL` leaf.
