# SpecialFive: the special component `5 ^ 1` with components at most `10 ^ 24`

These scripts produce and replay the certificate of `OddPerfect/SpecialFiveData.lean`, which
together with the checker `OddPerfect/SpecialFiveCode.lean`, its soundness theorem
`OddPerfect/SpecialFiveCheck.lean` and `OddPerfect/SpecialFive.lean` proves: an odd perfect
number `N` with `v_5(N) = 1` has a prime factor `p` with `10 ^ 24 < p ^ v_p(N)`.

Ochem and Rao (Math. Comp. 81, 2012) proved that every odd perfect number has a component
above `10 ^ 62`, so the statement is a special case of a published theorem. The odd perfect
number conjecture is open.

## Files

* `gen.py K OUTDIR`: runs the search for `B = 10 ^ K` and writes `OUTDIR/cert.json` and
  `OUTDIR/SpecialFiveData.lean`. Needs Python 3 and sympy (only `factorint`). `K` must be a
  natural number at least 1 (decimal digits only). Exit status 0 when the files are written, 1
  when the search gets stuck or no chain has two exponents so the corrupted tree `certBad`
  cannot be built (for example `K = 1`; nothing is written), 2 for a usage error.
* `stage1.py B [MAXNODES] [small|large]`: the measuring search of the table below (counts
  only, no certificate), branching on the smallest or the largest forced prime.
* `replay.py CERT [tree|bad]`: an independent Python mirror of `SpecialFive.check` (standard
  library only, does not import `gen.py`). It checks the Pratt certificate, the fact table and
  the tree, and prints `ACCEPT` or `REJECT` with the first failing node.

## Commands

From this folder:

```
python3 -I gen.py 24 out24
python3 -I replay.py out24/cert.json tree
python3 -I replay.py out24/cert.json bad
shasum -a 256 out24/cert.json out24/SpecialFiveData.lean
```

Output:

```
K=24 nodes=747 rows=348 pratt=958 used=326
ACCEPT tree for B = 10^24
REJECT bad: stop at 3^4 <= B, state [(5, 1)]
c758d9ddf446d385045d85968c08be633b4269c93a403636e94888d682da3caa  out24/cert.json
0913773e16651436ecf219a6347ecd2830adeaa5587ee5641a3f0598c9393c3d  out24/SpecialFiveData.lean
```

The output is byte for byte reproducible: it was produced identically on two machines (sympy
1.12 and 1.14). Factorizations are unique, the search order is fixed, every list is sorted or
follows the search, and every Pratt witness is the smallest that works. `out24/SpecialFiveData.lean`
is copied unchanged to `OddPerfect/SpecialFiveData.lean`.

The corrupted tree `bad` (also in the Lean module as `certBad`, rejected there by the theorem
`go_certBad`) cuts the chain of exponents of 3 after the exponent 2, so the chain stops at
`3 ^ 4 ≤ 10 ^ 24` and the check fails.

## The search

A node is a list of entries `(p, e)` with `v_p(N) = e`, newest first, from `[(5, 1)]`. Every
other prime factor of `N` has an even exponent at least 2 (Euler, since `v_5(N) = 1` is odd).
Leaves, tried in order: capacity at an entry `r` (the rows `σ(p ^ e)` of the entries contain
more than `e_r` factors of `r`), abundance (`∏ σ(p ^ e) > 2 ∏ p ^ e`), and a forced prime `r`
(a prime factor of some row, not an entry) with `r ^ 2 > B`, the one with the cheapest Pratt
certificate. Otherwise the node branches on the largest forced prime that is not an entry, over
the exponents `2, 4, …` while `r ^ e ≤ B`. No search run met a stuck node (a node with no
forced prime left and no leaf); this is observed for every bound below, not proved.

The `nodes` count of `gen.py` counts certificate constructors (`br`, `cap`, `abund`, `stop`,
`ord`); the `states` of the table count the nodes of the search, that is the calls of the
search function (747 constructors and 389 states at `10 ^ 24`).

## Scaling

`python3 -I stage1.py B 200000 large` (and `small`), each run stopped at 200000 states or
10 minutes. The largest prime is the largest prime factor of any row `σ(p ^ e)` met.

| B | states (large) | size | capacity | abundance | stuck | largest prime | states (small) |
|---|---|---|---|---|---|---|---|
| 10^4 | 9 | 2 | 1 | 1 | 0 | 1093 | 10 |
| 10^6 | 15 | 6 | 1 | 2 | 0 | 797161 | 19 |
| 10^8 | 33 | 14 | 1 | 3 | 0 | 10378063 | 46 |
| 10^10 | 46 | 16 | 3 | 3 | 0 | 10378063 | 83 |
| 10^12 | 68 | 26 | 3 | 4 | 0 | 90849403261 | 242 |
| 10^14 | 98 | 30 | 5 | 5 | 0 | 20877076602037 | 831 |
| 10^16 | 139 | 41 | 9 | 6 | 0 | 412877527584271 | 3320 |
| 10^20 | 224 | 65 | 14 | 7 | 0 | 27083393683324732531 | |
| 10^24 | 389 | 114 | 22 | 9 | 0 | 109912203092239643840221 | |
| 10^30 | 698 | 202 | 44 | 11 | 0 | 172545754771028210096747645881 | |
| 10^33 | 894 | 257 | 51 | 12 | 0 | 751410597400064602523400427092397 | |
| 10^36 | over 1045 | | | | 0 | | |
| 10^40 | over 430 | | | | 0 | | |

At `10 ^ 36` and `10 ^ 40` the search did not finish within 10 minutes (1045 and 430 states
done): the tree stays small, but full factorizations of rows `σ(p ^ e)` with 30 to 80 digits
become the cost. On the Lean side the data module, with the Pratt certificate, the table and
the tree checked by three separate kernel theorems, takes 65 s and 5.3 GB at `10 ^ 24`
(958 Pratt entries); the Pratt check alone took 43 s and 5.2 GB, the table and tree 34 s and
5.4 GB (load included). At `10 ^ 30` the certificate needs 1972 Pratt entries and 1341 tree
constructors. The only build at `10 ^ 30` (unchunked lists, the full check run twice) failed
with a recursion depth error after 409 s and 21 GB. Memory is the binding limit (9 GB per
module); a larger bound needs the Pratt certificate split over several modules.
