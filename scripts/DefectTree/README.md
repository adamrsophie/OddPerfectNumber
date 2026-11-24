# DefectTree: factor chain trees with the defect ledger

Untrusted helper scripts for the Lean modules `OddPerfect/DefectTreeCode.lean` (the checker),
`OddPerfect/DefectTreeCheck.lean` (its soundness theorem `check_sound`),
`OddPerfect/DefectTreeTwoData.lean` and `OddPerfect/DefectTreeFourData.lean` (generated data and
kernel checks), `OddPerfect/DefectTreeTwo.lean` and `OddPerfect/DefectTreeFour.lean` (the
results). Every literal is checked again by the Lean kernel; the soundness theorem carries no
data.

Files:

* `search.py`: the search; writes a certificate with full witnesses (JSON) and extends the
  frozen row table.
* `rows.json`: the frozen row table: the odd prime factorizations of the rows used
  (`σ(p ^ e)` for ordinary primes, `p + 1` for the special prime) and the factorizations of
  `p - 1` needed for the Pratt certificates. With this file present, regeneration needs no
  factoring and no sympy.
* `gen.py`: writes the Lean data module (parameters, Pratt certificate, fact table, certificate
  term, kernel check).
* `check.py`: an independent replay of a certificate in exact arithmetic.
* `cert2.json`, `cert4.json`: the certificates for `K = 2` and `K = 4`.

Commands (from this folder; Python 3, sympy only for rows missing from `rows.json`):

```
python3 search.py 2 0 3 3 none rows.json cert2.json
python3 search.py 4 0 3 3 none rows.json cert4.json
python3 gen.py cert2.json rows.json Two ../../OddPerfect/DefectTreeTwoData.lean
python3 gen.py cert4.json rows.json Four ../../OddPerfect/DefectTreeFourData.lean
python3 check.py cert2.json rows.json
python3 check.py cert4.json rows.json
```

The arguments of `search.py` are `K W U ROOT CAP ROWS OUT`: the bound `K` for
`W * ω(N) + supportDefect N q`, the weight `W`, the lower bound `U` for the prime factors, the
root prime, and the cap for the total excess (`none` or an integer). Flags: `noledger` switches
the ledger rule off, `maxnodes=M` stops after `M` nodes and `maxexp=E` leaves a chain open above the
exponent `E` (open leaves are reported),
`factor_seconds=S` bounds the time per row factorization (after a timeout only proven prime
factors are kept, which is still a valid lower bound).

Regeneration is deterministic: running the commands twice gives the same `cert2.json`,
`cert4.json`, `rows.json` and Lean files (compare with `shasum`).

Controls:

```
python3 gen.py cert2.json rows.json Bad DefectTreeBadControl.lean corrupt
python3 check.py cert2.json rows.json corrupt
python3 search.py 2 0 3 3 none rows_copy.json o.json noledger maxnodes=1000 maxexp=8 \
    factor_seconds=2
```

The first writes a module stating `check ... = false` for the certificate with its first
capacity witness changed (a control outside the library); the second shows the rejected node;
the third shows that the search does not close without the ledger rule.

## Total excess at least 5 and at least 6

Certificates for `OddPerfect/ExcessFive.lean` (`five_le_excess`) and `OddPerfect/ExcessSix.lean`
(`six_le_excess`). Suppose the total excess `T` is at most `c` (`c = 4`, then `c = 5`). The defect
identity and `#escapeRows ≤ 1` give `ω(N) + D ≤ 5 * c + 6`. If `3 ∣ N` the root is 3 with lower
bound 3; otherwise the smallest prime factor `p` is the root and the lower bound, and Grün's
bound with `ω(N) ≤ 5 * T + 2` gives `3 * p < 10 * c + 10`, so `p` is 5, 7, 11, 13 for `c = 4` and
5, 7, 11, 13, 17, 19 for `c = 5`.

Files:

* `cert_excess5_<root>.json`: parameters `K = 26`, `w = 1`, cap 4, roots 3, 5, 7, 11, 13
  (1782, 290, 159, 19 and 52 nodes).
* `cert_excess6_<root>.json`: parameters `K = 31`, `w = 1`, cap 5, roots 3, 5, 7, 11, 13, 17, 19
  (4522, 761, 362, 31, 99, 130 and 71 nodes).
* `rows.json`: the frozen row table, extended by these searches (743 rows, 2110 factorizations
  of `p - 1`). It contains the earlier table, so `cert2.json` and `cert4.json` regenerate
  unchanged.
* `gen.py`: the flag `split` (with `gnodes=G`) writes the data of a large certificate to several
  modules: `<OUT>P.lean` (the Pratt certificate in parts of 150 entries, one kernel check per
  part), `<OUT>T.lean` (the fact table in parts of 150 rows), `<OUT>G0.lean`, `<OUT>G1.lean`,
  ... (subtrees of at most `G` nodes at their states, one kernel check per subtree) and
  `<OUT>.lean` (the rest of the tree, assembled with `simp`, and the full check
  `check params pratt tab cert = true`). The equations used for the assembly are in
  `OddPerfect/DefectTreeSplit.lean`. Without the flag the output is unchanged.

Commands (from this folder):

```
for u in 3 5 7 11 13; do
  python3 search.py 26 1 $u $u 4 rows.json cert_excess5_$u.json factor_seconds=60
done
for u in 3 5 7 11 13 17 19; do
  python3 search.py 31 1 $u $u 5 rows.json cert_excess6_$u.json factor_seconds=60
done
python3 gen.py cert_excess5_3.json rows.json Excess5R3 ../../OddPerfect/ExcessFiveData3.lean split
for u in 5 7 11 13; do
  python3 gen.py cert_excess5_$u.json rows.json Excess5R$u ../../OddPerfect/ExcessFiveData$u.lean
done
python3 gen.py cert_excess6_3.json rows.json Excess6R3 ../../OddPerfect/ExcessSixData3.lean \
    split gnodes=800
for u in 5 17; do
  python3 gen.py cert_excess6_$u.json rows.json Excess6R$u ../../OddPerfect/ExcessSixData$u.lean \
      split
done
for u in 7 11 13 19; do
  python3 gen.py cert_excess6_$u.json rows.json Excess6R$u ../../OddPerfect/ExcessSixData$u.lean
done
for f in cert_excess5_*.json cert_excess6_*.json; do python3 check.py $f rows.json; done
```

With `rows.json` present no factoring is needed. Running the commands twice gives the same
certificates, row table and Lean files (compare with `shasum`).

Controls:

```
python3 check.py cert_excess5_3.json rows.json corrupt
python3 search.py 26 1 3 3 4 rows_copy.json o.json noledger maxnodes=20000 maxexp=12 \
    factor_seconds=60
```

The first rejects the certificate with its first capacity witness changed (first rejected node:
the capacity leaf at the state `3^2 7^2 19^2 127^2`, special prime 13, witness 5). The second runs
the search for root 3 and cap 4 without the ledger rule on a copy of the table: it also closes
(1867 nodes, no open leaf), as do the roots 5, 7, 11 and 13 (350, 168, 24 and 56 nodes). For
the cap 4 the ledger rule only shortens the trees.

The results bound the total excess from below; the method does not bound it from above, and
the odd perfect number conjecture is open.

License: GPL 3, same as the repository.
