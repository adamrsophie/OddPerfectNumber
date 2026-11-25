# SpecialFiveMore: the special component `5 ^ 1` with components at most `10 ^ 33`

These scripts produce and replay the split certificate of the modules
`OddPerfect/SpecialFiveMore*.lean`, which prove with the unchanged checker
`OddPerfect.SpecialFive.check` and its soundness theorem `OddPerfect.SpecialFive.check_sound`:
an odd perfect number `N` with `v_5(N) = 1` has a prime factor `p` with
`10 ^ 33 < p ^ v_p(N)` (theorem
`OddPerfect.exists_component_gt_ten_pow_thirty_three_of_factorization_five_eq_one`).

Ochem and Rao (Math. Comp. 81, 2012) proved that every odd perfect number has a component
above `10 ^ 62`, so the statement is a special case of a published theorem; nothing here is
new mathematics. The odd perfect number conjecture is open.

## Why a split

The landed certificate of `scripts/SpecialFive` sits in one data module, which at `10 ^ 24`
already took 5.3 GB. At `10 ^ 33` the certificate has 2753 Pratt entries, 801 table rows and
1725 tree constructors. `OddPerfect.SpecialFiveMoreLemmas` restates the checker in pieces:

* `check_append`: a Pratt certificate `a ++ b` is accepted when `a` is, and `b` is accepted
  from a list of known primes that all occur as primes of `a` (with `checkAux_mono` and
  `checkAux_append`);
* `tabOK_append`: the table check of a concatenation;
* `go_br`, `go_ord`, `go_stop`: the tree check at a branch, a chain step and a chain end
  reduces to the checks of the children.

## Modules (import order)

* `SpecialFiveMoreLemmas`: the lemmas above.
* `SpecialFiveMorePratt0` to `SpecialFiveMorePratt5`: chunks of 500 Pratt entries, each
  checked by `Pratt.checkAux prattK<i> prattC<i>`, where `prattK<i>` lists the primes from 200
  on that the chunk uses and earlier chunks certify.
* `SpecialFiveMorePc`: `pratt` is the concatenation; `pratt_ok : Pratt.check pratt = true` by
  `check_append`, each known list checked against the earlier chunks by `decide +kernel`.
* `SpecialFiveMoreTab0` to `SpecialFiveMoreTab3`: chunks of 201 table rows, each checked by
  `tabOK pratt`.
* `SpecialFiveMoreTable`: `tab` is the concatenation; `tab_ok` by `tabOK_append`.
* `SpecialFiveMoreTree0` to `SpecialFiveMoreTree2`: 79 subtrees of at most 150 constructors,
  packed into modules of at most 600 constructors, each checked by `go (10 ^ 33) tab` at its
  state written out. `SpecialFiveMoreTree0` also holds the negative control `pieceBad`.
* `SpecialFiveMore`: the 92 skeleton nodes above the subtrees, glued by `go_br`, `go_ord`,
  `go_stop`; `check_cert : SpecialFive.check (10 ^ 33) pratt tab cert = true`; the theorem.

## Files

* `gen.py K OUTDIR [PRATT_CHUNK TAB_CHUNK PIECE TREE_CAP]` (defaults 500, 201, 150, 600):
  runs the search for `B = 10 ^ K` and writes `OUTDIR/cert.json`, `OUTDIR/modules.txt` and
  the Lean modules in `OUTDIR/OddPerfect/`. Standard library only (trial division, Miller
  and Rabin, Pollard's rho with Brent's cycle search). The search is the one of
  `scripts/SpecialFive/gen.py`. `K` and the four chunk sizes must be natural numbers at least
  1 (decimal digits only). Exit status 0 when the files are written, 1 when the search gets
  stuck, no chain has two exponents (no corrupted piece, for example `K = 1`) or the Pratt
  certificate is empty (for example `K = 2`), with nothing written, and 2 for a usage error.
* `replay.py CERT [tree|bad]`: an independent mirror of the Lean modules (standard library
  only, does not import `gen.py`): each Pratt chunk with only its known list, each known list
  inside the earlier chunks, each table chunk against the whole Pratt certificate, the
  skeleton walked from `[(5, 1)]` with each subtree checked at the state the walk reaches
  (which must be its recorded state, each subtree used once), and the module manifest
  `modules` of `cert.json` as a partition of the subtrees (each subtree in exactly one nonempty
  module, no subtree that does not exist; otherwise `REJECT`, exit status 1). Prints `ACCEPT`
  or `REJECT`.

## Commands

From this folder:

```
python3 -I gen.py 33 out33
python3 -I replay.py out33/cert.json tree
python3 -I replay.py out33/cert.json bad
shasum -a 256 out33/cert.json
cd out33/OddPerfect && shasum -a 256 *.lean
```

Output (the generator takes about 3 minutes on one core):

```
K=33 nodes=1725 rows=801 pratt=2753 used=756 pratt_chunks=6 tab_chunks=4 pieces=79
  tree_modules=3 skeleton=92   (one line)
ACCEPT tree for B = 10^33
REJECT bad: stop at 13^4 <= B, state [(3, 2), (5, 1)]
558d103db1417fd9f6327542b1a624e495b462a5c21af12433625b5d5c3124b9  out33/cert.json
556ffad2fab2d03792a20d50502c8d36faa25c2fe913bdd0275b00e2fe99bd62  SpecialFiveMore.lean
764220440a8066cbc469c37121bf3ccf20897eb2db01abd22d76ae4d4613e89f  SpecialFiveMorePc.lean
98e43134daef375f3994cb5df92059e45836163a29483e960b9933cadd261496  SpecialFiveMorePratt0.lean
75f2f5749a4aaa5bc199997db6db7563ec2b69167e474ecafee1993092877f09  SpecialFiveMorePratt1.lean
9c8134aaeadaf2cff418591c57ab1a0fef704e77f1c4f6154f4d56ac9722d4c1  SpecialFiveMorePratt2.lean
d689fa93ff2188b33d276966b9215f074278817e929456cbc5a17d4a7821e89a  SpecialFiveMorePratt3.lean
c046b32371e3c9ed2b1aae86b77c65b91728a47556bd1640527233196aab1dd7  SpecialFiveMorePratt4.lean
546553cb4de1477f3a5466f80fc101cedda4195beaafed03213f6d3055a7113a  SpecialFiveMorePratt5.lean
f1cef6d0e2185a8a94ca6d0cecafe23584c9021f379faf154db4b9eb253bf5be  SpecialFiveMoreTab0.lean
6259a6d66a2e91636ee4f41c8b3c9f0396700b118681f47c761b5dce4a65f506  SpecialFiveMoreTab1.lean
2806c9004b7fd42d895c03f98953d919bdd7cf10278c82a2c9d0f6afed640cec  SpecialFiveMoreTab2.lean
5820792e12be96c8e4b789f54476dd134434b6a4f02ecc7f71b3d1cc2db8e661  SpecialFiveMoreTab3.lean
238d7387b4e62bb97381343e77bb6067c3a886d0eae0d4ef12e4b5632dea6014  SpecialFiveMoreTable.lean
04adb9eb7f2636f7317394885437197b856e98e5e1402fae11ccb3bfb074d85b  SpecialFiveMoreTree0.lean
0a6f822eb3b4a1d12ddaf529c188fa57a9b6b585ee8dbf3f6fec312036439973  SpecialFiveMoreTree1.lean
e43aa62f743a352cfa6b8cebc38d1b262fe912d589c6301d0a9e9565452af7d9  SpecialFiveMoreTree2.lean
```

The files of `out33/OddPerfect/` are copied unchanged to `OddPerfect/`
(`SpecialFiveMoreLemmas.lean` is written by hand). The flat Pratt certificate, the flat table
and the reassembled tree are identical to those of `scripts/SpecialFive/gen.py 33` (sympy
1.14), checked at `10 ^ 27` and `10 ^ 33`.

The corrupted subtree `pieceBad` (rejected in Lean by `pieceBad_rejected`) cuts the chain of
exponents of 13 in subtree 0 after the exponent 2, so the chain stops at `13 ^ 4 ≤ 10 ^ 33`.

## Measured build (build server; CPU time and peak memory of each compile process)

| module | CPU s | peak GB |
|---|---|---|
| SpecialFiveMoreLemmas | 2.1 | 2.1 |
| SpecialFiveMorePratt0 to 5 | 18.2, 20.5, 22.8, 25.0, 25.5, 12.8 | 3.6, 3.9, 4.1, 4.4, 4.4, 3.2 |
| SpecialFiveMorePc | 29.4 | 3.4 |
| SpecialFiveMoreTab0 to 3 | 22.9, 29.6, 30.0, 30.1 | 5.1, 6.0, 6.0, 6.0 |
| SpecialFiveMoreTable | 1.8 | 2.1 |
| SpecialFiveMoreTree0 to 2 | 16.7, 19.3, 16.9 | 2.5, 2.4, 2.5 |
| SpecialFiveMore | 6.7 | 6.7 |

Independent modules were compiled in parallel, each in its own process.

The table check is the most memory hungry part (400 rows per module took 9.1 and 9.9 GB, so
the chunks have 201 rows). The search was not run above `10 ^ 33`: the README of
`scripts/SpecialFive` records that it did not finish at `10 ^ 36` within 10 minutes.
