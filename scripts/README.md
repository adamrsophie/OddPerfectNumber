# Search and generator scripts

These are programs that found certificates, proof trees, tables and primality witnesses used in the Lean library `OddPerfect`. The folder is not complete; see the last section. Nothing in this folder is trusted: every certificate these scripts produce is checked again by the Lean kernel inside the library, so a bug here can make a search fail but cannot make a false theorem pass. The scripts exist so that the searches can be repeated and extended.

## Requirements

* Python 3 (version 3.12.14 was used). Most scripts need only the standard library.
* `ExponentTenTwelve/gen.py` and `ExponentTenTwelve/explore.py` need sympy (version 1.14.0 was used).
* `LowerBound/gen.py` and `LowerBound/emit.py` use cypari2 (version 2.2.4 was used) for factoring; without it they fall back to Pollard rho and ECM and may produce a different tree.
* A C compiler for `EqualExponentChain/osearch.c`: `cc -O2 -o osearch osearch.c`.

Each script starts with a header that says what it computes, which Lean declaration uses the result, how to run it and roughly how long it takes. Scripts read and write their data files in the current folder and find their helper files next to themselves, so they can be run from any folder.

## Scripts

Verification status: "reproduces" means the published copy was run and its output was compared with the literal in the Lean file and agrees (whitespace and `private` modifiers aside). Helper files are listed with the script that uses them.

| module | script | what it produces | Lean declaration | verification status |
|---|---|---|---|---|
| Pratt | `Pratt/gen.py` | Pratt certificates | `OddPerfect.Pratt.witnessCert`, `prime_9701563`; `prime_4294967291` in `SupportBridges.lean` | reproduces the literal in `OddPerfect/Pratt.lean` and `OddPerfect/SupportBridges.lean` |
| McDaniel | `McDaniel/gen.py` (helper `tree2.py`) | forcing tree and proof body | module docstring tree and proof of `mcdaniel_of_three_dvd` | reproduces the literal in `OddPerfect/McDaniel.lean` |
| McDaniel | `McDaniel/gen2.py` | primality lemmas | the `pr_*` lemmas | reproduces the literal in `OddPerfect/McDaniel.lean` |
| EqualExponentChain | `EqualExponentChain/gen2.py` (helpers `nt.py`, `pm1.py`, `osearch.c`) | certificate JSON per prime `l` | `pc5` .. `pc29`, `ord5` .. `ord29`, `spec5` .. `spec29` | differs: for `l = 5, 7` and the ordinary part of `l = 17` the script finds certificates other than those in the Lean file (`checker.py` accepts the ones for `l = 5, 7`; repeated runs for `l = 5` agree with each other); the certificates used in the Lean file are stored in `EqualExponentChain/certs/`, and how the search was configured when they were found was not recorded; larger `l` not rerun (up to about half an hour per part) |
| EqualExponentChain | `EqualExponentChain/emit.py`, `assemble.py` | Lean text from certificate JSON | instances section | reproduces the literal in `OddPerfect/EqualExponentChain.lean`: run on the eight files in `EqualExponentChain/certs/`, `assemble.py` reproduces the whole instances section |
| EqualExponentChain | `EqualExponentChain/certs/cert_5.json` .. `cert_29.json` | the certificates used in the library (data, not a script) | `pc5` .. `pc29`, `ord5` .. `ord29`, `spec5` .. `spec29` | not rerun: data files; `checker.py` accepts all eight, and `assemble.py` turns them into the instances section |
| EqualExponentChain | `EqualExponentChain/checker.py` | independent recheck of certificate JSON | mirror of `checkAll` | runs; output not compared: a checker, no literal to compare; accepts the fresh certificates for `l = 5, 7` and all eight original ones |
| LargestPrimeFactor | `LargestPrimeFactor/gen4.py` | prime list `P`, product `M`, product `D` of the `q - 1`, row table `T` | `exists_primeFactor_gt` (`B = 10000`) | reproduces the literal in `OddPerfect/LargestPrimeFactor.lean` (`python3 gen4.py 10000 thm`, about 3.5 minutes; replaces `gen2.py`, which produced the earlier table for `B = 2000` and no longer matches the Lean file) |
| LowerBound | `LowerBound/emit.py` (helpers `gen.py`, `nt.py`, `pf.py`, `ecm.py`) | prime table and proof trees `tree3`, `tree5`, `tree7` | the section between "Generated trees (BEGIN)" and "(END)" (`table`, `table_ok`, `table_prime`, the tree parts) | reproduces the literal in `OddPerfect/LowerBound.lean` (`emit.py 79 trees.lean 3: 5:3 7:3,5` with cypari2, run with empty caches); the bound is a parameter of the script; not rerun without cypari2, where the fallback factoring may find fewer factors and build a different tree |
| LowerBound | `LowerBound/mktail.py` | final section | `good3`, `good5`, `good7`, `card_primeFactors_of_no_prime_lt_11`, `lower_bound` | reproduces the literal in `OddPerfect/LowerBound.lean` (`mktail.py 79 11 tail.lean`) |
| LowerBound | `LowerBound/check.py` | independent replay of `run` on the emitted definitions | mirror of `run` and of the table check | runs; output not compared: a checker, no literal to compare; accepts the table (2131 entries) and the three trees of `OddPerfect/LowerBound.lean` |
| OmegaSix | `OmegaSix/mirror.py` | mirror of the Lean solver, choice of `W` and fuel | `search_four`, `search_five` (`W = 10`, fuel 30) | runs; output not compared: no literal to compare; the mirror closes both searches with these parameters |
| OmegaFive | `OmegaFive/sup.py` (helper `pr.py`) | admissible supports | support ranges of `tab5`, `tab7`, `tab11`, `tab13` | runs; output not compared: the ranges in the Lean file are bounds chosen from this output |
| OmegaFive | `OmegaFive/chk.py` | mirror of `checkSupport` over the tables | `tab5` .. `tab13` | runs; output not compared: reports 104 supports, no failures |
| ExponentTenTwelve | `ExponentTenTwelve/gen.py` | primality lemmas and case lemma bodies | `pr_*` lemmas and the six case lemmas | reproduces the literal in `OddPerfect/ExponentTenTwelve.lean` |
| ExponentTenTwelve | `ExponentTenTwelve/explore.py` | forcing graph | forcing chains used by `gen.py` | runs; output not compared: every edge used in `gen.py` occurs in its output; the edges were chosen by hand |
| ExponentSix | `ExponentSix/fac.py` | factorizations of `σ(p^6)` | forcing chains of the module | runs; output not compared: every edge of the chains in the module docstring was checked with its `factor` function; the chains were chosen by hand |
| ThreeFreeException | `ThreeFreeException/exact.py` | box products and tail bounds | `boxProd` bounds `1717/1000`, `1450/1000` | runs; output not compared: the Lean file holds rounded bounds, not the values; the exact values 1.71661 and 1.44953 lie below the rounded bounds in the Lean file |
| ThreeFreeCert | `ThreeFreeCert/gen.py` | `Cert` terms | `certThreeFree17`, `23`, `41`, `47`, `53` | reproduces the literal in `OddPerfect/ThreeFreeCert.lean` |
| ThreeFreeTwo | `ThreeFreeTwo/explore.py`, `gen.py`, `genlean.py` (helpers `fac.py`, `ev4.py`) | `Ctx.table`, box lemmas, leaf lemmas | `Ctx.table`, `box_*`, `leaf_*` | runs; output not compared: the leaf tactics were edited by hand, so the file cannot match as a whole; table, all 9 boxes and the statements and data of all 41 leaves agree with `OddPerfect/ThreeFreeTwo.lean`; the closing tactic lines of the leaves were edited by hand afterwards |
| CountingClaytonHansen | `CountingClaytonHansen/mine2.py` (helper `simplex.py`) | optimal constants of the ledger LP | constants `99/37`, `187/37`, `51/19`, `46/19` | reproduces the literal in `OddPerfect/CountingClaytonHansen.lean` |
| SmallPrimes | `SmallPrimes/a.py` (helper `pr.py`) | counts and supports | the `*_le_card_*` theorems | reproduces the literal in `OddPerfect/SmallPrimes.lean` (each bound `L` is the prime before the printed prime) |
| SmallPrimes | `SmallPrimes/e.py` (helper `c.py`) | split trees | `excl_*` lemmas | runs; output not compared: checked only by hand against the case splits of the `excl_*` lemmas, which agree |
| ExceptionCount | `ExceptionCount/check.py` (helper `nt.py`) | prime lists and factorizations | `ecL29`, `ecL31` and the facts in the module docstring | reproduces the literal in `OddPerfect/ExceptionCount.lean` |
| AttackSize | `AttackSize/c.py` (helper `util.py`) | the bound `1416/793` and the partial products | `1416/793` and the sets `{5, 11, ..., 89}`, `{5, 7, 11, 13}` | reproduces the literal in `OddPerfect/AttackSize.lean` |
| Restrained | `Restrained/leaves.py` (helper `nt.py`) | parameters of leaves C4, C7, C9 | `B`, `α`, `β` arguments of `close_leaf` and the `ok` lists of the three leaves | reproduces the literal in `OddPerfect/Restrained.lean` (the parameters are constants in the script that it checks; the `ok` lists are the printed roots with 0 added) |
| Restrained | `Restrained/c36.py` | root lists | the `ok` lists of `box_13_19_*`, `box_61_31_*` | reproduces the literal in `OddPerfect/Restrained.lean` (each list is the printed roots with 0 added) |
| Restrained | `Restrained/c36b.py` | parameters of leaves C3, C6 | `α`, `β` of the one slot leaves | reproduces the literal in `OddPerfect/Restrained.lean` (constants in the script that it checks) |
| ForcingClosed | `ForcingClosed/pratt.py` (helpers `fc.py`, `rows.py`) | Pratt certificates | `pr_3169`, `pr_5419`, `pr_1674289`, `pr_3348577`, `pr_934415109937`, `pr_3737657091169` | reproduces the literal in `OddPerfect/ForcingClosed.lean` |
| ReciprocalSum | `ReciprocalSum/ex2.py` | rational bounds `a_p` | `twentythree_fortieths_lt_sum_inv` and its lemmas | reproduces the literal in `OddPerfect/ReciprocalSum.lean` |

## Not included

* `SecondLargestPrime`, `ForcingClosedBound`, `OmegaSeven`, `OmegaSevenFermat`, `EqualExponentChainMore`, `KanoldFive`, `CommonPrimeChain` and `ExponentTwentyFour`: their generator and check scripts are not yet published. For `EqualExponentChainMore`, the search for `l = 47` did not finish and has no certificate.
* Modules whose data were chosen by hand or come from classical sources, with no program to publish: for example `Spoof`, `SpoofInt`, `KanoldFour`, `AttackPrimality`, `Certificate` and the constants in `Seed/`.
* Modules that contain no data found by search.
* Exploratory programs whose results are not used in the library.

## License

GPL 3, same as the repository.
