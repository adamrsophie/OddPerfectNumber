# Restrained leaves: certificate formats

This note describes the finite certificates of `OddPerfect/RestrainedThree.lean`,
`RestrainedFour.lean` and `RestrainedFive.lean` and the scripts in this folder that produce or
recheck them. All three modules work in the setting of `restrained_three_sq_cases`: `N` is an odd
perfect number with special prime `q`, `r ≠ q` is a further prime, every other prime factor has
exponent exactly 2, and `3^2 ∥ N`. Write `phi3 t = t^2 + t + 1 = σ(t^2)`. A *slot* is a prime
factor `t ≡ 1 (mod 3)` with exponent 2; each slot spends one factor `3` of the budget `v_3(N) = 2`.

Every certificate is a Boolean function evaluated by the Lean kernel (`decide +kernel`); the
scripts mirror these functions line by line, so a disagreement shows up as a failed check.

## Root checks (all three modules)

`lowRoot V f lo hi` is a bisection with fuel `f` for the largest `m` with `phi3 m ≤ V`.
`rootIn L V` holds when `V` lies strictly between `phi3 m` and `phi3 (m + 1)` for the candidate
`m`, or when `phi3 m = V` and `m ∈ L`. Its soundness uses only the monotonicity of `phi3`, so any
fuel is acceptable; if `rootIn L V` holds and `phi3 t = V`, then `t ∈ L`. The boxes are
`box_7_13` (values `7^a 13^b < 10^16`, list `[0, 2, 3, 9, 18]`), `box_61_13` (values
`61^a 13^b < 10^16`, list `[0, 3]`), `box_13` (values `13^a < 10^16`, list `[0, 3]`) and
`box_A` (values `3 · 13^a < phi3 10^6`, list `[1, 22]`).

## RestrainedThree: the kill check (leaf `q = 13`, `r = 7`)

`strip p f n` divides `n` by `p` while possible, at most `f` times; `sqLo m f lo hi` is a
bisection for the integer square root. For a candidate slot `x`, `mpart x` is `phi3 x / 3` with
the factors `7` and `13` removed. Since a second slot `y` is the only other prime that can divide
`phi3 x / 3`, the check `kill x` holds when `x` is even or `1`, or when `m = mpart x` is not `1`,
`s = sqLo m` is the integer square root of `m`, `yfail x m` holds, and `yfail x s` holds when
`m = s^2`. Here `yfail x y` says that `y` is not a slot whose `phi3 y / 3` is supported on
`{7, 13, x}`. `kill_all` checks `kill x` for every `x < 10000` with `x ≡ 1 (mod 3)`, so slots are
at least `10000`.

## RestrainedFour: `slotOK` (leaf `r = 61`)

A slot `x` has `phi3 x = 3 · 13^d 61^a q^b`. `slotChk q V` is `rootIn` for `3V`, except that a
root `m` is accepted when `badSlot q m` holds (`m` even, `m ≢ 1 (mod 3)`, `m ∈ {13, 61, q}`,
`m ≤ 1`, or `m` has a divisor in `[2, 100)` below `m`). `slotOK q X` runs three nested loops
(`loop13`, `loop61`, `loopQ`, fuel 40 each) over `v = 13^d 61^a q^b` and checks `slotChk q v` for
every `v` with `3v < phi3 X`; then every slot is at least `X`. `qOK X q` is `qSmall q ∨ slotOK q X`,
where `qSmall q` holds for `q ≢ 1 (mod 12)`, `q ≤ 1`, `q` with a small divisor, or `q` in the list
`excList` of special primes refuted by forcing chains. The certificates are `qSmall` on
`range 157`, `qOK 8836` on `157 .. 9276` (four parts), `qOK 169` on `9277 .. 9464`, and
`slotOK 1000000 169` for larger `q`.

## RestrainedFive: forcing trees and the Pratt list (leaf `r = 13`)

A state is `(qk, sl, o2)`: the special prime `qk` if known (`0` when unknown and `q ≥ 337`), the
listed slots `sl` and the listed prime factors `o2 ≡ 2 (mod 3)`. A tree is `.dead` or
`.step p d cs co cq`. The source is `phi3 p` for a listed prime `p`, or `qk + 1` when `p = 0` and
`qk` is known. `check P Q0 qk sl o2 t` requires that `d` is prime (trial division below `100`, or
a member of `P`), divides the source, and is none of `2, 3, 13, qk` and no listed prime. Then `d`
can only be `q`, a new slot or a new member of `o2`, and each possible role must lead to a
subtree that passes:

* slot: needed when `d ≡ 1 (mod 3)`, fewer than two slots are listed and `d^3 ∤ source`; the
  subtree is checked at `(qk, d :: sl, o2)`;
* `o2`: needed when `d ≡ 2 (mod 3)` and `d^3 ∤ source`; subtree at `(qk, sl, d :: o2)`;
* `q`: needed when `qk = 0`, `d ≡ 1 (mod 12)` and `Q0 ≤ d`; subtree at `(d, sl, o2)`.

`.dead` never passes, so a passing tree refutes its root state. The excluded roles are excluded
by the 3-adic budget (at most two slots), by the caps `v_y(σ(p^2)) ≤ 2` and `v_y(q + 1) ≤ 2` for
`y` of exponent 2, and by `q ≡ 1 (mod 12)`, `q ≥ Q0`. Soundness is `check_sound`.

`qRoots` is a list of pairs `(q, t)` checked at `(q, [], [])`, one for every prime
`q ≡ 1 (mod 12)` below `337` other than `13` (`cover_q`); `zRoots` is a list of pairs `(z, t)`
checked at `(0, [z], [])`, one for every prime `z ≡ 1 (mod 3)` below `1225` other than `13`
(`cover_z`). The coverage tests accept a number that is `≤ 1`, has a divisor in `[2, 100)` below
itself, or is `13`.

`prattCert` is a flat Pratt certificate: entries `(p, a, fs)` with `fs` the prime factors of
`p - 1` with multiplicity, `a^(p-1) ≡ 1` and `a^((p-1)/f) ≢ 1 (mod p)` for each `f`, every `f`
either certified by an earlier entry or prime by trial division (`Pratt.check`). The list `P` of
`check` is the list of first components.

## Scripts

| script | checks or produces | requires |
|---|---|---|
| `gen13.py` | writes `prattCert`, `qRoots`, `zRoots` exactly as they appear in `RestrainedFive.lean` | sympy |
| `mirror13.py` | reads those three literals from a Lean file and replays `pratt_ok`, `cert_q`, `cert_z`, `cover_q`, `cover_z`, `box_13`, `box_A`, the weights of `rankin_tail3` and both closing inequalities | standard library |
| `mirror61.py` | replays `cert_small`, `cert_band1_0` .. `cert_band1_3`, `cert_band2`, `cert_free`, `box_61_13`, the forcing chains behind `excList`, the weights of `rankin_tail` and the three closing inequalities of `RestrainedFour.lean` | standard library |
| `mirror13_7.py` | replays `kill_all`, `box_7_13`, the weights of `tail_le` and the closing inequality of `RestrainedThree.lean` | standard library |

Each mirror prints one line per check and exits with status 1 if any check fails.
