# ShapeSmall: power series certificates and residue masks

Untrusted helper scripts for `OddPerfect/ShapeSmall.lean`, which uses the bound of
`OddPerfect/ShapeSeries.lean` (`prime_le_of_two_sq_eq_succ_sigma`) to show that
`2 t ^ 2 = 1 + σ(p ^ e)` has no solution with `p` an odd prime, `t` odd, `e` even, `0 < e < 16`
and `e + 1` prime (`e ∈ {2, 4, 6, 10, 12}`, `e = 2 h`). Every literal is checked again by the
Lean kernel or by `norm_num`; the scripts are not trusted. The module docstrings mention
`cert.py` and `gen.py`; those scripts were not kept, and these two replace them.

The shape of the inequality `q < m` is not excluded (exponents `e ≥ 16` stay open), and the odd
perfect number conjecture is open.

## The data

* Certificates `c1, c2, c3, c5, c6` and their `D`: `c_i = D f_i` where
  `f = √((1 - X / 2) / (1 - X)) = 1 + X / 4 + 7 X ^ 2 / 32 + ...`, so that `c_0 = D`,
  `2 ∑_{i + j = k} c_i c_j = D ^ 2` for `1 ≤ k ≤ h` and `2 c_i ≤ D`. `D` is the smallest value
  making `c_0, ..., c_h` integers (a power of 2); any multiple would also be a certificate.
* Bounds `p ≤ max 7 (2 D)`: 8, 64, 256, 16384, 131072 (`prime_le_h`, `no_sol_h`).
* `no_sol_1`: `p ≤ 8`, `u < 3` (the smallest `U` with `2 (2 U + 1) ^ 2 > 1 + σ(8 ^ 2)`) and
  the decided ranges `p < 9`, `u < 3`.
* Residue masks `L2, L3, L5, L6`: bit `r` of the mask for modulus `m` is set exactly when
  `1 + σ(r ^ (2 h))` is not twice a square modulo `m`. Given the modulus, the mask is forced.
  The moduli are the greedy choice among the odd primes below 100 and the powers of 2 up to 64
  (each step takes the modulus that removes the most odd numbers of `[3, 2 D]` still left, ties
  to the smaller modulus), stopped after 3, 4, 8 and 6 moduli.
* Kernel ranges `chk h Lh start n`: the odd numbers `3, 5, ..., 2 D + 1` in chunks of at most
  16384, and for `h = 6` the case split `i < 16384, 32768, 49152` of `no_sol_6`.
* `isq ... 10`: ten averaging steps of the integer square root in `nsq`.

## Files

* `gen.py`: recomputes every literal above, prints them in the order of the source with a tag,
  and with `--check PATH` compares them with the Lean file (exit 1 on any difference). Tags:
  `exact` (forced by the mathematics, with `D` minimal), `rule` (the masks: reproduced exactly
  by the greedy rule above, whose candidate set and counts were chosen) and `choice` (chunk
  size, case split, step count: the script verifies the property the proof needs). It also
  verifies that every odd number left by the masks passes the square root test within the
  step count.
* `replay.py`: an independent mirror (does not import `gen.py`) of the Lean definitions `geo`,
  `isq`, `sqOK`, `nsq`, `maskOK`, `filt`, `good`, `chk`, in exact integer arithmetic. It replays
  every `decide +kernel` goal (the key of `no_sol_1`, the certificate hypotheses, `Lh_ok`,
  `chkh_j`), the `norm_num` facts (`0 < D`, `1 ≤ h`, `max 7 (2 D) ≤ bound`) and the coverage of
  each `no_sol_h` by its chunks. With `bad` it runs two negative controls.

## Commands

From this folder, Python 3 standard library only:

```
python3 -I gen.py --check ../../OddPerfect/ShapeSmall.lean
python3 -I replay.py ../../OddPerfect/ShapeSmall.lean
python3 -I replay.py ../../OddPerfect/ShapeSmall.lean bad
```

Output of `gen.py --check` (last lines; the full output lists the 25 literal groups, plus the
five docstring values `D = ...` compared in check mode):

```
verified: h=2: 0 odd numbers left after the masks, the square root test is never reached
verified: h=3: 0 odd numbers left after the masks, the square root test is never reached
verified: h=5: 0 odd numbers left after the masks, the square root test is never reached
verified: h=6: 679 odd numbers left after the masks, square root test needs at most 6 steps (Lean uses 10)
check: 30 literal groups, 0 differences
```

Output of `replay.py` (22 lines, all `ACCEPT`, exit 0), for example:

```
ACCEPT prime_le_6: c6 = [65536, 16384, 14336, 12800, 11616, 10680, 9923] is a certificate of degree 6 with D = 65536, max 7 (2 D) = 131072 <= 131072
ACCEPT L6_ok: 6 masks
ACCEPT chk 6 L6 98307 16384
ACCEPT no_sol_6: chunks [(3, 16384), (32771, 16384), (65539, 16384), (98307, 16384)] cover the odd p in [3, 131072]
```

Output of the controls (exit 0 when both are rejected):

```
REJECTED L5 mask for modulus 17 with bit 0 added
  first failure: REJECT L5_ok: 8 masks
REJECTED c6 with last coefficient 9923 -> 9924
  first failure: REJECT prime_le_6: c6 = [65536, 16384, 14336, 12800, 11616, 10680, 9924] is a certificate of degree 6 with D = 65536, max 7 (2 D) = 131072 <= 131072
```

Each script runs in under a second. The output of `gen.py` is deterministic (two runs give the
same bytes; SHA-256 of `python3 -I gen.py` output:
`58d1bad5c674000aab7b1ef5b8b54e7a73c09077bcf92051997b6c3a020fcea5`).

SHA-256 of the scripts:

```
e344049043e9ab9f8921a96fd14c1510a0fa8f9d816c420f5eeb619dd92cb1b8  gen.py
227735fc9a7be13158aa5026ad612d209ede3edf94214538bd9bb432662b31dd  replay.py
```

License: GPL 3, same as the repository.
