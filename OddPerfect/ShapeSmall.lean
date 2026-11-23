import OddPerfect.ShapeSeries
import OddPerfect.SpecialBelow

/-!
# The open shape of `q < m`: the exponent is at least 16

In Euler's form `N = q ^ k * m ^ 2` of an odd perfect number, `q < m` is proved except in one
shape (`special_lt_or_index_prime_pow`, `OddPerfect/SpecialBelow.lean`, with the normal form of
`OddPerfect/EulerIndexPrimePower.lean`): `k = 1`, a prime `p ∣ m` with even exponent
`e = v_p(N) > 0`, `e + 1` prime, `σ(p ^ e) = q`, `q + 1 = 2 t ^ 2` and `t` odd.

This module uses only the equation `2 t ^ 2 = 1 + σ(p ^ e)` (with `t` odd for `e = 2`). For
`e = 2 h` with `h ∈ {1, 2, 3, 5, 6}` the power series certificate of `OddPerfect/ShapeSeries.lean`
bounds `p` by `max 7 (2 D_h)` (at most `131072`), and a kernel checked search shows that no odd
`p` up to that bound gives a solution. Since `e + 1` is prime, `e ∉ {8, 14}`. Hence `e ≥ 16`
(`sixteen_le_exponent_of_le_special`).

The finite search runs over every odd number up to the bound (prime or not). Each number is
first tested against residue masks: bit `r` of the mask for the modulus `m` is set when
`1 + σ(r ^ e)` is not twice a square modulo `m`; the masks are verified in the kernel. The few
numbers that pass every mask are handled by an integer square root (averaging steps
`x ↦ (x + v / x) / 2`) with the check `r ^ 2 < v < (r + 1) ^ 2`. The certificates and
the masks were produced by a script; every one of them is verified here in the kernel, so the
script is not trusted.

The shape itself is not excluded: exponents `e ≥ 16` stay open. Novelty was not verified.
-/

open Finset
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace ShapeSmall

/-- `geo r n = 1 + r + ... + r ^ (n - 1)`, by the recurrence `geo r (n + 1) = 1 + r geo r n`. -/
def geo (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + r * geo r n

/-- `geo` is the geometric sum. -/
theorem geo_eq (r : ℕ) : ∀ n, geo r n = ∑ i ∈ range n, r ^ i
  | 0 => rfl
  | n + 1 => by
    rw [geo, geo_eq r n, Finset.sum_range_succ', Finset.mul_sum, pow_zero, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

/-- `geo` respects congruences of the base. -/
theorem geo_modEq (r m : ℕ) : ∀ n, geo (r % m) n ≡ geo r n [MOD m]
  | 0 => rfl
  | n + 1 => (Nat.ModEq.refl 1).add ((Nat.mod_modEq r m).mul (geo_modEq r m n))

/-- `k` averaging steps for the integer square root of `v`, starting from `x` (never increasing). -/
def isq (v : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => isq v k (min x ((x + v / x) / 2))

/-- `r ^ 2 < v < (r + 1) ^ 2`, so `v` is not a square. -/
def sqOK (v r : ℕ) : Bool := decide (r * r < v) && decide (v < (r + 1) * (r + 1))

/-- `(1 + σ(p ^ (2 h))) / 2` is strictly between two consecutive squares. -/
def nsq (h p : ℕ) : Bool :=
  sqOK ((1 + geo p (2 * h + 1)) / 2) (isq ((1 + geo p (2 * h + 1)) / 2) 10 (p ^ h))

/-- Soundness of the square root test. -/
theorem nsq_sound {h p : ℕ} (H : nsq h p = true) (t : ℕ) :
    2 * t ^ 2 ≠ 1 + geo p (2 * h + 1) := by
  intro ht
  unfold nsq at H
  rw [← ht, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)] at H
  generalize isq (t ^ 2) 10 (p ^ h) = r at H
  simp only [sqOK, Bool.and_eq_true, decide_eq_true_eq] at H
  rcases Nat.lt_or_ge r t with h1 | h1
  · have h1' : r + 1 ≤ t := h1
    have : (r + 1) * (r + 1) ≤ t ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul h1' h1'
    exact absurd (lt_of_lt_of_le H.2 this) (lt_irrefl _)
  · have : t ^ 2 ≤ r * r := by rw [pow_two]; exact Nat.mul_le_mul h1 h1
    exact absurd (lt_of_lt_of_le H.1 this) (lt_irrefl _)

/-- The mask `mask` for the modulus `m` is correct: for every residue `r` whose bit is set,
`1 + σ(r ^ (2 h))` is not twice a square modulo `m`. -/
def maskOK (h m mask : ℕ) : Bool :=
  decide (0 < m) && (List.range m).all fun r =>
    (mask >>> r) % 2 == 0 ||
      (List.range m).all fun x => (2 * x * x) % m != (1 + geo r (2 * h + 1)) % m

/-- Some mask of the list has the bit of `p` set. -/
def filt (L : List (ℕ × ℕ)) (p : ℕ) : Bool := L.any fun mm => (mm.2 >>> (p % mm.1)) % 2 == 1

/-- Soundness of the residue masks. -/
theorem filt_sound {h : ℕ} {L : List (ℕ × ℕ)}
    (hL : L.all (fun mm => maskOK h mm.1 mm.2) = true) {p : ℕ} (H : filt L p = true) (t : ℕ) :
    2 * t ^ 2 ≠ 1 + geo p (2 * h + 1) := by
  intro ht
  obtain ⟨⟨m, mask⟩, hmem, hbit⟩ := List.any_eq_true.mp H
  have hok := List.all_eq_true.mp hL _ hmem
  simp only [maskOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hok
  simp only [beq_iff_eq] at hbit
  obtain ⟨hm, hall⟩ := hok
  rcases hall (p % m) (Nat.mod_lt _ hm) with h0 | h1
  · rw [h0] at hbit
    exact absurd hbit (by norm_num)
  · apply h1 (t % m) (Nat.mod_lt _ hm)
    have e1 : 2 * (t % m) * (t % m) ≡ 2 * t ^ 2 [MOD m] := by
      rw [pow_two, ← mul_assoc]
      exact ((Nat.ModEq.refl 2).mul (Nat.mod_modEq t m)).mul (Nat.mod_modEq t m)
    have e2 : 1 + geo (p % m) (2 * h + 1) ≡ 1 + geo p (2 * h + 1) [MOD m] :=
      (Nat.ModEq.refl 1).add (geo_modEq p m _)
    rw [ht] at e1
    exact e1.trans e2.symm

/-- One number passes: by a mask or by the square root test. -/
def good (h : ℕ) (L : List (ℕ × ℕ)) (p : ℕ) : Bool := filt L p || nsq h p

/-- The numbers `p, p + 2, ..., p + 2 (n - 1)` all pass. -/
def chk (h : ℕ) (L : List (ℕ × ℕ)) : ℕ → ℕ → Bool
  | _, 0 => true
  | p, n + 1 => good h L p && chk h L (p + 2) n

/-- Soundness of the range checker. -/
theorem chk_sound {h : ℕ} {L : List (ℕ × ℕ)} :
    ∀ n p, chk h L p n = true → ∀ i < n, good h L (p + 2 * i) = true
  | 0, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, p, H, i, hi => by
    simp only [chk, Bool.and_eq_true] at H
    rcases i with _ | i
    · simpa using H.1
    · have := chk_sound n (p + 2) H.2 i (by omega)
      rwa [show p + 2 * (i + 1) = p + 2 + 2 * i by ring]

/-- A passing number gives no solution of `2 t ^ 2 = 1 + σ(p ^ (2 h))`. -/
theorem good_sound {h : ℕ} {L : List (ℕ × ℕ)}
    (hL : L.all (fun mm => maskOK h mm.1 mm.2) = true) {p : ℕ} (H : good h L p = true)
    (t : ℕ) : 2 * t ^ 2 ≠ 1 + ∑ i ∈ range (2 * h + 1), p ^ i := by
  rw [← geo_eq]
  simp only [good, Bool.or_eq_true] at H
  rcases H with H | H
  · exact filt_sound hL H t
  · exact nsq_sound H t

/-- The case `h = 1`: only `p = 5, t = 4` solves the equation below `8`, and `t` is even. -/
theorem no_sol_1 {p t : ℕ} (hp : p % 2 = 1) (hB : p ≤ 8) (ht : Odd t) :
    2 * t ^ 2 ≠ 1 + ∑ i ∈ range (2 * 1 + 1), p ^ i := by
  rw [← geo_eq]
  obtain ⟨u, rfl⟩ := ht
  intro h
  have hu : u < 3 := by
    have : geo p (2 * 1 + 1) = 1 + p * (1 + p * 1) := by simp [geo]
    rw [this] at h
    nlinarith
  have key : ∀ p < 9, ∀ u < 3, p % 2 = 1 → 2 * (2 * u + 1) ^ 2 ≠ 1 + geo p (2 * 1 + 1) := by
    decide +kernel
  exact key p (by omega) u hu hp h


/-- Certificate of degree `1` (from `cert.py`): `D = 4`. -/
def c1 (i : ℕ) : ℕ := [4, 1].getD i 0

/-- The certificate bound for `e = 2`. -/
theorem prime_le_1 {p t : ℕ} (hp : p.Prime)
    (ht : 2 * t ^ 2 = 1 + ∑ i ∈ range (2 * 1 + 1), p ^ i) : p ≤ 8 := by
  have hb := prime_le_of_two_sq_eq_succ_sigma (h := 1) (D := 4) c1 (by norm_num) rfl
    (fun k hk1 hk2 => by interval_cases k; all_goals decide +kernel)
    (fun i hi1 hi2 => by interval_cases i; all_goals decide +kernel) (by norm_num) hp ht
  exact hb.trans (by norm_num)

/-- Certificate of degree `2` (from `cert.py`): `D = 32`. -/
def c2 (i : ℕ) : ℕ := [32, 8, 7].getD i 0

/-- The certificate bound for `e = 4`. -/
theorem prime_le_2 {p t : ℕ} (hp : p.Prime)
    (ht : 2 * t ^ 2 = 1 + ∑ i ∈ range (2 * 2 + 1), p ^ i) : p ≤ 64 := by
  have hb := prime_le_of_two_sq_eq_succ_sigma (h := 2) (D := 32) c2 (by norm_num) rfl
    (fun k hk1 hk2 => by interval_cases k; all_goals decide +kernel)
    (fun i hi1 hi2 => by interval_cases i; all_goals decide +kernel) (by norm_num) hp ht
  exact hb.trans (by norm_num)

/-- Certificate of degree `3` (from `cert.py`): `D = 128`. -/
def c3 (i : ℕ) : ℕ := [128, 32, 28, 25].getD i 0

/-- The certificate bound for `e = 6`. -/
theorem prime_le_3 {p t : ℕ} (hp : p.Prime)
    (ht : 2 * t ^ 2 = 1 + ∑ i ∈ range (2 * 3 + 1), p ^ i) : p ≤ 256 := by
  have hb := prime_le_of_two_sq_eq_succ_sigma (h := 3) (D := 128) c3 (by norm_num) rfl
    (fun k hk1 hk2 => by interval_cases k; all_goals decide +kernel)
    (fun i hi1 hi2 => by interval_cases i; all_goals decide +kernel) (by norm_num) hp ht
  exact hb.trans (by norm_num)

/-- Certificate of degree `5` (from `cert.py`): `D = 8192`. -/
def c5 (i : ℕ) : ℕ := [8192, 2048, 1792, 1600, 1452, 1335].getD i 0

/-- The certificate bound for `e = 10`. -/
theorem prime_le_5 {p t : ℕ} (hp : p.Prime)
    (ht : 2 * t ^ 2 = 1 + ∑ i ∈ range (2 * 5 + 1), p ^ i) : p ≤ 16384 := by
  have hb := prime_le_of_two_sq_eq_succ_sigma (h := 5) (D := 8192) c5 (by norm_num) rfl
    (fun k hk1 hk2 => by interval_cases k; all_goals decide +kernel)
    (fun i hi1 hi2 => by interval_cases i; all_goals decide +kernel) (by norm_num) hp ht
  exact hb.trans (by norm_num)

/-- Certificate of degree `6` (from `cert.py`): `D = 65536`. -/
def c6 (i : ℕ) : ℕ := [65536, 16384, 14336, 12800, 11616, 10680, 9923].getD i 0

/-- The certificate bound for `e = 12`. -/
theorem prime_le_6 {p t : ℕ} (hp : p.Prime)
    (ht : 2 * t ^ 2 = 1 + ∑ i ∈ range (2 * 6 + 1), p ^ i) : p ≤ 131072 := by
  have hb := prime_le_of_two_sq_eq_succ_sigma (h := 6) (D := 65536) c6 (by norm_num) rfl
    (fun k hk1 hk2 => by interval_cases k; all_goals decide +kernel)
    (fun i hi1 hi2 => by interval_cases i; all_goals decide +kernel) (by norm_num) hp ht
  exact hb.trans (by norm_num)

/-- Residue masks for `e = 4` (from `gen.py`). -/
def L2 : List (ℕ × ℕ) :=
  [(16, 31610),
   (61, 976115313843303296),
   (13, 3152)]

/-- The masks for `e = 4` are correct. -/
theorem L2_ok : L2.all (fun mm => maskOK 2 mm.1 mm.2) = true := by
  decide +kernel

/-- Kernel check of a chunk of odd numbers for `e = 4`. -/
theorem chk2_0 : chk 2 L2 3 32 = true := by
  decide +kernel

/-- No odd `p` with `3 ≤ p ≤ 64` satisfies `2 t ^ 2 = 1 + σ(p ^ 4)`. -/
theorem no_sol_2 {p t : ℕ} (hp : p % 2 = 1) (h3 : 3 ≤ p) (hB : p ≤ 64) :
    2 * t ^ 2 ≠ 1 + ∑ i ∈ range (2 * 2 + 1), p ^ i := by
  obtain ⟨i, rfl⟩ : ∃ i, p = 3 + 2 * i := ⟨(p - 3) / 2, by omega⟩
  refine good_sound L2_ok ?_ t
  have := chk_sound _ _ chk2_0 (i - 0) (by omega)
  rwa [show 3 + 2 * (i - 0) = 3 + 2 * i by omega] at this

/-- Residue masks for `e = 6` (from `gen.py`). -/
def L3 : List (ℕ × ℕ) :=
  [(64, 9078834612657880056),
   (89, 152035843598095809998092920),
   (23, 3260336),
   (29, 64060800)]

/-- The masks for `e = 6` are correct. -/
theorem L3_ok : L3.all (fun mm => maskOK 3 mm.1 mm.2) = true := by
  decide +kernel

/-- Kernel check of a chunk of odd numbers for `e = 6`. -/
theorem chk3_0 : chk 3 L3 3 128 = true := by
  decide +kernel

/-- No odd `p` with `3 ≤ p ≤ 256` satisfies `2 t ^ 2 = 1 + σ(p ^ 6)`. -/
theorem no_sol_3 {p t : ℕ} (hp : p % 2 = 1) (h3 : 3 ≤ p) (hB : p ≤ 256) :
    2 * t ^ 2 ≠ 1 + ∑ i ∈ range (2 * 3 + 1), p ^ i := by
  obtain ⟨i, rfl⟩ : ∃ i, p = 3 + 2 * i := ⟨(p - 3) / 2, by omega⟩
  refine good_sound L3_ok ?_ t
  have := chk_sound _ _ chk3_0 (i - 0) (by omega)
  rwa [show 3 + 2 * (i - 0) = 3 + 2 * i by omega] at this

/-- Residue masks for `e = 10` (from `gen.py`). -/
def L5 : List (ℕ × ℕ) :=
  [(64, 6908099591761984506),
   (17, 32754),
   (7, 58),
   (79, 94833111187368456485530),
   (97, 67979843127376104338325591160),
   (67, 70016744034256342912),
   (29, 90798560),
   (11, 2)]

/-- The masks for `e = 10` are correct. -/
theorem L5_ok : L5.all (fun mm => maskOK 5 mm.1 mm.2) = true := by
  decide +kernel

/-- Kernel check of a chunk of odd numbers for `e = 10`. -/
theorem chk5_0 : chk 5 L5 3 8192 = true := by
  decide +kernel

/-- No odd `p` with `3 ≤ p ≤ 16384` satisfies `2 t ^ 2 = 1 + σ(p ^ 10)`. -/
theorem no_sol_5 {p t : ℕ} (hp : p % 2 = 1) (h3 : 3 ≤ p) (hB : p ≤ 16384) :
    2 * t ^ 2 ≠ 1 + ∑ i ∈ range (2 * 5 + 1), p ^ i := by
  obtain ⟨i, rfl⟩ : ∃ i, p = 3 + 2 * i := ⟨(p - 3) / 2, by omega⟩
  refine good_sound L5_ok ?_ t
  have := chk_sound _ _ chk5_0 (i - 0) (by omega)
  rwa [show 3 + 2 * (i - 0) = 3 + 2 * i by omega] at this

/-- Residue masks for `e = 12` (from `gen.py`). -/
def L6 : List (ℕ × ℕ) :=
  [(16, 31610),
   (71, 976519289014162310802),
   (67, 6234094719330932946),
   (97, 10834321022980272689388483842),
   (61, 772963487559521578),
   (23, 1358602)]

/-- The masks for `e = 12` are correct. -/
theorem L6_ok : L6.all (fun mm => maskOK 6 mm.1 mm.2) = true := by
  decide +kernel

/-- Kernel check of a chunk of odd numbers for `e = 12`. -/
theorem chk6_0 : chk 6 L6 3 16384 = true := by
  decide +kernel

/-- Kernel check of a chunk of odd numbers for `e = 12`. -/
theorem chk6_1 : chk 6 L6 32771 16384 = true := by
  decide +kernel

/-- Kernel check of a chunk of odd numbers for `e = 12`. -/
theorem chk6_2 : chk 6 L6 65539 16384 = true := by
  decide +kernel

/-- Kernel check of a chunk of odd numbers for `e = 12`. -/
theorem chk6_3 : chk 6 L6 98307 16384 = true := by
  decide +kernel

/-- No odd `p` with `3 ≤ p ≤ 131072` satisfies `2 t ^ 2 = 1 + σ(p ^ 12)`. -/
theorem no_sol_6 {p t : ℕ} (hp : p % 2 = 1) (h3 : 3 ≤ p) (hB : p ≤ 131072) :
    2 * t ^ 2 ≠ 1 + ∑ i ∈ range (2 * 6 + 1), p ^ i := by
  obtain ⟨i, rfl⟩ : ∃ i, p = 3 + 2 * i := ⟨(p - 3) / 2, by omega⟩
  refine good_sound L6_ok ?_ t
  by_cases c0 : i < 16384
  · have := chk_sound _ _ chk6_0 (i - 0) (by omega)
    rwa [show 3 + 2 * (i - 0) = 3 + 2 * i by omega] at this
  by_cases c1 : i < 32768
  · have := chk_sound _ _ chk6_1 (i - 16384) (by omega)
    rwa [show 32771 + 2 * (i - 16384) = 3 + 2 * i by omega] at this
  by_cases c2 : i < 49152
  · have := chk_sound _ _ chk6_2 (i - 32768) (by omega)
    rwa [show 65539 + 2 * (i - 32768) = 3 + 2 * i by omega] at this
  have := chk_sound _ _ chk6_3 (i - 49152) (by omega)
  rwa [show 98307 + 2 * (i - 49152) = 3 + 2 * i by omega] at this


end ShapeSmall

open ShapeSmall in
/-- For an odd prime `p`, an odd `t` and an even exponent `0 < e < 16` with `e + 1` prime,
`2 t ^ 2 ≠ 1 + σ(p ^ e)`. The exponents are `e ∈ {2, 4, 6, 10, 12}`; for each, the power series
certificate bounds `p` and a kernel checked search over the odd numbers below the bound finds no
solution (for `e = 2` the only one, `p = 5`, `t = 4`, has `t` even). -/
theorem two_sq_ne_one_add_sigma_of_lt_sixteen {p e t : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ht : Odd t) (he : Even e) (he0 : 0 < e) (he1 : (e + 1).Prime) (he16 : e < 16) :
    2 * t ^ 2 ≠ 1 + σ 1 (p ^ e) := by
  intro H
  rw [sigma_one_apply_prime_pow hp] at H
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨j, rfl⟩ := he
  rw [show j + j = 2 * j by ring] at H he1
  have hj1 : 1 ≤ j := by omega
  have hj7 : j ≤ 7 := by omega
  interval_cases j
  · exact no_sol_1 hodd (prime_le_1 hp H) ht H
  · exact no_sol_2 hodd h3 (prime_le_2 hp H) H
  · exact no_sol_3 hodd h3 (prime_le_3 hp H) H
  · norm_num at he1
  · exact no_sol_5 hodd h3 (prime_le_5 hp H) H
  · exact no_sol_6 hodd h3 (prime_le_6 hp H) H
  · norm_num at he1

/-- In Euler's form `N = q ^ k * m ^ 2` of an odd perfect number with `q ∤ m`, if `m ≤ q` (the
open shape of the inequality `q < m`), then some prime `p ∣ m` has `σ(p ^ v_p(N)) = q` and
exponent `v_p(N) ≥ 16`. Only the equation `2 t ^ 2 = 1 + σ(p ^ e)` of the shape is used. The
shape is not excluded: exponents `e ≥ 16` remain open. Novelty was not verified. -/
theorem sixteen_le_exponent_of_le_special {N q k m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hle : m ≤ q) :
    ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ σ 1 (p ^ N.factorization p) = q ∧ 16 ≤ N.factorization p := by
  rcases special_lt_or_index_prime_pow h hq hN hqm with hlt | ⟨rfl, p, hp, hpm, hI, hσ, hpr⟩
  · omega
  refine ⟨p, hp, hpm, hσ, ?_⟩
  have hN1 : N = q * m ^ 2 := by rw [hN, pow_one]
  have hpN : p ∣ N := by rw [hN1]; exact (hpm.trans (dvd_pow_self m two_ne_zero)).mul_left q
  have hb : 0 < N.factorization p := hp.factorization_pos_of_dvd h.ne_zero hpN
  obtain ⟨M, -, -, hMo, -, -, -, hqM, -, -, hev, -⟩ :=
    eulerIndex_prime_pow_normal_form h hq hN1 hqm hp hb hI
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h.not_two_dvd hpN
  by_contra hlt
  push Not at hlt
  exact two_sq_ne_one_add_sigma_of_lt_sixteen hp hp2 hMo hev hb hpr hlt (by omega)

end OddPerfect

#print axioms OddPerfect.ShapeSmall.geo_eq
#print axioms OddPerfect.ShapeSmall.geo_modEq
#print axioms OddPerfect.ShapeSmall.nsq_sound
#print axioms OddPerfect.ShapeSmall.filt_sound
#print axioms OddPerfect.ShapeSmall.chk_sound
#print axioms OddPerfect.ShapeSmall.good_sound
#print axioms OddPerfect.ShapeSmall.no_sol_1
#print axioms OddPerfect.ShapeSmall.prime_le_1
#print axioms OddPerfect.ShapeSmall.prime_le_2
#print axioms OddPerfect.ShapeSmall.prime_le_3
#print axioms OddPerfect.ShapeSmall.prime_le_5
#print axioms OddPerfect.ShapeSmall.prime_le_6
#print axioms OddPerfect.ShapeSmall.L2_ok
#print axioms OddPerfect.ShapeSmall.chk2_0
#print axioms OddPerfect.ShapeSmall.no_sol_2
#print axioms OddPerfect.ShapeSmall.L3_ok
#print axioms OddPerfect.ShapeSmall.chk3_0
#print axioms OddPerfect.ShapeSmall.no_sol_3
#print axioms OddPerfect.ShapeSmall.L5_ok
#print axioms OddPerfect.ShapeSmall.chk5_0
#print axioms OddPerfect.ShapeSmall.no_sol_5
#print axioms OddPerfect.ShapeSmall.L6_ok
#print axioms OddPerfect.ShapeSmall.chk6_0
#print axioms OddPerfect.ShapeSmall.chk6_1
#print axioms OddPerfect.ShapeSmall.chk6_2
#print axioms OddPerfect.ShapeSmall.chk6_3
#print axioms OddPerfect.ShapeSmall.no_sol_6
#print axioms OddPerfect.two_sq_ne_one_add_sigma_of_lt_sixteen
#print axioms OddPerfect.sixteen_le_exponent_of_le_special
