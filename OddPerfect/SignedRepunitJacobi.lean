import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Jacobi symbols of signed repunits

For natural numbers `X` and odd `n` let `A_n = (X ^ n + 1) / (X + 1)`, so that
`(X + 1) * A_n = X ^ n + 1` and `A_n = ∑ i < n, (-X) ^ i`. This module proves two arithmetic
statements for `X ≡ 1 (mod 4)`; no odd perfect number appears.

* `jacobiSym_signedRepunit`: for odd `n` and `m` with `gcd(n, m) = 1`, the Jacobi symbol
  `J(A_n | A_m)` is `1`.
* `alternating_sum_ne_prime_mul_sq`: for an odd prime `p`, `X ^ p + 1 ≠ (X + 1) * (p * y ^ 2)`,
  that is `A_p` is not `p` times a square.

The hypothesis `X ≡ 1 (mod 4)` is needed: for `X = 23` one has `A_3 = 507 = 3 * 13 ^ 2`.

No published source was checked for the two statements of this module, so their novelty is not
verified. The proof here is elementary and self contained.

Method. `A_n ≡ 1 (mod 4)`, `A_n ≡ 1 (mod X)` and `A_n ≡ n (mod X + 1)` follow from the
recursion `A_(n + 2) = X ^ 2 A_n - X + 1`. Reciprocity gives `J(X | A_m) = J(A_m | X) = 1`. Since
`(X + 1) A_m = X ^ m + 1` divides `X ^ (2 k m) - 1`, the index `n` may be reduced modulo `2 m`
to an odd `r < m` (either `A_n ≡ A_r` or `X ^ r A_n ≡ A_r` modulo `A_m`), and reciprocity
together with strong induction on `m` gives the first statement. For the second, `A_p = p y ^ 2`
forces `p ∣ X + 1` by Fermat's little theorem, hence `A_c ≡ c (mod p)`; an odd quadratic
nonresidue `c` modulo `p` then gives `1 = J(A_c | p y ^ 2) = -J(A_c | y) ^ 2 ≤ 0`.
-/

namespace OddPerfect

/-- The signed repunit `(X ^ n + 1) / (X + 1)`; for odd `n` it equals `∑ i < n, (-X) ^ i`. -/
def signedRepunit (X n : ℕ) : ℕ := (X ^ n + 1) / (X + 1)

/-- The defining identity of the signed repunit: `(X + 1) * A_n = X ^ n + 1` for odd `n`. -/
theorem signedRepunit_mul {X n : ℕ} (hn : Odd n) : (X + 1) * signedRepunit X n = X ^ n + 1 :=
  Nat.mul_div_cancel' (by simpa using hn.nat_add_dvd_pow_add_pow X 1)

namespace SignedRepunitJacobi

private lemma srj_mul {X n : ℕ} (hn : Odd n) : (X + 1) * signedRepunit X n = X ^ n + 1 :=
  signedRepunit_mul hn

private lemma srj_mul_int {X n : ℕ} (hn : Odd n) :
    ((X : ℤ) + 1) * (signedRepunit X n : ℤ) = (X : ℤ) ^ n + 1 := by
  exact_mod_cast srj_mul (X := X) hn

private lemma srj_one (X : ℕ) : signedRepunit X 1 = 1 := by
  simp [signedRepunit, Nat.div_self (Nat.succ_pos X)]

private lemma srj_succ_succ {X n : ℕ} (hn : Odd n) :
    (signedRepunit X (n + 2) : ℤ) = (X : ℤ) ^ 2 * signedRepunit X n - X + 1 := by
  have h1 := srj_mul_int (X := X) hn
  have h2 := srj_mul_int (X := X) (hn.add_even even_two)
  have hX : ((X : ℤ) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hX
  linear_combination h2 - (X : ℤ) ^ 2 * h1

/-- The congruences of `A_n` for odd `n`, by induction. -/
private lemma srj_facts_aux {X : ℕ} (hX : X % 4 = 1) (k : ℕ) :
    1 ≤ (signedRepunit X (2 * k + 1) : ℤ) ∧ (4 : ℤ) ∣ signedRepunit X (2 * k + 1) - 1 ∧
      (X : ℤ) ∣ signedRepunit X (2 * k + 1) - 1 ∧
      ((X : ℤ) + 1) ∣ signedRepunit X (2 * k + 1) - ((2 * k + 1 : ℕ) : ℤ) := by
  have hX4 : (4 : ℤ) ∣ (X : ℤ) - 1 := by omega
  have hX1 : (1 : ℤ) ≤ X := by omega
  induction k with
  | zero => simp [srj_one]
  | succ k ih =>
    obtain ⟨h1, ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := ih
    obtain ⟨d, hd⟩ := hX4
    have hrec := srj_succ_succ (X := X) (n := 2 * k + 1) (odd_two_mul_add_one k)
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, hrec]
    refine ⟨by nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg (X : ℤ))],
      ⟨(X : ℤ) ^ 2 * a + X * d, ?_⟩, ⟨X * signedRepunit X (2 * k + 1) - 1, ?_⟩,
      ⟨((X : ℤ) - 1) * signedRepunit X (2 * k + 1) - 1 + c, ?_⟩⟩
    · linear_combination (X : ℤ) ^ 2 * ha + (X : ℤ) * hd
    · ring
    · push_cast at hc ⊢
      linear_combination hc

private lemma srj_facts {X n : ℕ} (hX : X % 4 = 1) (hn : Odd n) :
    1 ≤ signedRepunit X n ∧ signedRepunit X n % 4 = 1 ∧
      (X : ℤ) ∣ signedRepunit X n - 1 ∧
      ((X : ℤ) + 1) ∣ signedRepunit X n - (n : ℤ) := by
  obtain ⟨k, rfl⟩ := hn
  obtain ⟨h1, h4, hXd, hX1⟩ := srj_facts_aux hX k
  exact ⟨by exact_mod_cast h1, by omega, hXd, hX1⟩

private lemma srj_odd {X n : ℕ} (hX : X % 4 = 1) (hn : Odd n) : Odd (signedRepunit X n) :=
  Nat.odd_iff.mpr (by have := (srj_facts hX hn).2.1; omega)

/-- `J(X | A_m) = 1`. -/
private lemma srj_jacobi_base {X m : ℕ} (hX : X % 4 = 1) (hm : Odd m) :
    jacobiSym (X : ℤ) (signedRepunit X m) = 1 := by
  rw [jacobiSym.quadratic_reciprocity_one_mod_four hX (srj_odd hX hm),
    jacobiSym.mod_left' (Int.ModEq.symm (Int.modEq_iff_dvd.mpr (srj_facts hX hm).2.2.1)),
    jacobiSym.one_left]

private lemma srj_dvd_pow_sub_one (X m k : ℕ) :
    ((X : ℤ) ^ m + 1) ∣ (X : ℤ) ^ (2 * k * m) - 1 := by
  have h1 : ((X : ℤ) ^ m + 1) ∣ (X : ℤ) ^ (2 * m) - 1 := ⟨(X : ℤ) ^ m - 1, by ring⟩
  have h2 := sub_dvd_pow_sub_pow ((X : ℤ) ^ (2 * m)) 1 k
  rw [one_pow, ← pow_mul] at h2
  rw [show 2 * k * m = 2 * m * k by ring]
  exact h1.trans h2

/-- Reduction by adding a multiple of `2 m` to the index. -/
private lemma srj_red_add {X m r : ℕ} (hm : Odd m) (hr : Odd r) (k : ℕ) :
    (signedRepunit X m : ℤ) ∣
      (signedRepunit X (r + 2 * k * m) : ℤ) - signedRepunit X r := by
  have hX : (0 : ℤ) < X + 1 := by positivity
  have hM := srj_mul_int (X := X) hm
  have h1 := srj_mul_int (X := X) hr
  have h2 := srj_mul_int (X := X) (n := r + 2 * k * m) (hr.add_even ⟨k * m, by ring⟩)
  have hd := srj_dvd_pow_sub_one X m k
  rw [← hM] at hd
  have e : ((X : ℤ) + 1) * ((signedRepunit X (r + 2 * k * m) : ℤ) - signedRepunit X r) =
      (X : ℤ) ^ r * ((X : ℤ) ^ (2 * k * m) - 1) := by
    linear_combination h2 - h1
  have : ((X : ℤ) + 1) * signedRepunit X m ∣
      ((X : ℤ) + 1) * ((signedRepunit X (r + 2 * k * m) : ℤ) - signedRepunit X r) := by
    rw [e]; exact Dvd.dvd.mul_left hd _
  exact (mul_dvd_mul_iff_left hX.ne').mp this

/-- Reduction by reflecting the index at a multiple of `2 m`. -/
private lemma srj_red_sub {X m n r k : ℕ} (hm : Odd m) (hn : Odd n) (hr : Odd r)
    (hk : n + r = 2 * k * m) :
    (signedRepunit X m : ℤ) ∣ (X : ℤ) ^ r * signedRepunit X n - signedRepunit X r := by
  have hX : (0 : ℤ) < X + 1 := by positivity
  have hM := srj_mul_int (X := X) hm
  have h1 := srj_mul_int (X := X) hn
  have h2 := srj_mul_int (X := X) hr
  have hd := srj_dvd_pow_sub_one X m k
  rw [← hM] at hd
  have e : ((X : ℤ) + 1) * ((X : ℤ) ^ r * signedRepunit X n - signedRepunit X r) =
      (X : ℤ) ^ (2 * k * m) - 1 := by
    rw [← hk]
    linear_combination (X : ℤ) ^ r * h1 - h2
  have : ((X : ℤ) + 1) * signedRepunit X m ∣
      ((X : ℤ) + 1) * ((X : ℤ) ^ r * signedRepunit X n - signedRepunit X r) := by
    rw [e]; exact hd
  exact (mul_dvd_mul_iff_left hX.ne').mp this

private lemma srj_coprime {n m r : ℕ} (h : Nat.Coprime n m) (hg : Nat.gcd r m ∣ n) :
    Nat.Coprime m r := by
  have h1 : Nat.gcd r m ∣ Nat.gcd n m := Nat.dvd_gcd hg (Nat.gcd_dvd_right r m)
  rw [h] at h1
  rw [Nat.Coprime, Nat.gcd_comm]
  exact Nat.dvd_one.mp h1

end SignedRepunitJacobi

open SignedRepunitJacobi

/-- **Jacobi symbols of signed repunits.** For `X ≡ 1 (mod 4)` and odd coprime `n`, `m`, with
`A_n = (X ^ n + 1) / (X + 1)`: `J(A_n | A_m) = 1`. Arithmetic only (no odd perfect number). No
published source was checked; novelty not verified. The proof is elementary (reciprocity and a
Euclidean descent on the index). -/
theorem jacobiSym_signedRepunit {X n m : ℕ} (hX : X % 4 = 1) (hn : Odd n) (hm : Odd m)
    (hnm : Nat.Coprime n m) :
    jacobiSym (signedRepunit X n) (signedRepunit X m) = 1 := by
  revert n
  revert hm
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm n hn hnm
  rcases (show m = 1 ∨ 3 ≤ m by obtain ⟨j, hj⟩ := hm; omega) with rfl | hm3
  · rw [srj_one]; exact jacobiSym.one_right _
  have hdiv := Nat.div_add_mod n (2 * m)
  set s := n % (2 * m) with hs
  set k := n / (2 * m) with hk
  have hslt : s < 2 * m := Nat.mod_lt _ (by omega)
  have hs2 : s % 2 = 1 := by
    rw [hs, Nat.mod_mod_of_dvd n (dvd_mul_right 2 m)]; exact Nat.odd_iff.mp hn
  have hso : Odd s := Nat.odd_iff.mpr hs2
  obtain ⟨t, ht⟩ : ∃ t, t = m * k := ⟨_, rfl⟩
  have hdiv' : 2 * t + s = n := by rw [ht, ← hdiv]; ring
  have hsm : s ≠ m := by
    intro hsm
    have hmn : m ∣ n := by
      rw [← hdiv, hsm]
      exact dvd_add (Dvd.dvd.mul_right (dvd_mul_left m 2) k) dvd_rfl
    have := Nat.Coprime.eq_one_of_dvd hnm.symm hmn
    omega
  have hAm := srj_odd hX hm
  rcases lt_or_gt_of_ne hsm with hlt | hgt
  · -- `n = s + 2 k m` with `s < m`
    have hred := srj_red_add (X := X) hm hso k
    rw [show s + 2 * k * m = n by rw [← hdiv]; ring] at hred
    rw [jacobiSym.mod_left' (Int.ModEq.symm (Int.modEq_iff_dvd.mpr hred)),
      jacobiSym.quadratic_reciprocity_one_mod_four (srj_facts hX hso).2.1 hAm]
    refine ih s hlt hso hm (srj_coprime hnm ?_)
    rw [← hdiv]
    exact dvd_add ((Nat.gcd_dvd_right s m).mul_left 2 |>.mul_right k) (Nat.gcd_dvd_left s m)
  · -- `n + r = 2 (k + 1) m` with `r = 2 m - s < m`
    set r := 2 * m - s with hr
    have hro : Odd r := Nat.odd_iff.mpr (by omega)
    have hsum : n + r = 2 * (k + 1) * m := by
      have : 2 * (k + 1) * m = 2 * t + 2 * m := by rw [ht]; ring
      rw [this]; omega
    have hred := srj_red_sub (X := X) hm hn hro hsum
    have hJ := jacobiSym.mod_left' (b := signedRepunit X m)
      (Int.ModEq.symm (Int.modEq_iff_dvd.mpr hred))
    rw [jacobiSym.mul_left, jacobiSym.pow_left, srj_jacobi_base hX hm, one_pow, one_mul] at hJ
    rw [hJ, jacobiSym.quadratic_reciprocity_one_mod_four (srj_facts hX hro).2.1 hAm]
    refine ih r (by omega) hro hm (srj_coprime hnm ?_)
    have hg : Nat.gcd r m ∣ n + r := by
      rw [hsum]; exact (Nat.gcd_dvd_right r m).mul_left _
    exact (Nat.dvd_add_left (Nat.gcd_dvd_left r m)).mp hg

/-- **A signed repunit of prime length is not the prime times a square.** For `X ≡ 1 (mod 4)`,
an odd prime `p` and every `y`: `X ^ p + 1 ≠ (X + 1) * (p * y ^ 2)`. Arithmetic only (no odd
perfect number). No published source was checked; novelty not verified. The proof is
elementary: Jacobi symbols of signed repunits
and an odd quadratic nonresidue modulo `p`. -/
theorem alternating_sum_ne_prime_mul_sq {X p y : ℕ} (hX : X % 4 = 1) (hp : p.Prime)
    (hp2 : p ≠ 2) : X ^ p + 1 ≠ (X + 1) * (p * y ^ 2) := by
  intro hxy
  have := Fact.mk hp
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hA : signedRepunit X p = p * y ^ 2 :=
    Nat.eq_of_mul_eq_mul_left (Nat.succ_pos X) ((srj_mul hpo).trans hxy)
  have hy0 : y ≠ 0 := by
    rintro rfl
    have := (srj_facts hX hpo).1
    rw [hA] at this
    simp at this
  -- `p ∣ X + 1` by Fermat's little theorem
  have hX1 : (p : ℤ) ∣ (X : ℤ) + 1 := by
    have h := congrArg (fun t : ℕ => (t : ZMod p)) hxy
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, ZMod.natCast_self,
      zero_mul, mul_zero, ZMod.pow_card] at h
    have h' : (((X + 1 : ℕ) : ℤ) : ZMod p) = 0 := by push_cast; exact h
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h'
  -- an odd quadratic nonresidue `c`
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  obtain ⟨c, hco, hca⟩ : ∃ c : ℕ, Odd c ∧ (c : ZMod p) = a := by
    rcases Nat.even_or_odd a.val with he | ho
    · exact ⟨a.val + p, he.add_odd hpo, by simp⟩
    · exact ⟨a.val, ho, by simp⟩
  have hpc : ¬ p ∣ c := by
    intro hd
    rw [(ZMod.natCast_eq_zero_iff c p).mpr hd] at hca
    rw [← hca] at ha
    exact ha ⟨0, by simp⟩
  have hcop : Nat.Coprime c p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpc).symm
  have hJ := jacobiSym_signedRepunit hX hco hpo hcop
  rw [hA, jacobiSym.mul_right' _ hp.ne_zero (pow_ne_zero 2 hy0), jacobiSym.pow_right] at hJ
  -- `A_c ≡ c (mod p)`, so `J(A_c | p) = -1`
  have hAc : ((signedRepunit X c : ℤ) : ZMod p) = a := by
    have hd : (p : ℤ) ∣ (signedRepunit X c : ℤ) - c := hX1.trans (srj_facts hX hco).2.2.2
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
    push_cast at this
    rw [← hca]
    push_cast
    exact sub_eq_zero.mp this
  have hneg : jacobiSym (signedRepunit X c) p = -1 :=
    ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mpr (by rw [hAc]; exact ha)
  rw [hneg] at hJ
  rcases jacobiSym.trichotomy (signedRepunit X c) y with h | h | h <;> rw [h] at hJ <;>
    norm_num at hJ

end OddPerfect

#print axioms OddPerfect.signedRepunit_mul
#print axioms OddPerfect.jacobiSym_signedRepunit
#print axioms OddPerfect.alternating_sum_ne_prime_mul_sq
