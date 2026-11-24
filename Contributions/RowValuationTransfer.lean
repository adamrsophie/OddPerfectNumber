import Mathlib.NumberTheory.Multiplicity
import Mathlib.FieldTheory.Finite.Basic
import OddPerfect.Steps

/-!
Proof of the step `RowValuationTransfer`. Write `m = c + 1`, so that
`(p - 1) * σ(p ^ c) = p ^ m - 1`. If `p ≡ 1 (mod q)`, lifting the exponent gives
`v_q(p ^ m - 1) = v_q(p - 1) + v_q(m)`. Otherwise `v_q(p - 1) = 0`, and lifting the exponent
twice through `p ^ ((q - 1) * k)` gives `v_q(p ^ k - 1) = v_q(p ^ (q - 1) - 1) + v_q(k)` for
every `k ≥ 1` with `q ∣ p ^ k - 1`. Since `p ^ y = σ(q ^ x) = 1 + q * (1 + q * T)`, the case
`k = y` forces `v_q(p ^ (q - 1) - 1) = 1`, and the case `k = m` gives the claim.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect.Proofs

private theorem geom_two (q n : ℕ) :
    ∑ k ∈ Finset.range (n + 2), q ^ k =
      1 + q * (1 + q * ∑ k ∈ Finset.range n, q ^ k) := by
  induction n with
  | zero => simp [add_comm]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

theorem RowValuationTransfer : OddPerfect.Steps.RowValuationTransfer := by
  intro p q x y c hp hq hq2 hx hrow hdvd
  have hqo : Odd q := hq.odd_of_ne_two hq2
  have := Fact.mk hq
  have hp1 := hp.one_lt
  have hq1 := hq.one_lt
  have hgeom : (p - 1) * σ 1 (p ^ c) = p ^ (c + 1) - 1 := by
    have h := geom_sum_mul_add (p - 1) (c + 1)
    rw [Nat.sub_add_cancel hp.one_le] at h
    rw [sigma_one_apply_prime_pow hp, mul_comm]
    omega
  have hpm : 1 < p ^ (c + 1) := Nat.one_lt_pow (by omega) hp1
  have hS0 : σ 1 (p ^ c) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hgeom
    omega
  have hmulv : padicValNat q (p ^ (c + 1) - 1) =
      padicValNat q (p - 1) + padicValNat q (σ 1 (p ^ c)) := by
    rw [← hgeom, padicValNat.mul (by omega) hS0]
  have hmod : p % q = 1 ↔ q ∣ p - 1 := by
    rw [← Nat.modEq_iff_dvd' hp.one_le, Nat.ModEq, Nat.mod_eq_of_lt hq1]
    exact eq_comm
  constructor
  · intro h
    have hd : q ∣ p - 1 := hmod.mp h
    have hnd : ¬ q ∣ p := by
      intro hd'
      obtain ⟨k, rfl⟩ := hd'
      simp at h
    have hl := padicValNat.pow_sub_pow (p := q) (x := p) (y := 1) hqo hp1 hd hnd
      (n := c + 1) (by omega)
    simp only [one_pow] at hl
    omega
  · intro h
    have hv1 : padicValNat q (p - 1) = 0 :=
      padicValNat.eq_zero_of_not_dvd (fun hd => h (hmod.mpr hd))
    obtain ⟨n, rfl⟩ : ∃ n, x = n + 1 := ⟨x - 1, by omega⟩
    rw [sigma_one_apply_prime_pow hq, geom_two] at hrow
    set T := ∑ k ∈ Finset.range n, q ^ k
    have hpos : 0 < q * (1 + q * T) := by positivity
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hrow
      omega
    have hq_one : ¬ q ∣ 1 := fun h1 => hq1.ne' (Nat.dvd_one.mp h1)
    have hnp : ¬ q ∣ p := by
      intro hd
      have h2 : q ∣ p ^ y := dvd_pow hd hy0
      rw [← hrow] at h2
      exact hq_one ((Nat.dvd_add_left (dvd_mul_right q _)).mp h2)
    have hpy1 : p ^ y - 1 = q * (1 + q * T) := by omega
    have hvy : padicValNat q (p ^ y - 1) = 1 := by
      rw [hpy1, padicValNat.mul hq.ne_zero (by positivity), padicValNat.self hq1,
        padicValNat.eq_zero_of_not_dvd]
      intro hd
      exact hq_one ((Nat.dvd_add_left (dvd_mul_right q T)).mp hd)
    have hpq : 1 < p ^ (q - 1) := Nat.one_lt_pow (by omega) hp1
    have hferm : q ∣ p ^ (q - 1) - 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hpq.le, Nat.cast_pow, Nat.cast_one,
        sub_eq_zero]
      apply ZMod.pow_card_sub_one_eq_one
      rwa [Ne, ZMod.natCast_eq_zero_iff]
    have hqq : padicValNat q (q - 1) = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      omega
    have key : ∀ k, k ≠ 0 → q ∣ p ^ k - 1 →
        padicValNat q (p ^ k - 1) = padicValNat q (p ^ (q - 1) - 1) + padicValNat q k := by
      intro k hk hkd
      have h1 := padicValNat.pow_sub_pow (p := q) (x := p ^ (q - 1)) (y := 1) hqo hpq hferm
        (fun hh => hnp (hq.dvd_of_dvd_pow hh)) (n := k) hk
      have h2 := padicValNat.pow_sub_pow (p := q) (x := p ^ k) (y := 1) hqo
        (Nat.one_lt_pow hk hp1) hkd (fun hh => hnp (hq.dvd_of_dvd_pow hh))
        (n := q - 1) (by omega)
      simp only [one_pow, ← pow_mul] at h1 h2
      rw [mul_comm k] at h2
      omega
    have hm : q ∣ p ^ (c + 1) - 1 := hgeom ▸ dvd_mul_of_dvd_right hdvd _
    have hqy : q ∣ p ^ y - 1 := hpy1 ▸ dvd_mul_right _ _
    have hk1 := key y hy0 hqy
    have hk2 := key (c + 1) (by omega) hm
    have hge : 1 ≤ padicValNat q (p ^ (q - 1) - 1) :=
      one_le_padicValNat_of_dvd (by omega) hferm
    omega

end OddPerfect.Proofs
