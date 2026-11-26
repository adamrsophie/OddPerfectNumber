import OddPerfect.EulerIndexPairCofactor
import OddPerfect.Valuation

/-!
# Two prime Euler index: the exponent `v` of the sender row

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly the two prime factors
`r ≠ s`. The landed labeling `(t, u)` has `σ(t ^ e) = q u ^ v` and `σ(u ^ f) = t ^ j` with
`e = v_t(N)`, `f = v_u(N)`, `j` odd and `j < e`, and `e + 1` is a prime or the square of a
prime. This module pins down `v`.

* `sigma_row_split` (arithmetic): for primes `t`, `u`, `q` with `t, u` odd, `t ≠ u ≠ q`,
  `e` even, `σ(t ^ e) = q u ^ v` and `t ^ j ≡ 1 (mod u)` with `0 < j < e + 1`. Let `D` be the
  order of `t` modulo `u`. If `v ≥ 1`, then either `D = 1` and `u ∣ e + 1`, and lifting the
  exponent gives `v = v_u(e + 1)`, or `D > 1` and `D` divides both `e + 1` and `j`.
  * If `e + 1` is prime, then `v = 0`, or `v = 1`, `u = e + 1` and `t ≡ 1 (mod u)`.
  * If `e + 1 = P ^ 2` with `P` prime, then `v ≥ 1` (a pure row has prime length), and either
    `v = 2`, `u = P` and `t ≡ 1 (mod u)`, or `P ∣ j` and `D = P`.
* `eulerIndex_pair_split`: both alternatives for the labeling of `eulerIndex_pair_t_count`.

These are restricted results (special exponent 1, Euler index supported on exactly two
primes). They do not exclude this case. Their novelty has not been verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- **Sender row, the exponent of `u`.** Let `t`, `u`, `q` be primes, `t` and `u` odd, `t ≠ u`,
`u ≠ q`, `e` even, `σ(t ^ e) = q u ^ v`, and `t ^ j ≡ 1 (mod u)` for some `0 < j < e + 1`.
If `e + 1` is prime, then `v = 0`, or `v = 1`, `u = e + 1` and `t ≡ 1 (mod u)`. If
`e + 1 = P ^ 2` with `P` prime, then either `v = 2`, `u = P` and `t ≡ 1 (mod u)`, or `v > 0`,
`P ∣ j` and the order of `t` modulo `u` is `P`. Elementary; nothing new is claimed. -/
theorem sigma_row_split {t u q e v j : ℕ} (ht : t.Prime) (ht2 : t ≠ 2) (hu : u.Prime)
    (hu2 : u ≠ 2) (hq : q.Prime) (htu : t ≠ u) (huq : u ≠ q) (he : Even e)
    (hrow : σ 1 (t ^ e) = q * u ^ v) (hj : 0 < j) (hje : j < e + 1)
    (htj : (t : ZMod u) ^ j = 1) :
    ((e + 1).Prime → v = 0 ∨ (v = 1 ∧ u = e + 1 ∧ t % u = 1)) ∧
    (∀ P, P.Prime → e + 1 = P ^ 2 →
      (v = 2 ∧ u = P ∧ t % u = 1) ∨ (0 < v ∧ P ∣ j ∧ orderOf (t : ZMod u) = P)) := by
  have := Fact.mk hu
  have hval : padicValNat u (σ 1 (t ^ e)) = v := by
    rw [hrow, Nat.padicValNat_def, padicValNat.mul hq.ne_zero (pow_ne_zero _ hu.ne_zero),
      padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd
        (fun hd => huq ((Nat.prime_dvd_prime_iff_eq hu hq).mp hd)), zero_add]
  -- order 1: `t ≡ 1 (mod u)` and lifting the exponent
  have hone : orderOf (t : ZMod u) = 1 → t % u = 1 ∧ v = padicValNat u (e + 1) := by
    intro hD
    have hc : (t : ZMod u) = 1 := orderOf_eq_one_iff.mp hD
    have hmod : t % u = 1 := by
      have := (ZMod.natCast_eq_natCast_iff' t 1 u).mp (by rw [hc, Nat.cast_one])
      rwa [Nat.mod_eq_of_lt hu.one_lt] at this
    refine ⟨hmod, ?_⟩
    rw [← hval]
    exact padicValNat_sigma_prime_pow_of_dvd_pred ht hu hu2
      ((Nat.modEq_iff_dvd' ht.one_lt.le).mp
        (by rw [Nat.ModEq, hmod, Nat.mod_eq_of_lt hu.one_lt]))
  have hdiv : 0 < v → (orderOf (t : ZMod u) = 1 ∧ u ∣ e + 1) ∨
      (orderOf (t : ZMod u) ≠ 1 ∧ orderOf (t : ZMod u) ∣ e + 1) := by
    intro hv
    have hud : u ∣ σ 1 (t ^ e) := by
      rw [hrow]; exact dvd_mul_of_dvd_right (dvd_pow_self u hv.ne') q
    rw [dvd_sigma_prime_pow_iff ht hu htu] at hud
    split_ifs at hud with hD
    · exact Or.inl ⟨hD, hud⟩
    · exact Or.inr ⟨hD, hud⟩
  have hDj : orderOf (t : ZMod u) ∣ j := orderOf_dvd_of_pow_eq_one htj
  refine ⟨fun hp => ?_, fun P hP hPe => ?_⟩
  · rcases Nat.eq_zero_or_pos v with hv | hv
    · exact Or.inl hv
    right
    rcases hdiv hv with ⟨hD, hud⟩ | ⟨hD, hd⟩
    · have hue : u = e + 1 := (Nat.prime_dvd_prime_iff_eq hu hp).mp hud
      obtain ⟨hmod, hv'⟩ := hone hD
      refine ⟨?_, hue, hmod⟩
      rw [hv', ← hue, Nat.padicValNat_def, padicValNat_self]
    · rcases (Nat.dvd_prime hp).mp hd with h1 | h1
      · exact absurd h1 hD
      · have := Nat.le_of_dvd hj (h1 ▸ hDj); omega
  · have hP4 : 2 * 2 ≤ P ^ 2 := by rw [sq]; exact Nat.mul_le_mul hP.two_le hP.two_le
    have hv : 0 < v := by
      rcases Nat.eq_zero_or_pos v with hv | hv
      · exfalso
        have hp : (e + 1).Prime := prime_succ_of_sigma_prime_pow_eq_prime_pow ht ht2 he
          (by omega) hq (by rw [hrow, hv, pow_zero, mul_one, pow_one])
        rw [hPe, sq] at hp
        exact Nat.not_prime_mul hP.ne_one hP.ne_one hp
      · exact hv
    rcases hdiv hv with ⟨hD, hud⟩ | ⟨hD, hd⟩
    · left
      have huP : u = P :=
        (Nat.prime_dvd_prime_iff_eq hu hP).mp (hu.dvd_of_dvd_pow (hPe ▸ hud))
      obtain ⟨hmod, hv'⟩ := hone hD
      refine ⟨?_, huP, hmod⟩
      rw [hv', hPe, ← huP, Nat.padicValNat_def, padicValNat.prime_pow]
    · right
      rw [hPe] at hd
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hP).mp hd
      interval_cases k
      · exact absurd (by simpa using hk') hD
      · rw [pow_one] at hk'
        exact ⟨hv, hk' ▸ hDj, hk'⟩
      · have := Nat.le_of_dvd hj (hk' ▸ hDj); omega

variable {N q m r s : ℕ}

/-- **Two prime index, the exponent `v`.** Let `N = q m ^ 2` be an odd perfect number with
special prime `q` of exponent 1, `q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has
exactly the two prime factors `r ≠ s`. For the labeling `(t, u)` of `eulerIndex_pair_t_count`,
with `e = v_t(N)`, `σ(t ^ e) = q u ^ v`, `σ(u ^ v_u(N)) = t ^ j`, `j` odd and `j < e`: if
`e + 1` is prime, then `v = 0` (so `σ(t ^ e) = q`), or `v = 1`, `u = e + 1` and
`t ≡ 1 (mod u)`; if `e + 1 = P ^ 2` with `P` prime, then either `v = 2`, `u = P` and
`t ≡ 1 (mod u)`, or `v > 0`, `P ∣ j` and the order of `t` modulo `u` is `P`. This is a
restricted result (special exponent 1, index supported on exactly two primes); it does not
exclude this case. Its novelty has not been verified. -/
theorem eulerIndex_pair_split (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧ ∃ v j,
      σ 1 (t ^ N.factorization t) = q * u ^ v ∧ 0 < j ∧ Odd j ∧
      σ 1 (u ^ N.factorization u) = t ^ j ∧ j < N.factorization t ∧
      ((N.factorization t + 1).Prime →
        (v = 0 ∧ σ 1 (t ^ N.factorization t) = q) ∨
          (v = 1 ∧ u = N.factorization t + 1 ∧ t % u = 1)) ∧
      (∀ P, P.Prime → N.factorization t + 1 = P ^ 2 →
        (v = 2 ∧ u = P ∧ t % u = 1) ∨ (0 < v ∧ P ∣ j ∧ orderOf (t : ZMod u) = P)) := by
  obtain ⟨t, u, htu, hne, ⟨v, hA⟩, -, -, j, hj, hjo, hB, hcount, hAodd, -⟩ :=
    eulerIndex_pair_t_count h hq hN hqm hr hs hrs hJ
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have hJm := eulerIndex_dvd_sq h hq hN1 hqm
  have hfacts : ∀ p ∈ ({t, u} : Finset ℕ), p.Prime ∧ p ≠ 2 ∧ p ≠ q := by
    intro p hp
    rw [htu, ← hJ] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpJ := Nat.dvd_of_mem_primeFactors hp
    have hpm : p ∣ m := hpp.dvd_of_dvd_pow (hpJ.trans hJm)
    refine ⟨hpp, ?_, ?_⟩
    · rintro rfl
      exact (Nat.not_even_iff_odd.mpr (odd_eulerIndex h hq hN1 hqm)) (even_iff_two_dvd.mpr hpJ)
    · rintro rfl; exact hqm hpm
  obtain ⟨ht, ht2, -⟩ := hfacts t (by simp)
  obtain ⟨hu, hu2, huq⟩ := hfacts u (by simp)
  set A := ∑ p ∈ N.primeFactors \ {q, r, s}, (σ 1 (p ^ N.factorization p)).factorization t
  have hje : j < N.factorization t := by obtain ⟨c, hc⟩ := hAodd; omega
  have he : Even (N.factorization t) := by
    obtain ⟨c, hc⟩ := hAodd
    obtain ⟨i, hi⟩ := hjo
    exact ⟨i + c + 1, by omega⟩
  have htj : (t : ZMod u) ^ j = 1 := by
    have h1 : ((σ 1 (u ^ N.factorization u) : ℕ) : ZMod u) = 1 := by
      rw [sigma_one_apply_prime_pow hu, Finset.sum_range_succ']
      push_cast
      simp
    rw [hB] at h1
    exact_mod_cast h1
  obtain ⟨h1, h2⟩ := sigma_row_split ht ht2 hu hu2 hq hne huq he hA hj (by omega) htj
  refine ⟨t, u, htu, hne, v, j, hA, hj, hjo, hB, hje, fun hp => ?_, h2⟩
  rcases h1 hp with hv | hv
  · left
    exact ⟨hv, by rw [hA, hv, pow_zero, mul_one]⟩
  · exact Or.inr hv

end OddPerfect

#print axioms OddPerfect.sigma_row_split
#print axioms OddPerfect.eulerIndex_pair_split
