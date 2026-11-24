import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Multiplicity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# The digit congruence for a square whose divisor sum is a prime power

Let `p` be a prime, `e ≥ 1`, `t` odd, `σ(t ^ 2) = p ^ e` and `2 t ^ 2 = 1 + σ(p ^ e)`.

* `prime_index_of_sigma_prime_pow`: if `r` and `p` are primes, `p` odd, `g ≥ 1`, `w ≥ 1` and
  `σ(r ^ g) = p ^ w`, then `g + 1` is prime, `g + 1 ∣ p - 1` and
  `r ^ (g + 1) = 1 + (r - 1) p ^ w`.
* `square_cycle_digit`: in the setting above, let `I` be the set of primes `r ∣ t` with
  `σ(r ^ (2 v_r(t))) = p` and `ℓ_r = 2 v_r(t) + 1`. Then `p` divides
  `2 ∑_{r ∈ I} (∏_{s ∈ I, s ≠ r} ℓ_s) (ℓ_r - 1) (r - 1) - ∏_{r ∈ I} ℓ_r`.
* `square_cycle_false_of_size`: the setting above is impossible, under the explicit hypothesis
  `hsize` (a size bound for rows with a common value `p`). This theorem is conditional on that
  hypothesis, which is not proved here.

Nothing here decides the odd perfect number conjecture. Novelty of these statements was not
verified.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The row identity `S(n) (r - 1) + 1 = r ^ n` for the geometric sum `S(n)`. -/
private theorem scd_geom_row (r n : ℕ) (hr : 1 ≤ r) :
    (∑ i ∈ range n, r ^ i) * (r - 1) + 1 = r ^ n := by
  have := geom_sum_mul_add (r - 1) n
  rwa [Nat.sub_add_cancel hr] at this

/-- `S(a b) = S(a) * ∑ i < b, (r ^ a) ^ i`. -/
private theorem scd_geom_mul (r a b : ℕ) :
    ∑ i ∈ range (a * b), r ^ i = (∑ i ∈ range a, r ^ i) * ∑ i ∈ range b, (r ^ a) ^ i := by
  induction b with
  | zero => simp
  | succ b ih =>
    have h2 : ∑ x ∈ range a, r ^ (a * b + x) = (∑ i ∈ range a, r ^ i) * (r ^ a) ^ b := by
      rw [sum_mul]
      exact sum_congr rfl fun i _ => by rw [pow_add, pow_mul]; ring
    rw [mul_add_one, sum_range_add, ih, sum_range_succ, mul_add, h2]

/-- A geometric sum with base at least `2` and at least two terms exceeds its length. -/
private theorem scd_lt_geom {x n : ℕ} (hx : 2 ≤ x) (hn : 1 ≤ n) :
    n + 1 < ∑ i ∈ range (n + 1), x ^ i := by
  rw [sum_range_succ]
  have h1 : n ≤ ∑ i ∈ range n, x ^ i := by
    have := sum_le_sum (s := range n) (f := fun _ => 1) (g := fun i => x ^ i)
      (fun i _ => Nat.pos_of_ne_zero (pow_ne_zero _ (by omega)))
    simpa using this
  have h2 : 2 ≤ x ^ n := le_trans hx (le_self_pow (by omega) (by omega))
  omega

/-- A divisor larger than `1` of a prime power `p ^ w` is divisible by `p`. -/
private theorem scd_dvd_of_dvd_pow {p w x : ℕ} (hp : p.Prime) (h : x ∣ p ^ w) (hx : 1 < x) :
    p ∣ x := by
  obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 h
  rcases k with _ | k
  · simp at hx
  · exact dvd_pow_self p (Nat.succ_ne_zero k)

/-- If `p ∣ S(n)` then `r ^ n = 1` in `ZMod p`. -/
private theorem scd_pow_eq_one {p r n : ℕ} (hr : 1 ≤ r) (h : p ∣ ∑ i ∈ range n, r ^ i) :
    (r : ZMod p) ^ n = 1 := by
  have h1 := congrArg (Nat.cast : ℕ → ZMod p) (scd_geom_row r n hr)
  rw [Nat.cast_add, Nat.cast_mul, (ZMod.natCast_eq_zero_iff _ _).2 h, zero_mul, zero_add,
    Nat.cast_one, Nat.cast_pow] at h1
  exact h1.symm

/-- **Prime index lemma.** If `σ(r ^ g) = p ^ w` with `r`, `p` prime, `p` odd, `g ≥ 1` and
`w ≥ 1`, then `g + 1` is prime, `g + 1 ∣ p - 1` and `r ^ (g + 1) = 1 + (r - 1) p ^ w`. -/
theorem prime_index_of_sigma_prime_pow {r p g w : ℕ} (hr : r.Prime) (hp : p.Prime) (hp2 : p ≠ 2)
    (hg : 1 ≤ g) (_hw : 1 ≤ w) (h : σ 1 (r ^ g) = p ^ w) :
    (g + 1).Prime ∧ g + 1 ∣ p - 1 ∧ r ^ (g + 1) = 1 + (r - 1) * p ^ w := by
  have := Fact.mk hp
  have hr1 : 1 ≤ r := hr.one_lt.le
  have hS : ∑ i ∈ range (g + 1), r ^ i = p ^ w := by rw [← sigma_one_apply_prime_pow hr, h]
  have hid : r ^ (g + 1) = 1 + (r - 1) * p ^ w := by
    rw [← scd_geom_row r (g + 1) hr1, hS]; ring
  have hdivS : ∀ a, a ∣ g + 1 → ∑ i ∈ range a, r ^ i ∣ p ^ w := by
    rintro a ⟨b, hb⟩
    rw [← hS, hb, scd_geom_mul]
    exact dvd_mul_right _ _
  have hkey : ∀ a, a ∣ g + 1 → 2 ≤ a → (r : ZMod p) ^ a = 1 := by
    intro a ha ha2
    apply scd_pow_eq_one hr1
    apply scd_dvd_of_dvd_pow hp (hdivS a ha)
    have := scd_lt_geom (x := r) (n := a - 1) hr.two_le (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ a)] at this
    omega
  -- (a) `r` is not `1` modulo `p`, by lifting the exponent
  have hne1 : (r : ZMod p) ≠ 1 := by
    intro h1
    have hpr : p ∣ r - 1 := by
      have : ((r - 1 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_sub hr1, h1]; simp
      exact (ZMod.natCast_eq_zero_iff _ _).1 this
    have hpr' : ¬ p ∣ r := by
      intro hd
      have h3 := Nat.dvd_sub hd hpr
      rw [show r - (r - 1) = 1 by omega] at h3
      exact hp.not_dvd_one h3
    have hlte := padicValNat.pow_sub_pow (hp.odd_of_ne_two hp2) hr.one_lt (by simpa using hpr)
      hpr' (n := g + 1) (by omega)
    have hrow := scd_geom_row r (g + 1) hr1
    rw [hS] at hrow
    have hsub : r ^ (g + 1) - 1 ^ (g + 1) = p ^ w * (r - 1) := by
      rw [one_pow, ← hrow, Nat.add_sub_cancel]
    rw [hsub, padicValNat.mul (pow_ne_zero _ hp.ne_zero)
      (show r - 1 ≠ 0 by have := hr.two_le; omega),
      padicValNat.prime_pow] at hlte
    have hv : w = padicValNat p (g + 1) := by omega
    have hdvd : p ^ w ∣ g + 1 := by rw [hv]; exact pow_padicValNat_dvd
    have hle := Nat.le_of_dvd (by omega) hdvd
    have hlt := scd_lt_geom (x := r) (n := g) hr.two_le hg
    omega
  -- (b) every prime divisor of `g + 1` is the order of `r` modulo `p`
  have horder : ∀ q, q.Prime → q ∣ g + 1 → orderOf (r : ZMod p) = q := by
    intro q hq hqd
    have := Fact.mk hq
    exact orderOf_eq_prime (hkey q hqd hq.two_le) hne1
  obtain ⟨ℓ, hℓ, hℓd⟩ : ∃ ℓ, ℓ.Prime ∧ ℓ ∣ g + 1 :=
    ⟨_, Nat.minFac_prime (show g + 1 ≠ 1 by omega), Nat.minFac_dvd _⟩
  have hℓ2 := hℓ.two_le
  have hp2' := hp.two_le
  have hrne0 : (r : ZMod p) ≠ 0 := by
    intro h0
    have := hkey _ hℓd hℓ2
    rw [h0, zero_pow hℓ.ne_zero] at this
    exact zero_ne_one this
  have hℓp : ℓ ∣ p - 1 := by
    rw [← horder _ hℓ hℓd]; exact ZMod.orderOf_dvd_card_sub_one hrne0
  -- (c) `g + 1` is squarefree, hence equal to its prime factor `ℓ`
  have hgl : g + 1 = ℓ := by
    obtain ⟨m, hm⟩ := hℓd
    have hm1 : m = 1 := by
      by_contra hm1
      have hq : m.minFac.Prime := Nat.minFac_prime hm1
      have hqd : m.minFac ∣ g + 1 := (Nat.minFac_dvd m).trans (Dvd.intro_left ℓ hm.symm)
      have hql : m.minFac = ℓ := by
        rw [← horder _ hq hqd, ← horder _ hℓ ⟨m, hm⟩]
      have hlm : ℓ ∣ m := by rw [← hql]; exact Nat.minFac_dvd m
      have hll : ℓ * ℓ ∣ g + 1 := by
        obtain ⟨c, hc⟩ := hlm
        exact ⟨c, by rw [mul_assoc, ← hc]; exact hm⟩
      have hT : ∑ i ∈ range ℓ, (r ^ ℓ) ^ i ∣ p ^ w := by
        have := hdivS _ hll
        rw [scd_geom_mul] at this
        exact (dvd_mul_left _ _).trans this
      have hT1 : 1 < ∑ i ∈ range ℓ, (r ^ ℓ) ^ i := by
        have h2 : 2 ≤ r ^ ℓ := le_trans hr.two_le (le_self_pow hr1 hℓ.ne_zero)
        have := scd_lt_geom (x := r ^ ℓ) (n := ℓ - 1) h2 (by omega)
        rw [Nat.sub_add_cancel (by omega : 1 ≤ ℓ)] at this
        omega
      have hpT := scd_dvd_of_dvd_pow hp hT hT1
      have hcast : ((∑ i ∈ range ℓ, (r ^ ℓ) ^ i : ℕ) : ZMod p) = ℓ := by
        push_cast
        rw [hkey ℓ ⟨m, hm⟩ hℓ2]
        simp
      rw [(ZMod.natCast_eq_zero_iff _ _).2 hpT] at hcast
      have hpl : p ∣ ℓ := (ZMod.natCast_eq_zero_iff _ _).1 hcast.symm
      have h1 := Nat.le_of_dvd hℓ.pos hpl
      have h2 := Nat.le_of_dvd (by omega) hℓp
      omega
    rw [hm1, mul_one] at hm
    exact hm
  refine ⟨?_, ?_, hid⟩
  · rw [hgl]; exact hℓ
  · rw [hgl]; exact hℓp

/-- A prime component of `n` whose divisor sum is a power of `p` has weight at least one. -/
private theorem scd_row_prime_pow {n p e r : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (hσ : σ 1 n = p ^ e) (hr : r ∈ n.primeFactors) :
    ∃ w, 1 ≤ w ∧ σ 1 (r ^ n.factorization r) = p ^ w := by
  have hfac : σ 1 n = ∏ s ∈ n.primeFactors, σ 1 (s ^ n.factorization s) := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ hn, Finsupp.prod,
      Nat.support_factorization]
  have hd : σ 1 (r ^ n.factorization r) ∣ p ^ e := by
    rw [← hσ, hfac]; exact dvd_prod_of_mem _ hr
  obtain ⟨w, -, hw⟩ := (Nat.dvd_prime_pow hp).1 hd
  have hr' := Nat.prime_of_mem_primeFactors hr
  have ha : 1 ≤ n.factorization r :=
    hr'.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hr)
  refine ⟨w, ?_, hw⟩
  rcases Nat.eq_zero_or_pos w with h0 | h0
  · exfalso
    have := scd_lt_geom (x := r) (n := n.factorization r) hr'.two_le ha
    rw [← sigma_one_apply_prime_pow hr', hw, h0, pow_zero] at this
    omega
  · exact h0

section Eps

variable {R : Type*} [CommRing R] {ε : R}

private theorem scd_one_add_eps_pow (hε : ε ^ 2 = 0) (c : R) (n : ℕ) :
    (1 + c * ε) ^ n = 1 + n * c * ε := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]; push_cast; linear_combination (n * c ^ 2) * hε

private theorem scd_prod_one_add_eps (hε : ε ^ 2 = 0) (s : Finset ℕ) (a : ℕ → R) :
    ∏ r ∈ s, (1 + a r * ε) = 1 + (∑ r ∈ s, a r) * ε := by
  refine Finset.induction_on s (by simp) ?_
  intro x s hx ih
  rw [prod_insert hx, sum_insert hx, ih]
  linear_combination (a x * ∑ r ∈ s, a r) * hε

private theorem scd_two_add_eps_pow (hε : ε ^ 2 = 0) (n : ℕ) :
    2 * (2 + ε) ^ n = 2 ^ (n + 1) + n * 2 ^ n * ε := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih]; push_cast; linear_combination (n * 2 ^ n) * hε

end Eps

/-- The weight one digit term `(ℓ - 1) ((p - 1) / ℓ) (r - 1)` with `ℓ = 2 v_r(t) + 1`. -/
private def scdTerm (p t r : ℕ) : ℕ :=
  2 * t.factorization r * ((p - 1) / (2 * t.factorization r + 1)) * (r - 1)

/-- **The digit congruence.** If `p` is prime, `e ≥ 1`, `t` is odd, `σ(t ^ 2) = p ^ e` and
`2 t ^ 2 = 1 + σ(p ^ e)`, let `I` be the set of primes `r ∣ t` with `σ(r ^ (2 v_r(t))) = p` and
`ℓ_r = 2 v_r(t) + 1`. Then `p` divides
`2 ∑_{r ∈ I} (∏_{s ∈ I, s ≠ r} ℓ_s) (ℓ_r - 1) (r - 1) - ∏_{r ∈ I} ℓ_r`. -/
theorem square_cycle_digit {p e t : ℕ} (hp : p.Prime) (he : 1 ≤ e) (ht : Odd t)
    (hσ : σ 1 (t ^ 2) = p ^ e) (hc : 2 * t ^ 2 = 1 + σ 1 (p ^ e)) :
    ∃ I : Finset ℕ,
      (∀ r ∈ I, r.Prime ∧ r ≠ 2 ∧ (2 * t.factorization r + 1).Prime ∧
        ∑ i ∈ Finset.range (2 * t.factorization r + 1), r ^ i = p) ∧
      (p : ℤ) ∣ 2 * ∑ r ∈ I, (∏ s ∈ I.erase r, ((2 * t.factorization s + 1 : ℕ) : ℤ)) *
          ((2 * t.factorization r : ℕ) : ℤ) * ((r : ℤ) - 1) -
        ∏ r ∈ I, ((2 * t.factorization r + 1 : ℕ) : ℤ) := by
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have ht20 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
  -- Step 0: `p` is odd
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 := scd_geom_row 2 (e + 1) (by norm_num)
    rw [← sigma_one_apply_prime_pow Nat.prime_two, show (2 : ℕ) - 1 = 1 from rfl, mul_one,
      pow_succ] at h2
    have h3 : t ^ 2 = 2 ^ e := by omega
    have h4 : 2 ∣ t ^ 2 := h3 ▸ dvd_pow_self 2 (by omega)
    exact (Nat.not_even_iff_odd.2 (ht.pow (n := 2))) (even_iff_two_dvd.2 h4)
  have := Fact.mk hp
  -- Step 1 and Step 2: the rows
  have hrow : ∀ r ∈ t.primeFactors,
      ∃ w, 1 ≤ w ∧ σ 1 (r ^ (2 * t.factorization r)) = p ^ w := by
    intro r hr
    have hr2 : r ∈ (t ^ 2).primeFactors := by rwa [Nat.primeFactors_pow t two_ne_zero]
    have := scd_row_prime_pow hp ht20 hσ hr2
    rwa [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at this
  have hdata : ∀ r ∈ t.primeFactors, ∃ w, 1 ≤ w ∧ σ 1 (r ^ (2 * t.factorization r)) = p ^ w ∧
      (2 * t.factorization r + 1).Prime ∧ 2 * t.factorization r + 1 ∣ p - 1 ∧
      r ^ (2 * t.factorization r + 1) = 1 + (r - 1) * p ^ w := by
    intro r hr
    obtain ⟨w, hw1, hw⟩ := hrow r hr
    have hr' := Nat.prime_of_mem_primeFactors hr
    have hv : 1 ≤ t.factorization r :=
      hr'.factorization_pos_of_dvd ht0 (Nat.dvd_of_mem_primeFactors hr)
    exact ⟨w, hw1, hw, prime_index_of_sigma_prime_pow hr' hp hp2 (by omega) hw1 hw⟩
  set I := t.primeFactors.filter
    (fun r => ∑ i ∈ Finset.range (2 * t.factorization r + 1), r ^ i = p) with hI
  refine ⟨I, ?_, ?_⟩
  · intro r hrI
    obtain ⟨hr, hP⟩ := mem_filter.1 hrI
    obtain ⟨w, -, -, hℓ, -⟩ := hdata r hr
    refine ⟨Nat.prime_of_mem_primeFactors hr, ?_, hℓ, hP⟩
    rintro rfl
    exact (Nat.not_even_iff_odd.2 ht) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hr))
  -- Step 3: computation modulo `p ^ 2`
  have hε : ((p : ZMod (p ^ 2))) ^ 2 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hrowR : ∀ r ∈ t.primeFactors,
      ((r : ZMod (p ^ 2))) ^ (2 * t.factorization r * (p - 1)) =
        if ∑ i ∈ Finset.range (2 * t.factorization r + 1), r ^ i = p then
          1 + ((scdTerm p t r : ℕ) : ZMod (p ^ 2)) * p else 1 := by
    intro r hr
    obtain ⟨w, hw1, hσw, -, hℓd, hid⟩ := hdata r hr
    obtain ⟨k, hk⟩ := hℓd
    have hkdiv : (p - 1) / (2 * t.factorization r + 1) = k := by
      rw [hk, Nat.mul_div_cancel_left _ (by omega)]
    have hexp : 2 * t.factorization r * (p - 1) =
        (2 * t.factorization r + 1) * (2 * t.factorization r * k) := by rw [hk]; ring
    rw [hexp, pow_mul, ← Nat.cast_pow, hid]
    have hS : ∑ i ∈ range (2 * t.factorization r + 1), r ^ i = p ^ w := by
      rw [← sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hr), hσw]
    rw [hS]
    by_cases hw : w = 1
    · subst hw
      rw [if_pos (pow_one p), scdTerm, hkdiv, pow_one]
      push_cast
      rw [scd_one_add_eps_pow hε]
      push_cast
      ring
    · rw [if_neg (fun h => hw (Nat.pow_right_injective hp.two_le (h.trans (pow_one p).symm)))]
      have h0 : ((p : ZMod (p ^ 2))) ^ w = 0 := by
        obtain ⟨u, rfl⟩ : ∃ u, w = u + 2 := ⟨w - 2, by omega⟩
        rw [pow_add, hε, mul_zero]
      push_cast
      rw [h0]
      simp
  have ht2 : t ^ 2 = ∏ r ∈ t.primeFactors, r ^ (2 * t.factorization r) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self ht0]
    rw [Finsupp.prod, Nat.support_factorization, ← prod_pow]
    exact prod_congr rfl fun r _ => by ring
  have hX : ((t : ZMod (p ^ 2)) ^ 2) ^ (p - 1) =
      1 + (∑ r ∈ I, ((scdTerm p t r : ℕ) : ZMod (p ^ 2))) * p := by
    have h1 : ((t : ZMod (p ^ 2)) ^ 2) ^ (p - 1) =
        ∏ r ∈ t.primeFactors, (r : ZMod (p ^ 2)) ^ (2 * t.factorization r * (p - 1)) := by
      rw [← Nat.cast_pow, ht2]
      push_cast
      rw [← prod_pow]
      exact prod_congr rfl fun r _ => (pow_mul _ _ _).symm
    rw [h1, prod_congr rfl hrowR, ← prod_filter]
    exact scd_prod_one_add_eps hε _ _
  have hY : (2 : ZMod (p ^ 2)) * (t : ZMod (p ^ 2)) ^ 2 = 2 + p := by
    have h := congrArg (Nat.cast : ℕ → ZMod (p ^ 2)) hc
    rw [sigma_one_apply_prime_pow hp] at h
    push_cast at h
    rw [h]
    obtain ⟨u, rfl⟩ : ∃ u, e = u + 1 := ⟨e - 1, by omega⟩
    have hz : ∑ i ∈ range u, (p : ZMod (p ^ 2)) ^ (i + 1 + 1) = 0 :=
      sum_eq_zero fun i _ => by rw [show i + 1 + 1 = i + 2 by ring, pow_add, hε, mul_zero]
    rw [sum_range_succ', sum_range_succ', hz]
    simp only [zero_add, pow_one, pow_zero]
    ring
  have h1 := scd_two_add_eps_pow hε (p - 1)
  rw [← hY, mul_pow, hX] at h1
  have key : (((2 ^ (p - 1) * (2 * ((∑ r ∈ I, scdTerm p t r : ℕ) : ℤ) - ((p - 1 : ℕ) : ℤ)) *
      p : ℤ)) : ZMod (p ^ 2)) = 0 := by
    push_cast at h1 ⊢
    linear_combination h1
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 key
  rw [Nat.cast_pow, pow_two] at hd
  have hd2 := (mul_dvd_mul_iff_right (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0)).1 hd
  have hpZ := Nat.prime_iff_prime_int.mp hp
  have hd3 : (p : ℤ) ∣ 2 * ((∑ r ∈ I, scdTerm p t r : ℕ) : ℤ) - ((p - 1 : ℕ) : ℤ) := by
    rcases hpZ.dvd_or_dvd hd2 with h | h
    · exfalso
      have h2 : (p : ℤ) ∣ 2 := hpZ.dvd_of_dvd_pow h
      have h3 : p ∣ 2 := by exact_mod_cast h2
      have := Nat.le_of_dvd (by norm_num) h3
      have := hp.two_le
      omega
    · exact h
  have h2A : (p : ℤ) ∣ 2 * ((∑ r ∈ I, scdTerm p t r : ℕ) : ℤ) + 1 := by
    have h4 : 2 * ((∑ r ∈ I, scdTerm p t r : ℕ) : ℤ) + 1 =
        (2 * ((∑ r ∈ I, scdTerm p t r : ℕ) : ℤ) - ((p - 1 : ℕ) : ℤ)) + p := by
      rw [Nat.cast_sub hp.one_le, Nat.cast_one]; ring
    rw [h4]; exact dvd_add hd3 dvd_rfl
  -- the exact identity that turns `p ∣ 2 A + 1` into the stated divisibility
  have hterm : ∀ r ∈ I, (∏ s ∈ I, ((2 * t.factorization s + 1 : ℕ) : ℤ)) *
        ((scdTerm p t r : ℕ) : ℤ) =
      (p : ℤ) * ((∏ s ∈ I.erase r, ((2 * t.factorization s + 1 : ℕ) : ℤ)) *
        ((2 * t.factorization r : ℕ) : ℤ) * ((r : ℤ) - 1)) -
      (∏ s ∈ I.erase r, ((2 * t.factorization s + 1 : ℕ) : ℤ)) *
        ((2 * t.factorization r : ℕ) : ℤ) * ((r : ℤ) - 1) := by
    intro r hrI
    have hr := (mem_filter.1 hrI).1
    obtain ⟨-, -, -, -, hℓd, -⟩ := hdata r hr
    have hr1 : 1 ≤ r := (Nat.prime_of_mem_primeFactors hr).one_lt.le
    have hDZ : (∏ s ∈ I, ((2 * t.factorization s + 1 : ℕ) : ℤ)) =
        ((2 * t.factorization r + 1 : ℕ) : ℤ) *
          ∏ s ∈ I.erase r, ((2 * t.factorization s + 1 : ℕ) : ℤ) :=
      (mul_prod_erase I (fun s => ((2 * t.factorization s + 1 : ℕ) : ℤ)) hrI).symm
    have hkZ : (((p - 1) / (2 * t.factorization r + 1) : ℕ) : ℤ) *
        ((2 * t.factorization r + 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hℓd, Nat.cast_sub hp.one_le, Nat.cast_one]
    have hcast : ((scdTerm p t r : ℕ) : ℤ) = ((2 * t.factorization r : ℕ) : ℤ) *
        (((p - 1) / (2 * t.factorization r + 1) : ℕ) : ℤ) * ((r : ℤ) - 1) := by
      rw [scdTerm, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hr1, Nat.cast_one]
    rw [hDZ, hcast]
    linear_combination ((∏ s ∈ I.erase r, ((2 * t.factorization s + 1 : ℕ) : ℤ)) *
        ((2 * t.factorization r : ℕ) : ℤ) * ((r : ℤ) - 1)) * hkZ
  set D : ℤ := ∏ r ∈ I, ((2 * t.factorization r + 1 : ℕ) : ℤ) with hD
  set B : ℤ := ∑ r ∈ I, (∏ s ∈ I.erase r, ((2 * t.factorization s + 1 : ℕ) : ℤ)) *
    ((2 * t.factorization r : ℕ) : ℤ) * ((r : ℤ) - 1) with hB
  have hsum : D * ((∑ r ∈ I, scdTerm p t r : ℕ) : ℤ) = (p : ℤ) * B - B := by
    rw [hD, hB, Nat.cast_sum, mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl hterm
  have key2 : (p : ℤ) ∣ (p : ℤ) * (2 * B) - D * (2 * ((∑ r ∈ I, scdTerm p t r : ℕ) : ℤ) + 1) :=
    dvd_sub (dvd_mul_right _ _) (dvd_mul_of_dvd_right h2A _)
  have hT : (p : ℤ) * (2 * B) - D * (2 * ((∑ r ∈ I, scdTerm p t r : ℕ) : ℤ) + 1) =
      2 * B - D := by
    linear_combination (-2) * hsum
  rw [hT] at key2
  exact key2

/-- **The contradiction, given a size bound for rows with a common value.** Under the explicit
hypothesis `hsize`, the setting of `square_cycle_digit` is impossible. -/
theorem square_cycle_false_of_size
    (hsize : ∀ (p : ℕ) (I : Finset ℕ) (ℓ : ℕ → ℕ), I.Nonempty →
      (∀ r ∈ I, r.Prime ∧ r ≠ 2 ∧ (ℓ r).Prime ∧ ℓ r ≠ 2 ∧
        ∑ i ∈ Finset.range (ℓ r), r ^ i = p) →
      2 * (∏ r ∈ I, ℓ r) * (∑ r ∈ I, (r - 1)) < p)
    {p e t : ℕ} (hp : p.Prime) (he : 1 ≤ e) (ht : Odd t)
    (hσ : σ 1 (t ^ 2) = p ^ e) (hc : 2 * t ^ 2 = 1 + σ 1 (p ^ e)) : False := by
  obtain ⟨I, hI, hdvd⟩ := square_cycle_digit hp he ht hσ hc
  rcases I.eq_empty_or_nonempty with h0 | hne
  · subst h0
    rw [sum_empty, prod_empty, mul_zero, zero_sub, dvd_neg] at hdvd
    have := Int.le_of_dvd one_pos hdvd
    have := hp.two_le
    omega
  have hs : 2 * (∏ r ∈ I, (2 * t.factorization r + 1)) * (∑ r ∈ I, (r - 1)) < p :=
    hsize p I (fun r => 2 * t.factorization r + 1) hne (fun r hr => by
      obtain ⟨h1, h2, h3, h4⟩ := hI r hr
      exact ⟨h1, h2, h3, by omega, h4⟩)
  set Dn := ∏ r ∈ I, (2 * t.factorization r + 1) with hDn
  set Bn := ∑ r ∈ I, (∏ s ∈ I.erase r, (2 * t.factorization s + 1)) *
    (2 * t.factorization r) * (r - 1) with hBn
  have hBle : Bn ≤ Dn * ∑ r ∈ I, (r - 1) := by
    rw [hBn, mul_sum]
    refine sum_le_sum fun r hr => ?_
    have hE : (2 * t.factorization r + 1) * ∏ s ∈ I.erase r, (2 * t.factorization s + 1) =
        Dn := mul_prod_erase I (fun s => 2 * t.factorization s + 1) hr
    apply Nat.mul_le_mul_right
    rw [← hE, mul_comm (2 * t.factorization r + 1)]
    exact Nat.mul_le_mul_left _ (by omega)
  have h2B : 2 * Bn < p := by
    have : 2 * Bn ≤ 2 * Dn * ∑ r ∈ I, (r - 1) := by
      rw [mul_assoc]; exact Nat.mul_le_mul_left 2 hBle
    omega
  have hBlow : Dn < 2 * Bn := by
    obtain ⟨r0, hr0⟩ := hne
    obtain ⟨hp0, hne2, hℓ0, -⟩ := hI r0 hr0
    have hv : 1 ≤ t.factorization r0 := by
      rcases Nat.eq_zero_or_pos (t.factorization r0) with h | h
      · rw [h] at hℓ0; exact absurd hℓ0 Nat.not_prime_one
      · exact h
    have hr3 : 3 ≤ r0 := by have := hp0.two_le; omega
    set E0 := ∏ s ∈ I.erase r0, (2 * t.factorization s + 1) with hE0d
    have hE0 : (2 * t.factorization r0 + 1) * E0 = Dn :=
      mul_prod_erase I (fun s => 2 * t.factorization s + 1) hr0
    have hE0pos : 0 < E0 := prod_pos fun s _ => by omega
    have hsingle : E0 * (2 * t.factorization r0) * (r0 - 1) ≤ Bn :=
      single_le_sum (f := fun r => (∏ s ∈ I.erase r, (2 * t.factorization s + 1)) *
        (2 * t.factorization r) * (r - 1)) (fun r _ => Nat.zero_le _) hr0
    obtain ⟨m, hm⟩ : ∃ m, r0 - 1 = m := ⟨_, rfl⟩
    rw [hm] at hsingle
    have hm2 : 2 ≤ m := by omega
    have hA : E0 * t.factorization r0 * 2 ≤ E0 * t.factorization r0 * m :=
      Nat.mul_le_mul_left _ hm2
    have hB' : E0 * 1 ≤ E0 * t.factorization r0 := Nat.mul_le_mul_left _ hv
    nlinarith
  have hcastB : (∑ r ∈ I, (∏ s ∈ I.erase r, ((2 * t.factorization s + 1 : ℕ) : ℤ)) *
      ((2 * t.factorization r : ℕ) : ℤ) * ((r : ℤ) - 1)) = ((Bn : ℕ) : ℤ) := by
    rw [hBn, Nat.cast_sum]
    refine sum_congr rfl fun r hr => ?_
    have hr1 : 1 ≤ r := (hI r hr).1.one_lt.le
    push_cast [Nat.cast_sub hr1]
    ring
  have hcastD : ∏ r ∈ I, ((2 * t.factorization r + 1 : ℕ) : ℤ) = ((Dn : ℕ) : ℤ) := by
    rw [hDn, Nat.cast_prod]
  rw [hcastB, hcastD] at hdvd
  have hpos : (0 : ℤ) < 2 * (Bn : ℤ) - Dn := by omega
  have := Int.le_of_dvd hpos hdvd
  omega

end OddPerfect

#print axioms OddPerfect.prime_index_of_sigma_prime_pow
#print axioms OddPerfect.square_cycle_digit
#print axioms OddPerfect.square_cycle_false_of_size
