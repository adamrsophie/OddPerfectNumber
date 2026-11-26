import OddPerfect.LargestPrimeSafe
import OddPerfect.LargestPrimeRoots
import OddPerfect.LargestPrimeSigned
import OddPerfect.SquareRow

/-!
# The largest prime factor is never `2 R + 1` with `R` an odd prime

Let `N` be an odd perfect number with largest prime factor `P`. A *sender* is a prime factor
`u ≠ P` with `P ∣ σ(u ^ e_u)`, where `e_u = v_u(N)`.

* `three_pow_sub_one_eq_two_mul_sq`: arithmetic. If `n` is odd and `3 ^ n - 1 = 2 y ^ 2`, then
  `n = 1` or `n = 5`. This is a case of the classical equation `(x ^ n - 1) / (x - 1) = y ^ 2`;
  here it follows from the landed `isSquare_sigma_prime_pow_iff` at `p = 3`.
* `largest_safe_sender_unique`: if `P = 2 R + 1` with `R` an odd prime, there is at most one
  sender. Each sender `u` has order `R` modulo `P` and the row `1 + u + ⋯ + u ^ (R - 1) = P ^ j`
  (`largest_safe_sender_row`). For senders `u₁, u₂` with `j₁ ≤ j₂`, the powers of `u₁` are all
  the `R`th roots of unity modulo `P`, so `u₂ ≡ u₁ ^ k (mod P)` with `1 ≤ k < R`. Both
  `u₂ < P` and `u₁ ^ k < P ^ j₁` have `2 R`th powers `≡ 1 (mod P ^ j₁)`, so the landed signed
  lifting lemma `eq_of_sq_modEq_of_pow_two_mul_modEq_one` gives `u₂ = u₁ ^ k`, hence
  `u₂ = u₁`.
* `largest_primeFactor_ne_two_mul_prime_add_one`: the main theorem. With one sender `u`,
  `v_P(N) = j` is even; the parity lemma forces `u = 3`, so `σ(3 ^ (R - 1)) = P ^ j` is a square
  and `R = 5`, `P = 11`, `j = 2`. Then `σ(11 ^ 2) = 7 · 19` divides `2 N`, and `19 > 11`.

Scope: statements 2 and 3 are about a hypothetical odd perfect number. Statement 3 excludes
one shape of the largest prime factor; it is not a bound and does not decide the conjecture,
which remains open. Novelty was not verified. Published context, not formalized here and not
used: the largest prime factor of an odd perfect number exceeds `10 ^ 8` (Goto and Ohno, 2008).
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

variable {N P R : ℕ}

/-- If `n` is odd and `3 ^ n - 1 = 2 y ^ 2`, then `n = 1` or `n = 5` (`3 ^ 5 - 1 = 2 · 11 ^ 2`).
A case of the classical equation `(x ^ n - 1) / (x - 1) = y ^ 2`. -/
theorem three_pow_sub_one_eq_two_mul_sq {n y : ℕ} (hn : Odd n) (h : 3 ^ n - 1 = 2 * y ^ 2) :
    n = 1 ∨ n = 5 := by
  obtain ⟨k, rfl⟩ := hn
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · left; rfl
  right
  have hg : (∑ i ∈ Finset.range (2 * k + 1), 3 ^ i) * 2 + 1 = 3 ^ (2 * k + 1) :=
    geom_sum_mul_add 2 (2 * k + 1)
  have hsq : IsSquare (σ 1 (3 ^ (2 * k))) := by
    refine ⟨y, ?_⟩
    rw [sigma_one_apply_prime_pow Nat.prime_three]
    have : 3 ^ (2 * k + 1) - 1 = (∑ i ∈ Finset.range (2 * k + 1), 3 ^ i) * 2 := by
      generalize 3 ^ (2 * k + 1) = T at hg ⊢
      omega
    rw [this] at h
    nlinarith
  have := ((isSquare_sigma_prime_pow_iff Nat.prime_three (by norm_num)
    (even_two_mul k) (by omega)).mp hsq).2
  omega

private theorem lpsn_odd_of_mem (h : OddPerfect N) {p : ℕ} (hp : p ∈ N.primeFactors) :
    p % 2 = 1 :=
  Nat.odd_iff.mp (h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))

/-- `u ^ R ≡ 1` modulo the row `1 + u + ⋯ + u ^ (R - 1)`. -/
private theorem lpsn_pow_modEq {u R : ℕ} (hu : 1 ≤ u) :
    u ^ R ≡ 1 [MOD ∑ i ∈ Finset.range R, u ^ i] := by
  have hg := geom_sum_mul_add (u - 1) R
  rw [Nat.sub_add_cancel hu] at hg
  rw [← hg, Nat.ModEq, Nat.mul_add_mod_self_left]

/-- The arithmetic core of uniqueness: two odd primes `u₁, u₂ < P` of order `R` modulo `P`
whose rows are `P ^ j₁` and `P ^ j₂` with `1 ≤ j₁ ≤ j₂` are equal. -/
private theorem lpsn_eq_aux {u₁ u₂ j₁ j₂ : ℕ} (hP : P.Prime) (hR2 : 2 ≤ R) (hPm : ¬ P ∣ 2 * R)
    (hu₁ : u₁.Prime) (hu₂ : u₂.Prime) (h1o : u₁ % 2 = 1) (h2o : u₂ % 2 = 1) (h2lt : u₂ < P)
    (hord1 : orderOf (u₁ : ZMod P) = R) (hord2 : orderOf (u₂ : ZMod P) = R)
    (hF1 : ∑ i ∈ Finset.range R, u₁ ^ i = P ^ j₁) (hF2 : ∑ i ∈ Finset.range R, u₂ ^ i = P ^ j₂)
    (hj1 : 1 ≤ j₁) (hj : j₁ ≤ j₂) : u₁ = u₂ := by
  have : Fact P.Prime := ⟨hP⟩
  set x : ZMod P := (u₁ : ZMod P) with hx
  have hxR : x ^ R = 1 := by rw [← hord1]; exact pow_orderOf_eq_one x
  have hyR : (u₂ : ZMod P) ^ R = 1 := by rw [← hord2]; exact pow_orderOf_eq_one _
  set L := (List.range R).map (fun i => x ^ i) with hL
  have hnd : L.Nodup := by
    refine List.Nodup.map_on (fun a ha b hb hab => ?_) List.nodup_range
    have ha' : a < orderOf x := by rw [hord1]; exact List.mem_range.mp ha
    have hb' : b < orderOf x := by rw [hord1]; exact List.mem_range.mp hb
    exact pow_injOn_Iio_orderOf ha' hb' hab
  have hmem := mem_of_pow_eq_one_of_nodup (by omega) hnd (by simp [hL])
    (fun z hz => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hz
      rw [← pow_mul, mul_comm, pow_mul, hxR, one_pow]) hyR
  obtain ⟨k, hkR, hk⟩ := List.mem_map.mp hmem
  have hkR' := List.mem_range.mp hkR
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    rw [← hk, orderOf_one] at hord2
    omega
  -- the lift modulo `P ^ j₁`
  have hM : P ^ j₁ ∣ P ^ j₂ := pow_dvd_pow P hj
  have hX2 : u₂ ^ (2 * R) ≡ 1 [MOD P ^ j₁] := by
    have h1 := (lpsn_pow_modEq (R := R) hu₂.one_lt.le).of_dvd (hF2 ▸ hM)
    rw [mul_comm, pow_mul]
    simpa using h1.pow 2
  have hY2 : (u₁ ^ k) ^ (2 * R) ≡ 1 [MOD P ^ j₁] := by
    have h1 := lpsn_pow_modEq (R := R) hu₁.one_lt.le
    rw [hF1] at h1
    rw [← pow_mul, show k * (2 * R) = R * (2 * k) by ring, pow_mul]
    simpa using h1.pow (2 * k)
  have hXlt : u₂ < P ^ j₁ := lt_of_lt_of_le h2lt (Nat.le_self_pow (by omega) P)
  have hYlt : u₁ ^ k < P ^ j₁ := by
    rw [← hF1]
    have hsub : ∑ i ∈ Finset.range (k + 1), u₁ ^ i ≤ ∑ i ∈ Finset.range R, u₁ ^ i :=
      Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
    rw [Finset.sum_range_succ] at hsub
    have hpos : 0 < ∑ i ∈ Finset.range k, u₁ ^ i :=
      Finset.sum_pos (fun i _ => pow_pos hu₁.pos i) ⟨0, Finset.mem_range.mpr (by omega)⟩
    omega
  have hYo : u₁ ^ k % 2 = 1 := by simp [Nat.pow_mod, h1o]
  have hXY : u₂ ^ 2 ≡ (u₁ ^ k) ^ 2 [MOD P] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    push_cast
    rw [← hk]
  have heq := eq_of_sq_modEq_of_pow_two_mul_modEq_one hP hPm hj1 hXlt hYlt h2o hYo hX2 hY2 hXY
  exact (Nat.prime_dvd_prime_iff_eq hu₁ hu₂).mp (heq ▸ dvd_pow_self u₁ hk0)

/-- At most one sender. Let the largest prime factor of an odd perfect number `N` be
`P = 2 R + 1` with `R` an odd prime. If `u` and `v` are prime factors different from `P` with
`P ∣ σ(u ^ e_u)` and `P ∣ σ(v ^ e_v)`, then `u = v`. -/
theorem largest_safe_sender_unique (h : OddPerfect N) (hP : P ∈ N.primeFactors)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hR : R.Prime) (hR2 : R ≠ 2) (hPR : P = 2 * R + 1)
    {u v : ℕ} (hu : u ∈ N.primeFactors) (huP : u ≠ P) (hdu : P ∣ σ 1 (u ^ N.factorization u))
    (hv : v ∈ N.primeFactors) (hvP : v ≠ P) (hdv : P ∣ σ 1 (v ^ N.factorization v)) :
    u = v := by
  have hPp := Nat.prime_of_mem_primeFactors hP
  obtain ⟨-, hou, hFu, hju⟩ := largest_safe_sender_row h hP hmax hR hR2 hPR hu huP hdu
  obtain ⟨-, hov, hFv, hjv⟩ := largest_safe_sender_row h hP hmax hR hR2 hPR hv hvP hdv
  obtain ⟨hlu, -⟩ := sender_largest_data h hP hmax hu huP hdu
  obtain ⟨hlv, -⟩ := sender_largest_data h hP hmax hv hvP hdv
  have hPm : ¬ P ∣ 2 * R := by
    intro hd
    have := Nat.le_of_dvd (by have := hR.two_le; omega) hd
    omega
  have hup := Nat.prime_of_mem_primeFactors hu
  have hvp := Nat.prime_of_mem_primeFactors hv
  rcases le_total (padicValNat P (σ 1 (u ^ N.factorization u)))
      (padicValNat P (σ 1 (v ^ N.factorization v))) with hle | hle
  · exact lpsn_eq_aux hPp hR.two_le hPm hup hvp (lpsn_odd_of_mem h hu) (lpsn_odd_of_mem h hv)
      hlv hou hov hFu hFv hju hle
  · exact (lpsn_eq_aux hPp hR.two_le hPm hvp hup (lpsn_odd_of_mem h hv) (lpsn_odd_of_mem h hu)
      hlu hov hou hFv hFu hjv hle).symm

/-- The senders into `P` and the ledger `v_P(N) = Σ_senders v_P(σ(u ^ e_u))` (a copy of a
private lemma of `OddPerfect/LargestPrimeCapacity.lean`). -/
private theorem lpsn_sum_senders (h : OddPerfect N) (hP : P ∈ N.primeFactors) :
    N.factorization P = ∑ p ∈ (N.primeFactors.erase P).filter
      (fun p => P ∣ σ 1 (p ^ N.factorization p)), padicValNat P (σ 1 (p ^ N.factorization p)) := by
  have hP2 : P ≠ 2 := by have := lpsn_odd_of_mem h hP; omega
  rw [factorization_eq_sum_erase h.perfect (Nat.prime_of_mem_primeFactors hP) hP2,
    Finset.sum_filter_of_ne]
  intro p _ hne
  by_contra hd
  exact hne (by rw [Nat.padicValNat_def]; exact multiplicity_eq_zero_of_not_dvd hd)

/-- **The largest prime factor of an odd perfect number is never `2 R + 1` with `R` an odd
prime.** This excludes one shape of the largest prime factor; it is not a bound and does not
decide the odd perfect number conjecture. Novelty was not verified. -/
theorem largest_primeFactor_ne_two_mul_prime_add_one (h : OddPerfect N)
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hR : R.Prime)
    (hR2 : R ≠ 2) : P ≠ 2 * R + 1 := by
  intro hPR
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hR3 : 3 ≤ R := by have := hR.two_le; omega
  have hRo := Nat.odd_iff.mp (hR.odd_of_ne_two hR2)
  set S := (N.primeFactors.erase P).filter (fun p => P ∣ σ 1 (p ^ N.factorization p))
    with hSdef
  have hcard : S.card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    rw [hSdef, Finset.mem_filter, Finset.mem_erase] at ha hb
    exact largest_safe_sender_unique h hP hmax hR hR2 hPR ha.1.2 ha.1.1 ha.2 hb.1.2 hb.1.1 hb.2
  by_cases h3 : P ∣ σ 1 (3 ^ N.factorization 3)
  swap
  · have h2 : 2 ≤ S.card := (largest_safe_card_senders h hP hmax hR hR2 hPR h3).2
    omega
  have h3N : 3 ∈ N.primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨Nat.prime_three, ?_, h.ne_zero⟩
    by_contra hn
    rw [Nat.factorization_eq_zero_of_not_dvd hn, sigma_one_apply_prime_pow Nat.prime_three]
      at h3
    norm_num at h3
    omega
  have h3P : (3 : ℕ) ≠ P := by omega
  obtain ⟨he, -, hrow, -⟩ := largest_safe_sender_row h hP hmax hR hR2 hPR h3N h3P h3
  have hpar := (largest_safe_sender_parity h hP hmax hR hR2 hPR h3N h3P h3).2 rfl
  set j := padicValNat P (σ 1 (3 ^ N.factorization 3)) with hjdef
  -- the row of `3` is a square, so `R = 5`
  have hσ : σ 1 (3 ^ (R - 1)) = P ^ j := by
    rw [sigma_one_apply_prime_pow Nat.prime_three, Nat.sub_add_cancel hR.one_le]
    exact hrow
  obtain ⟨m, hm⟩ := hpar
  have hsq : IsSquare (σ 1 (3 ^ (R - 1))) := ⟨P ^ m, by rw [hσ, hm, pow_add]⟩
  have hR5 : R = 5 := by
    have := ((isSquare_sigma_prime_pow_iff Nat.prime_three (by norm_num)
      ⟨(R - 1) / 2, by omega⟩ (by omega)).mp hsq).2
    omega
  subst hR5
  subst hPR
  have hj2 : j = 2 := by
    have h121 : (11 : ℕ) ^ j = 11 ^ 2 := by
      rw [← hσ, sigma_one_apply_prime_pow Nat.prime_three]
      decide
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 11) h121
  -- one sender, so `v_11(N) = 2`
  have hS : S = {3} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun x hx => ?_⟩
    · rw [hSdef, Finset.mem_filter, Finset.mem_erase]
      exact ⟨⟨h3P, h3N⟩, h3⟩
    · exact Finset.card_le_one.mp hcard x hx 3
        (by rw [hSdef, Finset.mem_filter, Finset.mem_erase]; exact ⟨⟨h3P, h3N⟩, h3⟩)
  have hv : N.factorization 11 = 2 := by
    rw [lpsn_sum_senders h hP, ← hSdef, hS, Finset.sum_singleton]
    exact hj2
  -- `σ(11 ^ 2) = 7 · 19` divides `2 N`
  have hdvd := OPNStarter.component_sigma_dvd h.perfect hPp hv
  have h19 : 19 ∣ 2 * N := by
    refine dvd_trans ?_ hdvd
    rw [sigma_one_apply_prime_pow hPp]
    decide
  have h19N : 19 ∣ N :=
    Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h19
  have := hmax 19 (Nat.mem_primeFactors.mpr ⟨by norm_num, h19N, h.ne_zero⟩)
  omega

/-! ## Controls -/

/-- The two odd solutions `n = 1` and `n = 5` of `3 ^ n - 1 = 2 y ^ 2`. -/
example : 3 ^ 5 - 1 = 2 * 11 ^ 2 ∧ 3 ^ 1 - 1 = 2 * 1 ^ 2 := by norm_num

/-- The divisor sum `σ(11 ^ 2) = 133 = 7 · 19`. -/
example : 1 + 11 + 11 ^ 2 = 7 * 19 := by norm_num

end OddPerfect

#print axioms OddPerfect.three_pow_sub_one_eq_two_mul_sq
#print axioms OddPerfect.largest_safe_sender_unique
#print axioms OddPerfect.largest_primeFactor_ne_two_mul_prime_add_one
