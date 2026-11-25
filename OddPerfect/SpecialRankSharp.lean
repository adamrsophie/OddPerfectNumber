import OddPerfect.SpecialRank

/-!
# A sharper rational gap and the rank two bound

Restricted result; whether it is in the literature was not verified.

* `lt_pow_mul_sigma_sub_sharp`. Same hypotheses as `lt_pow_mul_sigma_sub`; the conclusion gains
  the factor `q - 2`: `(q - 2) * M < q ^ (b + 1) * (σ(M) - M)`. In the notation of that proof,
  `K = (q - 1) J - q ^ (b + 1) ≥ 1` and `K + 1 = (q - 1) J - (q ^ (b + 1) - 1)` is a multiple
  of `q - 1`, so `K + 1 ≥ q - 1`, that is `K ≥ q - 2`.
* `sub_two_mul_pred_lt_pow_sharp`. For `M = P ^ e` with `P` prime this gives
  `(q - 2) * (P - 1) < q ^ (b + 1)`, since `(σ(P ^ e) - P ^ e) (P - 1) = P ^ e - 1`.
* `special_exponent_le_rank_two_sharp`. Same hypotheses as `special_exponent_le_rank_two`; the
  second term of the maximum drops by one: `a ≤ max (β + e D - 1) ((e + 1) β + e - 2)`. The
  special prime satisfies `q ≡ 1 (mod 4)`, so `q ≥ 5`, and then
  `q σ(P ^ e) < ((q - 2) (P - 1) + 1) ^ e ≤ q ^ ((b + 1) e)` for `e ≥ 2`, which gives
  `w + 1 < (b + 1) e` in place of `w < (b + 1) e`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

private theorem srs_sigma_mul_sub_one {p k : ℕ} (hp : p.Prime) :
    ((σ 1 (p ^ k) : ℕ) : ℤ) * ((p : ℤ) - 1) = (p : ℤ) ^ (k + 1) - 1 := by
  rw [sigma_one_apply_prime_pow hp]
  push_cast
  exact geom_sum_mul _ _

private theorem srs_lt_two_mul {p : ℕ} (hp : p.Prime) (k : ℕ) :
    σ 1 (p ^ k) < 2 * p ^ k := by
  have hg := srs_sigma_mul_sub_one (k := k) hp
  have h2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hpk : (0 : ℤ) < (p : ℤ) ^ k := by positivity
  zify
  rw [pow_succ] at hg
  nlinarith

private theorem srs_le_sigma {M : ℕ} (hM : M ≠ 0) : M ≤ σ 1 M := by
  rw [sigma_one_apply]
  exact Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors_self M hM)

/-- Sharp rational gap, in integers. Let `q` be an odd prime, `σ(M) < 2 M`, `b < a`, and
`q ^ (a - b) * M ∣ σ(q ^ a) * σ(M)`. Then `(q - 2) * M < q ^ (b + 1) * (σ(M) - M)`. This
sharpens `lt_pow_mul_sigma_sub` by the factor `q - 2`. Restricted result; novelty not
verified. -/
theorem lt_pow_mul_sigma_sub_sharp {q M a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hM : σ 1 M < 2 * M) (hab : b < a) (hd : q ^ (a - b) * M ∣ σ 1 (q ^ a) * σ 1 M) :
    (q - 2) * M < q ^ (b + 1) * (σ 1 M - M) := by
  have hM0 : M ≠ 0 := by rintro rfl; simp at hM
  have hle := srs_le_sigma hM0
  have hq3n : 3 ≤ q := by have := hq.two_le; omega
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hab
  rw [show b + c + 1 - b = c + 1 by omega] at hd
  obtain ⟨J, hJ⟩ := hd
  have hJ' : ((σ 1 (q ^ (b + c + 1)) : ℕ) : ℤ) * (σ 1 M : ℕ) =
      (q : ℤ) ^ (c + 1) * M * J := by exact_mod_cast hJ
  have hg := srs_sigma_mul_sub_one (k := b + c + 1) hq
  have hq3 : (3 : ℤ) ≤ q := by exact_mod_cast hq3n
  set S : ℤ := ((σ 1 M : ℕ) : ℤ) with hS
  set K : ℤ := ((q : ℤ) - 1) * J - (q : ℤ) ^ (b + 1) with hK
  have key : (q : ℤ) ^ (c + 1) * M * K = (q : ℤ) ^ (b + c + 2) * (S - M) - S := by
    rw [hK]
    linear_combination ((q : ℤ) - 1) * hJ'.symm + S * hg
  have hdvd : (q : ℤ) - 1 ∣ K + 1 := by
    have h3 : (q : ℤ) - 1 ∣ (q : ℤ) ^ (b + 1) - 1 := by
      simpa using sub_dvd_pow_sub_pow (q : ℤ) 1 (b + 1)
    have h4 : (q : ℤ) - 1 ∣ ((q : ℤ) - 1) * J := dvd_mul_right _ _
    have e : K + 1 = ((q : ℤ) - 1) * J - ((q : ℤ) ^ (b + 1) - 1) := by rw [hK]; ring
    rw [e]
    exact dvd_sub h4 h3
  have hMpos : (1 : ℤ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM0
  have hSM : (M : ℤ) ≤ S := by rw [hS]; exact_mod_cast hle
  have hS2 : S < 2 * M := by rw [hS]; exact_mod_cast hM
  have hX : (3 : ℤ) ≤ (q : ℤ) ^ (c + 1) :=
    hq3.trans (le_self_pow₀ (by linarith) (by omega))
  have hY : (0 : ℤ) ≤ (q : ℤ) ^ (b + c + 2) := by positivity
  have hXM : (0 : ℤ) ≤ (q : ℤ) ^ (c + 1) * M := by positivity
  -- `K ≥ 0`: otherwise the left side of `key` is at most `-3 M < -S`
  have hK0 : 0 ≤ K := by
    by_contra hneg
    have hK1 : K ≤ -1 := by omega
    have := mul_le_mul_of_nonneg_left hK1 hXM
    nlinarith
  have hKq : (q : ℤ) - 2 ≤ K := by
    have := Int.le_of_dvd (by omega) hdvd
    linarith
  have hlt : (q : ℤ) ^ (c + 1) * (((q : ℤ) - 2) * M) <
      (q : ℤ) ^ (c + 1) * ((q : ℤ) ^ (b + 1) * (S - M)) := by
    have h1 := mul_le_mul_of_nonneg_left hKq hXM
    have e : (q : ℤ) ^ (c + 1) * ((q : ℤ) ^ (b + 1) * (S - M)) =
        (q : ℤ) ^ (b + c + 2) * (S - M) := by ring
    rw [e]
    have hS0 : (0 : ℤ) < S := by linarith
    nlinarith
  have hfin := lt_of_mul_lt_mul_left hlt (by positivity)
  zify [hle, show 2 ≤ q by omega]
  exact hfin

/-- Sharp rational gap for one prime power. Let `q` be an odd prime, `P` a prime, `b < a`,
and `q ^ (a - b) * P ^ e ∣ σ(q ^ a) * σ(P ^ e)`. Then `(q - 2) * (P - 1) < q ^ (b + 1)`.
Restricted result; novelty not verified. -/
theorem sub_two_mul_pred_lt_pow_sharp {q P e a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hP : P.Prime) (hab : b < a)
    (hd : q ^ (a - b) * P ^ e ∣ σ 1 (q ^ a) * σ 1 (P ^ e)) :
    (q - 2) * (P - 1) < q ^ (b + 1) := by
  have hgap := lt_pow_mul_sigma_sub_sharp hq hq2 (srs_lt_two_mul hP e) hab hd
  have hge : P ^ e ≤ σ 1 (P ^ e) := srs_le_sigma (pow_ne_zero _ hP.ne_zero)
  have hq3n : 3 ≤ q := by have := hq.two_le; omega
  have hP1 : 1 ≤ P := hP.one_lt.le
  have hg := srs_sigma_mul_sub_one (k := e) hP
  zify [hge, show 2 ≤ q by omega] at hgap
  zify [hP1, show 2 ≤ q by omega]
  set Q : ℤ := ((q ^ (b + 1) : ℕ) : ℤ)
  have hD : (((σ 1 (P ^ e) : ℕ) : ℤ) - ((P ^ e : ℕ) : ℤ)) * ((P : ℤ) - 1) =
      ((P ^ e : ℕ) : ℤ) - 1 := by
    push_cast at hg ⊢
    rw [pow_succ] at hg
    linear_combination hg
  have hP1' : (0 : ℤ) < (P : ℤ) - 1 := by
    have := hP.one_lt
    have : (1 : ℤ) < P := by exact_mod_cast this
    linarith
  have hPe0 : (0 : ℤ) < ((P ^ e : ℕ) : ℤ) := by exact_mod_cast pow_pos hP.pos e
  have hQ0 : (0 : ℤ) ≤ Q := by positivity
  have hA := mul_lt_mul_of_pos_right hgap hP1'
  push_cast at hA hD hPe0 ⊢
  have hA2 : ((q : ℤ) - 2) * (P : ℤ) ^ e * ((P : ℤ) - 1) <
      (q : ℤ) ^ (b + 1) * ((P : ℤ) ^ e - 1) :=
    calc _ < _ := hA
      _ = _ := by rw [mul_assoc, hD]
  by_contra hcon
  push Not at hcon
  have hq0 : (0 : ℤ) < (q : ℤ) ^ (b + 1) := by positivity
  have h1 := mul_le_mul_of_nonneg_right hcon hPe0.le
  nlinarith

private theorem srs_succ_le_pow_of_le {P q m : ℕ} (hP : P.Prime) (hq : q.Prime) (hqP : q < P)
    (hle : P ≤ q ^ m) : P + 1 ≤ q ^ m := by
  rcases Nat.lt_or_ge P (q ^ m) with h | h
  · omega
  · exfalso
    have heq : P = q ^ m := le_antisymm hle h
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [pow_zero] at heq
      exact hP.one_lt.ne' heq
    · have hd : q ∣ P := heq ▸ dvd_pow_self q hm.ne'
      have := (Nat.prime_dvd_prime_iff_eq hq hP).mp hd
      omega

private theorem srs_lt_of_pow_le_lt {q w m X : ℕ} (hq : q.Prime) (h1 : q ^ w ≤ X)
    (h2 : X < q ^ m) : w < m :=
  (Nat.pow_lt_pow_iff_right hq.one_lt).mp (lt_of_le_of_lt h1 h2)

/-- For `5 ≤ q < P` and `(q - 2) (P - 1) + 1 ≤ x`, `q σ(P ^ e) < x ^ e` once `e ≥ 2`. -/
private theorem srs_mul_geom_lt {q P x : ℕ} (hq5 : 5 ≤ q) (hqP : q < P)
    (hx : (q - 2) * (P - 1) + 1 ≤ x) :
    ∀ e, 2 ≤ e → q * ∑ i ∈ Finset.range (e + 1), P ^ i < x ^ e := by
  obtain ⟨s, rfl⟩ : ∃ s, q = s + 5 := ⟨q - 5, by omega⟩
  obtain ⟨u, rfl⟩ : ∃ u, P = u + 1 := ⟨P - 1, by omega⟩
  have hx' : (s + 3) * u + 1 ≤ x := by
    rw [show s + 5 - 2 = s + 3 by omega, show u + 1 - 1 = u by omega] at hx
    exact hx
  have hu : s + 5 ≤ u := by omega
  intro e he
  induction e, he using Nat.le_induction with
  | base =>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
    have h1 : ((s + 3) * u + 1) ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hx' 2
    obtain ⟨t, rfl⟩ : ∃ t, u = s + 5 + t := ⟨u - (s + 5), by omega⟩
    have e : ((s + 3) * (s + 5 + t) + 1) ^ 2 = (s + 5) * (0 + 1 + (s + 5 + t + 1) +
        (s + 5 + t + 1) ^ 2) + (s ^ 4 + 2 * s ^ 3 * t + 15 * s ^ 3 + s ^ 2 * t ^ 2 +
        20 * s ^ 2 * t + 78 * s ^ 2 + 5 * s * t ^ 2 + 57 * s * t + 148 * s + 4 * t ^ 2 +
        31 * t + 41) := by ring
    omega
  | succ k hk ih =>
    have e : ∑ i ∈ Finset.range (k + 1 + 1), (u + 1) ^ i =
        (u + 1) * ∑ i ∈ Finset.range (k + 1), (u + 1) ^ i + 1 := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp [pow_succ, mul_comm]
    have hxP : u + 1 ≤ x := by nlinarith
    rw [e, pow_succ]
    set T := ∑ i ∈ Finset.range (k + 1), (u + 1) ^ i
    have h1 : (u + 1) * ((s + 5) * T + 1) ≤ (u + 1) * x ^ k := Nat.mul_le_mul_left _ ih
    have h2 : (u + 1) * x ^ k ≤ x ^ k * x := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hxP
    have e2 : (s + 5) * ((u + 1) * T + 1) + (u + 1) = (u + 1) * ((s + 5) * T + 1) + (s + 5) := by
      ring
    omega

/-- Sharp rank two bound on the special exponent. Hypotheses as in
`special_exponent_le_rank_two`: `N` odd perfect with special prime `q`, a prime factor `P > q`
such that every other prime factor is at most `q`, every prime factor `p < q` has
`v_p(N) ≤ D`, and the rows of the prime factors `p < q` carry at most `β` at `q` in total.
Then with `e = v_P(N)`, `a ≤ max (β + e D - 1) ((e + 1) β + e - 2)`. Restricted result;
novelty not verified. -/
theorem special_exponent_le_rank_two_sharp {N q P D β : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hP : P ∈ N.primeFactors) (hqP : q < P)
    (hsecond : ∀ p ∈ N.primeFactors, p ≠ P → p ≤ q)
    (hD : ∀ p ∈ N.primeFactors, p < q → N.factorization p ≤ D)
    (hβ : ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p q ≤ β) :
    N.factorization q ≤ max (β + N.factorization P * D - 1)
      ((N.factorization P + 1) * β + N.factorization P - 2) := by
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hPq : P ≠ q := by omega
  have hoddN : ∀ p ∈ N.primeFactors, p % 2 = 1 := fun p hp =>
    Nat.odd_iff.mp (h.1.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
  have hqmem : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by obtain ⟨j, hj⟩ := hodd; omega)
  have hq2 : q ≠ 2 := fun h2 => by have := hoddN q hqmem; omega
  have hP2 : P ≠ 2 := fun h2 => by have := hoddN P hP; omega
  have hq5 : 5 ≤ q := by
    have h4 := (special_mod_four h hq hodd).1
    have := hq.two_le
    have : q ≠ 1 := hq.one_lt.ne'
    omega
  set a := N.factorization q with ha
  set e := N.factorization P with he
  set w := sigmaWeight N P q with hw
  have he2 : 2 ≤ e := by
    obtain ⟨k, hk⟩ := even_factorization_of_ne h hq hodd hPp hPq
    have : 1 ≤ e := (hPp.dvd_iff_one_le_factorization h.ne_zero).mp
      (Nat.dvd_of_mem_primeFactors hP)
    omega
  have hsum := sigmaWeight_sum_eq h.2 hq hq2
  rw [← Finset.sum_filter_add_sum_filter_not N.primeFactors (· < q)] at hsum
  have hrest : ∑ p ∈ N.primeFactors.filter (fun p => ¬ p < q), sigmaWeight N p q ≤ w := by
    have hsub : N.primeFactors.filter (fun p => ¬ p < q) ⊆ {q, P} := by
      intro p hp
      obtain ⟨hp, hpq⟩ := Finset.mem_filter.mp hp
      by_cases hpP : p = P
      · simp [hpP]
      · have := hsecond p hp hpP
        simp [show p = q by omega]
    refine (Finset.sum_le_sum_of_subset hsub).trans ?_
    rw [Finset.sum_pair hPq.symm, sigmaWeight_self hq]
    omega
  have haw : a ≤ β + w := by omega
  have hwa : w ≤ a := by
    have := Finset.single_le_sum (f := fun p => sigmaWeight N p q) (fun _ _ => Nat.zero_le _) hP
    have h2 := sigmaWeight_sum_eq h.2 hq hq2
    omega
  have hσP : σ 1 (P ^ e) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hPp.ne_zero)).ne'
  have hqw : q ^ w ∣ σ 1 (P ^ e) := Nat.ordProj_dvd _ _
  have hqwle : q ^ w ≤ σ 1 (P ^ e) := Nat.le_of_dvd (Nat.pos_of_ne_zero hσP) hqw
  have hσlt := sigma_prime_pow_lt_succ_pow hPp he2
  by_cases hc1 : ∃ u ∈ N.primeFactors, u < q ∧ P ∣ σ 1 (u ^ N.factorization u)
  · -- Case 1: the largest prime divides the row of a smaller prime (unchanged)
    obtain ⟨u, hu, huq, hPu⟩ := hc1
    have hup := Nat.prime_of_mem_primeFactors hu
    set k := N.factorization u with hk
    have hkD : k ≤ D := hD u hu huq
    have h1 : P ≤ σ 1 (u ^ k) :=
      Nat.le_of_dvd (sigma_pos 1 _ (pow_ne_zero _ hup.ne_zero)) hPu
    have h2 := sigma_prime_pow_le_succ_pow hup k
    have h3 : (u + 1) ^ k ≤ q ^ k := Nat.pow_le_pow_left (by omega) k
    have h4 : q ^ k ≤ q ^ D := Nat.pow_le_pow_right hq.pos hkD
    have hPD : P + 1 ≤ q ^ D := srs_succ_le_pow_of_le hPp hq hqP (by omega)
    have h5 : (P + 1) ^ e ≤ q ^ (D * e) := by
      rw [pow_mul]
      exact Nat.pow_le_pow_left hPD e
    have hwlt : w < D * e := srs_lt_of_pow_le_lt hq hqwle (lt_of_lt_of_le hσlt h5)
    have : D * e = e * D := Nat.mul_comm _ _
    exact le_max_of_le_left (by omega)
  · -- Case 2: all of `v_P(N)` comes from the special row
    push Not at hc1
    have hsumP := sigmaWeight_sum_eq h.2 hPp hP2
    rw [Finset.sum_eq_single q] at hsumP
    · have hPe : P ^ e ∣ σ 1 (q ^ a) := by
        have := Nat.ordProj_dvd (σ 1 (q ^ a)) P
        unfold sigmaWeight at hsumP
        rwa [hsumP] at this
      have hdvd : q ^ w * P ^ e ∣ σ 1 (q ^ a) * σ 1 (P ^ e) := by
        rw [mul_comm (σ 1 (q ^ a))]
        exact mul_dvd_mul hqw hPe
      rcases Nat.eq_zero_or_pos w with hw0 | hw0
      · have : β ≤ (e + 1) * β := Nat.le_mul_of_pos_left β (show 0 < e + 1 by omega)
        exact le_max_of_le_right (by omega)
      · set b := a - w with hb
        have hPQ := sub_two_mul_pred_lt_pow_sharp (P := P) (e := e) (a := a) (b := b) hq hq2
          hPp (by omega) (by rw [show a - b = w by omega]; exact hdvd)
        have hmain := srs_mul_geom_lt hq5 hqP (show (q - 2) * (P - 1) + 1 ≤ q ^ (b + 1) by
          omega) e he2
        rw [← sigma_one_apply_prime_pow hPp, ← pow_mul] at hmain
        have hqw1 : q ^ (w + 1) ≤ q * σ 1 (P ^ e) := by
          rw [pow_succ, mul_comm]
          exact Nat.mul_le_mul_left q hqwle
        have hwlt : w + 1 < (b + 1) * e := srs_lt_of_pow_le_lt hq hqw1 hmain
        have hbβ : b ≤ β := by omega
        have h6 : (b + 1) * e ≤ (β + 1) * e := Nat.mul_le_mul_right e (by omega)
        have h7 : (e + 1) * β + e = (β + 1) * e + β := by ring
        exact le_max_of_le_right (by omega)
    · intro p hp hpq
      by_cases hpP : p = P
      · rw [hpP]; exact sigmaWeight_self hPp
      · have hpq' : p < q := by have := hsecond p hp hpP; omega
        exact Nat.factorization_eq_zero_of_not_dvd (hc1 p hp hpq')
    · intro hq'
      exact absurd hqmem hq'

end OddPerfect

#print axioms OddPerfect.lt_pow_mul_sigma_sub_sharp
#print axioms OddPerfect.sub_two_mul_pred_lt_pow_sharp
#print axioms OddPerfect.special_exponent_le_rank_two_sharp
