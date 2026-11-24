import OddPerfect.UpperBound
import OddPerfect.RadicalBound

/-!
# The sharper upper bound of Nielsen (2015)

Following P. P. Nielsen, "Odd perfect numbers, Diophantine equations, and upper bounds",
Math. Comp. 84 (2015), 2549 to 2567, an odd perfect number `N` with `k` distinct prime
factors satisfies `N < 2^((2^k - 1)^2)` (`lt_two_pow_sq`, inequality (18) of Corollary 1.7).

Two inputs are combined, both in the power form (with `x^(2^r)` in place of Nielsen's
`F_r(x) = x^(2^r) - x^(2^(r-1))`):

* Theorem 1.6, second inequality (`mul_mul_prod_lt_succ_pow_four_pow`): an odd `N` with
  `σ(N)/N = n/d` satisfies `n N Π(X) Π'(X) < (d + 1)^(4^k)`, where `Π(X)` is the product of
  the prime factors and `Π'(X)` the product of the `p - 1`. The proof is the Heath-Brown and
  Nielsen algorithm of `OddPerfect.UpperBound`, restated here so that each step keeps the
  factor `Π(W) Π'(W)` of the selected prime power components (Lemma 1.5 (ii)).
* Inequality (19) in power form (`two_mul_prod_sub_one_mul_lt`): Cook's lemma applied to the
  numbers `p^(e+1)` with `a = 2 Π'(X)` and `b = Π(X)` gives
  `2 Π'(X) Π(X) N < (2 Π'(X) + 1)^(2^k)`.

With `c = 2 Π'(X) + 1 ≤ Π(X)`, the first bound is used when `c ≥ 2^(2^k)` and the second when
`c ≤ 2^(2^k)`; in both cases `N c (c - 1) < C^(2^k)` for `C = min(c, 2^(2^k))`, which gives
`N < 2 C^(2^k - 2) ≤ 2^((2^k - 1)^2)`.

The helper lemmas below restate private lemmas of `OddPerfect.UpperBound`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect.UpperBoundSharp

private theorem one_sub_inv_pos {x : ℕ} (hx : 2 ≤ x) : 0 < 1 - 1 / (x : ℚ) := by
  have : (2 : ℚ) ≤ x := by exact_mod_cast hx
  have : 1 / (x : ℚ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
  linarith

private theorem prod_one_sub_inv_eq {H : Finset ℕ} (h2 : ∀ x ∈ H, 2 ≤ x) :
    ∏ x ∈ H, (1 - 1 / (x : ℚ)) = ((∏ x ∈ H, (x - 1) : ℕ) : ℚ) / ((∏ x ∈ H, x : ℕ) : ℚ) := by
  rw [Nat.cast_prod, Nat.cast_prod, ← prod_div_distrib]
  refine prod_congr rfl (fun x hx => ?_)
  have hx := h2 x hx
  have hx0 : (x : ℚ) ≠ 0 := by positivity
  rw [Nat.cast_sub (by omega), Nat.cast_one]
  field_simp

private theorem abundancy_mul_one_sub {p : ℕ} (hp : p.Prime) (k : ℕ) :
    abundancy (p ^ k) * (1 - 1 / (p : ℚ)) = 1 - 1 / ((p ^ (k + 1) : ℕ) : ℚ) := by
  rw [abundancy_prime_pow hp, one_div, geom_sum_mul_neg]
  push_cast
  rw [one_div, inv_pow]

private theorem sigma_mul_sub_one {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (σ 1 (p ^ k) : ℚ) * ((p : ℚ) - 1) = (p : ℚ) ^ (k + 1) - 1 := by
  rw [sigma_one_apply_prime_pow hp]
  push_cast
  exact geom_sum_mul _ _

private theorem succ_le_sigma {N : ℕ} (hN : 1 < N) : N + 1 ≤ σ 1 N := by
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have : 1 ≤ ∑ i ∈ N.properDivisors, i :=
    single_le_sum (f := id) (fun _ _ => Nat.zero_le _)
      (Nat.one_mem_properDivisors_iff_one_lt.mpr hN)
  omega

private theorem two_le_of_mem {N p : ℕ} (hp : p ∈ N.primeFactors) : 2 ≤ p :=
  (Nat.prime_of_mem_primeFactors hp).two_le

private theorem prod_sub_one_pos (S : Finset ℕ) (h2 : ∀ p ∈ S, 2 ≤ p) :
    0 < ∏ p ∈ S, (p - 1) :=
  prod_pos (fun p hp => by have := h2 p hp; omega)

/-- Gluing step: `Q (t + 1)^e + 1 ≤ (t Q + 1)^e + Q` for `Q ≥ 1`. -/
private theorem glue_aux (t Q e : ℕ) (hQ : 1 ≤ Q) :
    Q * (t + 1) ^ e + 1 ≤ (t * Q + 1) ^ e + Q := by
  induction e with
  | zero => simp only [pow_zero, mul_one]; omega
  | succ e ih =>
    obtain ⟨c, hc⟩ : ∃ c, (t * Q + 1) ^ e = c + 1 :=
      ⟨(t * Q + 1) ^ e - 1, by have := Nat.one_le_pow e (t * Q + 1) (by omega); omega⟩
    rw [hc] at ih
    rw [pow_succ, pow_succ, hc]
    have h1 := Nat.mul_le_mul_right (t + 1) ih
    have h2 : c * t ≤ c * t * Q := Nat.le_mul_of_pos_right _ hQ
    nlinarith

private theorem glue {X t Q e : ℕ} (h : X < (t + 1) ^ e) (hQ : 1 ≤ Q) :
    X * Q < (t * Q + 1) ^ e := by
  have h1 := glue_aux t Q e hQ
  have h2 : (X + 1) * Q ≤ (t + 1) ^ e * Q := Nat.mul_le_mul_right _ h
  nlinarith

section Step

variable {N d n : ℕ}

private theorem n_pos (hN : 0 < N) (hd : 0 < d) (hσ : d * σ 1 N = n * N) : 0 < n := by
  have : 0 < σ 1 N := ArithmeticFunction.sigma_pos 1 N hN.ne'
  rcases Nat.eq_zero_or_pos n with h | h
  · rw [h, zero_mul] at hσ
    exact absurd hσ (Nat.mul_pos hd this).ne'
  · exact h

private theorem abundancy_eq (hN : 0 < N) (hd : 0 < d) (hσ : d * σ 1 N = n * N) :
    abundancy N = n / d := by
  rw [abundancy, div_eq_div_iff (by exact_mod_cast hN.ne') (by exact_mod_cast hd.ne')]
  have : ((d * σ 1 N : ℕ) : ℚ) = ((n * N : ℕ) : ℚ) := by rw [hσ]
  push_cast at this
  linarith

private theorem prod_lt_d_div_n (hN1 : 1 < N) (hd : 0 < d) (hσ : d * σ 1 N = n * N) :
    ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ)) < d / n := by
  have hn := n_pos (by omega) hd hσ
  have hab := abundancy_eq (by omega) hd hσ
  rw [abundancy_eq_prod_primeFactors (by omega)] at hab
  have key : (∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ))) * (n / d) < 1 := by
    rw [← hab, ← prod_mul_distrib]
    have : ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ)) * abundancy (p ^ N.factorization p) =
        ∏ p ∈ N.primeFactors, (1 - 1 / ((p ^ (N.factorization p + 1) : ℕ) : ℚ)) :=
      prod_congr rfl (fun p hp => by
        rw [mul_comm, abundancy_mul_one_sub (Nat.prime_of_mem_primeFactors hp)])
    rw [this]
    calc _ < ∏ p ∈ N.primeFactors, (1 : ℚ) := by
          apply prod_lt_prod_of_nonempty
          · intro p hp
            exact one_sub_inv_pos (le_trans (two_le_of_mem hp)
              (Nat.le_self_pow (by omega) p))
          · intro p hp
            have : (0 : ℚ) < ((p ^ (N.factorization p + 1) : ℕ) : ℚ) := by
              have := two_le_of_mem hp; positivity
            have : 0 < 1 / ((p ^ (N.factorization p + 1) : ℕ) : ℚ) := by positivity
            linarith
          · exact Nat.nonempty_primeFactors.mpr hN1
      _ = 1 := prod_const_one
  have hnd : (0 : ℚ) < n / d := by
    have : (0 : ℚ) < n := by exact_mod_cast hn
    have : (0 : ℚ) < d := by exact_mod_cast hd
    positivity
  rw [← lt_div_iff₀ hnd, one_div_div] at key
  exact key

private theorem prod_pp_le (hN : 0 < N) (hd : 0 < d) (hσ : d * σ 1 N = n * N) {R : Finset ℕ}
    (hR : R ⊆ N.primeFactors) :
    ∏ p ∈ R, (1 - 1 / ((p ^ (N.factorization p + 1) : ℕ) : ℚ)) ≤
      (n / d) * ∏ p ∈ R, (1 - 1 / (p : ℚ)) := by
  have hab := abundancy_eq hN hd hσ
  rw [abundancy_eq_prod_primeFactors (by omega)] at hab
  have e : ∏ p ∈ R, (1 - 1 / ((p ^ (N.factorization p + 1) : ℕ) : ℚ)) =
      (∏ p ∈ R, abundancy (p ^ N.factorization p)) * ∏ p ∈ R, (1 - 1 / (p : ℚ)) := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl (fun p hp => by
      rw [abundancy_mul_one_sub (Nat.prime_of_mem_primeFactors (hR hp))])
  rw [e, ← hab]
  apply mul_le_mul_of_nonneg_right _ (prod_nonneg (fun p hp =>
    (one_sub_inv_pos (two_le_of_mem (hR hp))).le))
  rw [← prod_sdiff hR]
  have h1 : ∀ p ∈ N.primeFactors, 1 ≤ abundancy (p ^ N.factorization p) := fun p hp => by
    have hp' := Nat.prime_of_mem_primeFactors hp
    have := one_add_inv_le_abundancy_prime_pow hp'
      (hp'.factorization_pos_of_dvd hN.ne' (Nat.dvd_of_mem_primeFactors hp))
    have : (0 : ℚ) ≤ (p : ℚ)⁻¹ := by positivity
    linarith
  have h0 : ∀ p ∈ N.primeFactors, 0 ≤ abundancy (p ^ N.factorization p) := fun p hp =>
    le_trans zero_le_one (h1 p hp)
  have : 1 ≤ ∏ p ∈ N.primeFactors \ R, abundancy (p ^ N.factorization p) := by
    calc (1 : ℚ) = ∏ p ∈ N.primeFactors \ R, (1 : ℚ) := prod_const_one.symm
      _ ≤ _ := prod_le_prod (fun _ _ => zero_le_one)
          (fun p hp => h1 p (sdiff_subset hp))
  have hpos : 0 ≤ ∏ p ∈ R, abundancy (p ^ N.factorization p) :=
    prod_nonneg (fun p hp => h0 p (hR hp))
  nlinarith

private theorem prod_ne_d_div_n (hodd : Odd N) (hN1 : 1 < N) (hd : 0 < d)
    (hσ : d * σ 1 N = n * N)
    {R : Finset ℕ} (hR : R ⊆ N.primeFactors) :
    ∏ p ∈ R, (1 - 1 / (p : ℚ)) ≠ d / n := by
  intro h
  have hn := n_pos (by omega) hd hσ
  have h2R : ∀ p ∈ R, 2 ≤ p := fun p hp => two_le_of_mem (hR hp)
  rw [prod_one_sub_inv_eq h2R] at h
  have hPR : 0 < ∏ p ∈ R, p := prod_pos (fun p hp => by have := h2R p hp; omega)
  rw [div_eq_div_iff (by exact_mod_cast hPR.ne') (by exact_mod_cast hn.ne')] at h
  have hE : (∏ p ∈ R, (p - 1)) * n = d * ∏ p ∈ R, p := by exact_mod_cast h
  have hE2 : (∏ p ∈ R, (p - 1)) * σ 1 N = (∏ p ∈ R, p) * N := by
    apply Nat.eq_of_mul_eq_mul_left hd
    calc d * ((∏ p ∈ R, (p - 1)) * σ 1 N) = (∏ p ∈ R, (p - 1)) * (d * σ 1 N) := by ring
      _ = (∏ p ∈ R, (p - 1)) * n * N := by rw [hσ]; ring
      _ = d * ((∏ p ∈ R, p) * N) := by rw [hE]; ring
  have hNodd : ¬ 2 ∣ N := hodd.not_two_dvd_nat
  have hpodd : ∀ p ∈ R, ¬ 2 ∣ p := fun p hp h2 => by
    have hp' := Nat.prime_of_mem_primeFactors (hR hp)
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp').mp h2
    subst this
    exact hNodd (Nat.dvd_of_mem_primeFactors (hR hp))
  have hodd2 : ¬ 2 ∣ (∏ p ∈ R, p) * N := by
    intro h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · obtain ⟨p, hp, h2p⟩ := (Prime.dvd_finsetProd_iff Nat.prime_two.prime _).mp h
      exact hpodd p hp h2p
    · exact hNodd h
  rcases R.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · simp only [prod_empty, one_mul] at hE2
    have := succ_le_sigma hN1
    omega
  · have h2p : 2 ∣ p - 1 := by have := hpodd p hp; omega
    exact hodd2 (hE2 ▸ dvd_mul_of_dvd_left
      (dvd_trans h2p (dvd_prod_of_mem (fun q => q - 1) hp)) _)

/-- One step of the algorithm, keeping the factor `Π(W) Π'(W)` (Nielsen 2015, Lemma 1.5 (ii),
power form). -/
private theorem step (hodd : Odd N) (hN1 : 1 < N) (hd : 0 < d) (hσ : d * σ 1 N = n * N)
    {S : Finset ℕ} (hS : S ⊆ N.primeFactors) :
    ∃ W T : Finset ℕ, ∃ w : ℕ, W ⊆ N.primeFactors ∧ W.Nonempty ∧ T ⊆ N.primeFactors \ W ∧
      T.card + W.card = S.card + w ∧
      d * σ 1 (∏ p ∈ W, p ^ N.factorization p) * (∏ p ∈ T, p) *
          ((∏ p ∈ W, p) * ∏ p ∈ W, (p - 1)) + 1 ≤
        (d * ∏ p ∈ S, p + 1) ^ (2 ^ (w + W.card)) := by
  classical
  have hN0 : 0 < N := by omega
  have hn := n_pos hN0 hd hσ
  have h2P : ∀ p ∈ N.primeFactors, 2 ≤ p := fun p hp => two_le_of_mem hp
  -- Step A: extend `S` by an initial segment of the remaining primes.
  have hPS : 0 < ∏ p ∈ S, p := prod_pos (fun p hp => by have := h2P p (hS hp); omega)
  have hUS : 0 < ∏ p ∈ S, (p - 1) := prod_sub_one_pos S (fun p hp => h2P p (hS hp))
  have hcS := prod_one_sub_inv_eq (fun p hp => h2P p (hS hp))
  have hcSpos : 0 < ∏ p ∈ S, (1 - 1 / (p : ℚ)) :=
    prod_pos (fun p hp => one_sub_inv_pos (h2P p (hS hp)))
  have hF3 := prod_lt_d_div_n hN1 hd hσ
  rw [← prod_sdiff hS] at hF3
  have hfrac1 : ((d * ∏ p ∈ S, p : ℕ) : ℚ) / ((n * ∏ p ∈ S, (p - 1) : ℕ) : ℚ) =
      ((d : ℚ) / n) / ∏ p ∈ S, (1 - 1 / (p : ℚ)) := by
    rw [hcS]
    have : ((∏ p ∈ S, (p - 1) : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hUS.ne'
    have : ((∏ p ∈ S, p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hPS.ne'
    have : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp
  have hQ : ∏ p ∈ N.primeFactors \ S, (1 - 1 / (p : ℚ)) ≤
      ((d * ∏ p ∈ S, p : ℕ) : ℚ) / ((n * ∏ p ∈ S, (p - 1) : ℕ) : ℚ) := by
    rw [hfrac1, le_div_iff₀ hcSpos]; exact hF3.le
  obtain ⟨S', hS'sub, hS'le, hS'bd⟩ :=
    UpperBound.select (Nat.mul_pos hd hPS) (fun p hp => h2P p (sdiff_subset hp)) hQ
  rw [hfrac1, le_div_iff₀ hcSpos] at hS'le
  have hdisj : Disjoint S S' :=
    disjoint_left.mpr (fun p hpS hpS' => (mem_sdiff.mp (hS'sub hpS')).2 hpS)
  set R := S ∪ S' with hR
  have hRP : R ⊆ N.primeFactors := union_subset hS (fun p hp => sdiff_subset (hS'sub hp))
  have hRlt : ∏ p ∈ R, (1 - 1 / (p : ℚ)) < d / n :=
    lt_of_le_of_ne (by rw [prod_union hdisj, mul_comm]; exact hS'le)
      (prod_ne_d_div_n hodd hN1 hd hσ hRP)
  have hRbd : d * ∏ p ∈ R, p < (d * ∏ p ∈ S, p + 1) ^ (2 ^ S'.card) := by
    rw [prod_union hdisj, ← mul_assoc]; exact hS'bd
  -- Step B: select prime power components among the primes of `R`.
  have h2R : ∀ p ∈ R, 2 ≤ p := fun p hp => h2P p (hRP hp)
  have hPR : 0 < ∏ p ∈ R, p := prod_pos (fun p hp => by have := h2R p hp; omega)
  have hUR : 0 < ∏ p ∈ R, (p - 1) := prod_sub_one_pos R h2R
  have hcR := prod_one_sub_inv_eq h2R
  set d'' := d * ∏ p ∈ R, p with hd''
  set n'' := n * ∏ p ∈ R, (p - 1) with hn''
  have hn''pos : 0 < n'' := Nat.mul_pos hn hUR
  have hd''pos : 0 < d'' := Nat.mul_pos hd hPR
  have hnd'' : n'' < d'' := by
    rw [hcR, div_lt_div_iff₀ (by exact_mod_cast hPR) (by exact_mod_cast hn)] at hRlt
    have : (∏ p ∈ R, (p - 1)) * n < d * ∏ p ∈ R, p := by exact_mod_cast hRlt
    rw [hn'', mul_comm]; exact this
  set f : ℕ → ℕ := fun p => p ^ (N.factorization p + 1) with hf
  have hinj : Set.InjOn f R := by
    intro p hp q hq hpq
    have hp' := Nat.prime_of_mem_primeFactors (hRP hp)
    have hq' := Nat.prime_of_mem_primeFactors (hRP hq)
    have : p ∣ q ^ (N.factorization q + 1) := by
      have h' : f p = f q := hpq
      simp only [hf] at h'
      rw [← h']; exact dvd_pow_self p (Nat.succ_ne_zero _)
    exact (Nat.prime_dvd_prime_iff_eq hp' hq').mp (hp'.dvd_of_dvd_pow this)
  have h2F : ∀ x ∈ R.image f, 2 ≤ x := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
    exact le_trans (h2R p hp) (Nat.le_self_pow (Nat.succ_ne_zero _) p)
  have hFle : ∏ x ∈ R.image f, (1 - 1 / (x : ℚ)) ≤ (n'' : ℚ) / d'' := by
    rw [prod_image hinj]
    refine le_trans (prod_pp_le hN0 hd hσ hRP) (le_of_eq ?_)
    rw [hcR, hn'', hd'']
    have : ((∏ p ∈ R, p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hPR.ne'
    have : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    field_simp
  obtain ⟨G, hGF, hGle, hGbd⟩ := UpperBound.select hn''pos h2F hFle
  set W := R.filter (fun p => f p ∈ G) with hW
  have hWR : W ⊆ R := filter_subset _ _
  have hGW : G = W.image f := by
    ext x
    constructor
    · intro hx
      obtain ⟨p, hp, rfl⟩ := mem_image.mp (hGF hx)
      exact mem_image.mpr ⟨p, mem_filter.mpr ⟨hp, hx⟩, rfl⟩
    · intro hx
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
      exact (mem_filter.mp hp).2
  have hinjW : Set.InjOn f W := hinj.mono (fun x hx => hWR hx)
  have hGcard : G.card = W.card := by rw [hGW]; exact card_image_of_injOn hinjW
  have hGprodQ : ∏ x ∈ G, (1 - 1 / (x : ℚ)) = ∏ p ∈ W, (1 - 1 / ((f p : ℕ) : ℚ)) := by
    rw [hGW]; exact prod_image hinjW
  have hGprodN : ∏ x ∈ G, x = ∏ p ∈ W, f p := by rw [hGW]; exact prod_image hinjW
  have hWne : W.Nonempty := by
    rcases W.eq_empty_or_nonempty with h | h
    · exfalso
      have hG0 : G = ∅ := by rw [hGW, h, image_empty]
      rw [hG0, prod_empty, le_div_iff₀ (by exact_mod_cast hd''pos), one_mul] at hGle
      have : (d'' : ℚ) ≤ n'' := hGle
      have : d'' ≤ n'' := by exact_mod_cast this
      omega
    · exact h
  -- Step C: the new denominator, keeping the factor `Π(W) Π'(W)`.
  have hσV : σ 1 (∏ p ∈ W, p ^ N.factorization p) = ∏ p ∈ W, σ 1 (p ^ N.factorization p) :=
    isMultiplicative_sigma.map_prod _ W (fun p hp q hq hpq =>
      Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors (hRP (hWR hp)))
        (Nat.prime_of_mem_primeFactors (hRP (hWR hq))) hpq)
  have hRsplit : (∏ p ∈ R, (p : ℚ)) = (∏ p ∈ R \ W, (p : ℚ)) * ∏ p ∈ W, (p : ℚ) :=
    (prod_sdiff hWR).symm
  have hcastW : ∏ p ∈ W, ((p - 1 : ℕ) : ℚ) = ∏ p ∈ W, ((p : ℚ) - 1) := by
    exact prod_congr rfl (fun p hp => by
      have := h2R p (hWR hp)
      rw [Nat.cast_sub (by omega), Nat.cast_one])
  have hsig2 : (∏ p ∈ W, ((σ 1 (p ^ N.factorization p) : ℕ) : ℚ)) * ∏ p ∈ W, ((p : ℚ) - 1) =
      (∏ p ∈ W, ((f p : ℕ) : ℚ)) * ∏ p ∈ W, (1 - 1 / ((f p : ℕ) : ℚ)) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl (fun p hp => ?_)
    rw [sigma_mul_sub_one (Nat.prime_of_mem_primeFactors (hRP (hWR hp)))]
    have : ((f p : ℕ) : ℚ) ≠ 0 := by
      have := h2R p (hWR hp)
      have : 0 < f p := by simp only [hf]; positivity
      exact_mod_cast this.ne'
    simp only [hf] at this ⊢
    push_cast at this ⊢
    field_simp
  have hGle' : ∏ p ∈ W, (1 - 1 / ((f p : ℕ) : ℚ)) ≤ (n'' : ℚ) / d'' := hGprodQ ▸ hGle
  have hkey : d * σ 1 (∏ p ∈ W, p ^ N.factorization p) * (∏ p ∈ R \ W, p) *
      ((∏ p ∈ W, p) * ∏ p ∈ W, (p - 1)) ≤ n'' * ∏ p ∈ W, f p := by
    have hd''Q : (d'' : ℚ) = d * ((∏ p ∈ R \ W, (p : ℚ)) * ∏ p ∈ W, (p : ℚ)) := by
      rw [hd'', ← hRsplit]; push_cast; ring
    have hd''0 : (0 : ℚ) < d'' := by exact_mod_cast hd''pos
    have hX0 : (0 : ℚ) ≤ d'' * ∏ p ∈ W, ((f p : ℕ) : ℚ) := by positivity
    have : ((d * σ 1 (∏ p ∈ W, p ^ N.factorization p) * (∏ p ∈ R \ W, p) *
        ((∏ p ∈ W, p) * ∏ p ∈ W, (p - 1)) : ℕ) : ℚ) ≤
        ((n'' * ∏ p ∈ W, f p : ℕ) : ℚ) := by
      rw [hσV]
      push_cast
      rw [hcastW]
      calc (d : ℚ) * (∏ p ∈ W, ((σ 1 (p ^ N.factorization p) : ℕ) : ℚ)) *
              (∏ p ∈ R \ W, (p : ℚ)) * ((∏ p ∈ W, (p : ℚ)) * ∏ p ∈ W, ((p : ℚ) - 1))
          = (d'' : ℚ) * ((∏ p ∈ W, ((σ 1 (p ^ N.factorization p) : ℕ) : ℚ)) *
              ∏ p ∈ W, ((p : ℚ) - 1)) := by rw [hd''Q]; ring
        _ = (d'' : ℚ) * (∏ p ∈ W, ((f p : ℕ) : ℚ)) * ∏ p ∈ W, (1 - 1 / ((f p : ℕ) : ℚ)) := by
            rw [hsig2]; ring
        _ ≤ (d'' : ℚ) * (∏ p ∈ W, ((f p : ℕ) : ℚ)) * ((n'' : ℚ) / d'') :=
            mul_le_mul_of_nonneg_left hGle' hX0
        _ = (n'' : ℚ) * ∏ p ∈ W, ((f p : ℕ) : ℚ) := by field_simp
    exact_mod_cast this
  have hGbd' : n'' * ∏ p ∈ W, f p < (n'' + 1) ^ (2 ^ W.card) := by
    rw [← hGprodN, ← hGcard]; exact hGbd
  refine ⟨W, R \ W, S'.card, hWR.trans hRP, hWne, fun p hp => ?_, ?_, ?_⟩
  · obtain ⟨hpR, hpW⟩ := mem_sdiff.mp hp
    exact mem_sdiff.mpr ⟨hRP hpR, hpW⟩
  · rw [card_sdiff_add_card_eq_card hWR, hR, card_union_of_disjoint hdisj]
  · calc _ ≤ (n'' + 1) ^ (2 ^ W.card) := by omega
      _ ≤ d'' ^ (2 ^ W.card) := Nat.pow_le_pow_left hnd'' _
      _ ≤ ((d * ∏ p ∈ S, p + 1) ^ (2 ^ S'.card)) ^ (2 ^ W.card) :=
          Nat.pow_le_pow_left hRbd.le _
      _ = _ := by rw [← pow_mul, ← pow_add]

end Step

/-- Nielsen, Math. Comp. 84 (2015), Theorem 1.6 in power form, in the form used for
induction: if `N` is odd with `k` distinct prime factors, `d σ(N) = n N` with `d > 0`, and `S`
is a set of prime factors of `N`, then
`d σ(N) Π(X) Π'(X) < (d ∏_{p ∈ S} p + 1)^(2^(2k - |S|))`, where `Π(X)` is the product of the
prime factors of `N` and `Π'(X)` the product of the `p - 1`. -/
theorem general : ∀ (k N d n : ℕ) (S : Finset ℕ), N.primeFactors.card = k → Odd N → 0 < d →
    d * σ 1 N = n * N → S ⊆ N.primeFactors →
    d * σ 1 N * ((∏ p ∈ N.primeFactors, p) * ∏ p ∈ N.primeFactors, (p - 1)) <
      (d * ∏ p ∈ S, p + 1) ^ (2 ^ (2 * k - S.card)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro N d n S hk hodd hd hσ hS
  classical
  have hN0 : 0 < N := hodd.pos
  rcases Nat.lt_or_ge 1 N with hN1 | hN1
  swap
  · have h1 : N = 1 := by omega
    subst h1
    have hS0 : S = ∅ := subset_empty.mp (by simpa using hS)
    subst hS0
    simp at hk
    subst hk
    simp [isMultiplicative_sigma.map_one]
  obtain ⟨W, T, w, hWP, hWne, hTP, hcardT, hbd⟩ := step hodd hN1 hd hσ hS
  set P := N.primeFactors with hP
  set V := ∏ p ∈ W, p ^ N.factorization p with hV
  set U := ∏ p ∈ P \ W, p ^ N.factorization p with hU
  have hNVU : N = V * U := by
    rw [mul_comm, hV, hU, prod_sdiff hWP]
    exact Nat.prod_primeFactors_pow_factorization hN0.ne'
  have hcop : Nat.Coprime V U := by
    apply Nat.coprime_prod_left_iff.mpr
    intro p hp
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    have hpq : p ≠ q := fun h => (mem_sdiff.mp hq).2 (h ▸ hp)
    exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors (hWP hp))
      (Nat.prime_of_mem_primeFactors (sdiff_subset hq)) hpq
  have hU0 : U ≠ 0 := by
    rw [hU]
    exact prod_ne_zero_iff.mpr (fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors (sdiff_subset hp)).ne_zero)
  have hUpf : U.primeFactors = P \ W := by
    ext p
    constructor
    · intro hp
      have hp' := Nat.prime_of_mem_primeFactors hp
      obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp'.prime _).mp
        (Nat.dvd_of_mem_primeFactors hp)
      have hq' := Nat.prime_of_mem_primeFactors (sdiff_subset hq)
      have := (Nat.prime_dvd_prime_iff_eq hp' hq').mp (hp'.dvd_of_dvd_pow hpq)
      exact this ▸ hq
    · intro hp
      have hpP := sdiff_subset hp
      have hp' := Nat.prime_of_mem_primeFactors hpP
      have he : N.factorization p ≠ 0 :=
        (hp'.factorization_pos_of_dvd hN0.ne' (Nat.dvd_of_mem_primeFactors hpP)).ne'
      exact Nat.mem_primeFactors.mpr ⟨hp', dvd_trans (dvd_pow_self p he)
        (dvd_prod_of_mem (fun q => q ^ N.factorization q) hp), hU0⟩
  have hoddU : Odd U := (Nat.odd_mul.mp (hNVU ▸ hodd)).2
  have hσN : σ 1 N = σ 1 V * σ 1 U := by
    rw [hNVU]; exact isMultiplicative_sigma.map_mul_of_coprime hcop
  have hσU : (d * σ 1 V) * σ 1 U = (n * V) * U := by
    calc (d * σ 1 V) * σ 1 U = d * σ 1 N := by rw [hσN]; ring
      _ = n * N := hσ
      _ = (n * V) * U := by rw [hNVU]; ring
  have hV0 : V ≠ 0 := by
    intro h; rw [h, zero_mul] at hNVU; omega
  have hVσ : V ≤ σ 1 V := by
    rw [sigma_one_apply]
    exact single_le_sum (f := id) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self V hV0)
  have hδ : 0 < d * σ 1 V := Nat.mul_pos hd (lt_of_lt_of_le (Nat.pos_of_ne_zero hV0) hVσ)
  have hWcard : W.card ≤ k := hk ▸ card_le_card hWP
  have hWpos : 0 < W.card := card_pos.mpr hWne
  have hPW : (P \ W).card + W.card = k := by rw [card_sdiff_add_card_eq_card hWP, hk]
  have hTcard : T.card ≤ (P \ W).card := card_le_card hTP
  have hUcard : U.primeFactors.card = k - W.card := by rw [hUpf]; omega
  have hIH := IH (k - W.card) (by omega) U (d * σ 1 V) (n * V) T hUcard hoddU hδ hσU
    (hUpf ▸ hTP)
  rw [hUpf] at hIH
  have h2W : ∀ p ∈ W, 2 ≤ p := fun p hp => two_le_of_mem (hWP hp)
  have hMW : 1 ≤ (∏ p ∈ W, p) * ∏ p ∈ W, (p - 1) :=
    Nat.mul_pos (prod_pos (fun p hp => by have := h2W p hp; omega))
      (prod_sub_one_pos W h2W)
  have hglue := glue hIH hMW
  have hsplit : (∏ p ∈ P, p) * ∏ p ∈ P, (p - 1) =
      ((∏ p ∈ P \ W, p) * ∏ p ∈ P \ W, (p - 1)) * ((∏ p ∈ W, p) * ∏ p ∈ W, (p - 1)) := by
    rw [← prod_sdiff hWP (f := fun p => p), ← prod_sdiff hWP (f := fun p => p - 1)]
    ring
  have hexp : w + W.card + (2 * (k - W.card) - T.card) = 2 * k - S.card := by omega
  calc d * σ 1 N * ((∏ p ∈ P, p) * ∏ p ∈ P, (p - 1))
      = d * σ 1 V * σ 1 U * ((∏ p ∈ P \ W, p) * ∏ p ∈ P \ W, (p - 1)) *
          ((∏ p ∈ W, p) * ∏ p ∈ W, (p - 1)) := by rw [hσN, hsplit]; ring
    _ < (d * σ 1 V * (∏ p ∈ T, p) * ((∏ p ∈ W, p) * ∏ p ∈ W, (p - 1)) + 1) ^
          (2 ^ (2 * (k - W.card) - T.card)) := hglue
    _ ≤ ((d * ∏ p ∈ S, p + 1) ^ (2 ^ (w + W.card))) ^ (2 ^ (2 * (k - W.card) - T.card)) :=
        Nat.pow_le_pow_left hbd _
    _ = _ := by rw [← pow_mul, ← pow_add, hexp]

/-- Final arithmetic: `2 ≤ C` and `N (C - 1) C < C^(e + 2)` give `N < 2 C^e`. -/
private theorem lt_two_mul_pow {N C e : ℕ} (hC : 2 ≤ C) (h : N * ((C - 1) * C) < C ^ (e + 2)) :
    N < 2 * C ^ e := by
  obtain ⟨c, rfl⟩ : ∃ c, C = c + 2 := ⟨C - 2, by omega⟩
  have e1 : c + 2 - 1 = c + 1 := by omega
  rw [e1, pow_add] at h
  by_contra hN
  have hN' : 2 * (c + 2) ^ e ≤ N := not_lt.mp hN
  have h1 : 2 * (c + 2) ^ e * ((c + 1) * (c + 2)) ≤ N * ((c + 1) * (c + 2)) :=
    Nat.mul_le_mul_right _ hN'
  have h2 : (c + 2) ^ 2 ≤ 2 * ((c + 1) * (c + 2)) := by nlinarith
  have h3 : (c + 2) ^ e * (c + 2) ^ 2 ≤ (c + 2) ^ e * (2 * ((c + 1) * (c + 2))) :=
    Nat.mul_le_mul_left _ h2
  have h4 : (c + 2) ^ e * (2 * ((c + 1) * (c + 2))) = 2 * (c + 2) ^ e * ((c + 1) * (c + 2)) := by
    ring
  omega

end OddPerfect.UpperBoundSharp

namespace OddPerfect

/-- Nielsen, Math. Comp. 84 (2015), Theorem 1.6, second inequality: an odd `N` with
`σ(N)/N = n/d` and `k` distinct prime factors satisfies `n N Π(X) Π'(X) < (d + 1)^(4^k)`,
where `Π(X)` is the product of the prime factors and `Π'(X)` the product of the `p - 1`. -/
theorem mul_mul_prod_lt_succ_pow_four_pow {N d n : ℕ} (hodd : Odd N) (hd : 0 < d)
    (hσ : d * σ 1 N = n * N) :
    n * N * ((∏ p ∈ N.primeFactors, p) * ∏ p ∈ N.primeFactors, (p - 1)) <
      (d + 1) ^ (4 ^ N.primeFactors.card) := by
  have h := UpperBoundSharp.general _ N d n ∅ rfl hodd hd hσ (Finset.empty_subset _)
  rw [hσ] at h
  have e : 2 ^ (2 * N.primeFactors.card) = 4 ^ N.primeFactors.card := by
    rw [pow_mul]; norm_num
  simpa [e] using h

/-- Nielsen, Math. Comp. 84 (2015), Theorem 1.6 for an odd perfect number:
`2 N Π(X) Π'(X) < 2^(4^k)`. -/
theorem two_mul_mul_prod_lt_two_pow_four_pow {N : ℕ} (h : OddPerfect N) :
    2 * N * ((∏ p ∈ N.primeFactors, p) * ∏ p ∈ N.primeFactors, (p - 1)) <
      2 ^ (4 ^ N.primeFactors.card) := by
  have := mul_mul_prod_lt_succ_pow_four_pow (n := 2) h.odd one_pos
    (by rw [one_mul, h.sigma_eq])
  simpa using this

/-- Nielsen, Math. Comp. 84 (2015), inequality (19) in power form, for an odd perfect number:
Lemma 1.4 (here Cook's lemma) with `a = 2 Π'(X)` and `b = Π(X)` applied to the numbers
`p^(e+1)` gives `2 Π'(X) Π(X) N < (2 Π'(X) + 1)^(2^k)`. -/
theorem two_mul_prod_sub_one_mul_lt {N : ℕ} (h : OddPerfect N) :
    2 * (∏ p ∈ N.primeFactors, (p - 1)) * ((∏ p ∈ N.primeFactors, p) * N) <
      (2 * (∏ p ∈ N.primeFactors, (p - 1)) + 1) ^ (2 ^ N.primeFactors.card) := by
  classical
  have hN1 : N ≠ 1 := by
    rintro rfl
    have := h.sigma_eq
    rw [isMultiplicative_sigma.map_one] at this
    omega
  have hN1' : 1 < N := by have := h.pos; omega
  set P := N.primeFactors with hP
  have h2P : ∀ p ∈ P, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  set f : ℕ → ℕ := fun p => p ^ (N.factorization p + 1) with hf
  have hinj : Set.InjOn f P := by
    intro p hp q hq hpq
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hq' := Nat.prime_of_mem_primeFactors hq
    have : p ∣ q ^ (N.factorization q + 1) := by
      have h' : f p = f q := hpq
      simp only [hf] at h'
      rw [← h']; exact dvd_pow_self p (Nat.succ_ne_zero _)
    exact (Nat.prime_dvd_prime_iff_eq hp' hq').mp (hp'.dvd_of_dvd_pow this)
  set G := P.image f with hG
  have h2G : ∀ x ∈ G, 2 ≤ x := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact le_trans (h2P p hp) (Nat.le_self_pow (Nat.succ_ne_zero _) p)
  have hGcard : G.card = P.card := Finset.card_image_of_injOn hinj
  have hGprod : ∏ x ∈ G, x = (∏ p ∈ P, p) * N := by
    rw [hG, Finset.prod_image hinj]
    have hNp : ∏ p ∈ P, p ^ N.factorization p = N :=
      (Nat.prod_primeFactors_pow_factorization h.ne_zero).symm
    calc ∏ p ∈ P, f p = ∏ p ∈ P, (p * p ^ N.factorization p) :=
          Finset.prod_congr rfl (fun p _ => by simp only [hf]; ring)
      _ = _ := by rw [Finset.prod_mul_distrib, hNp]
  have hprodQ : ∏ x ∈ G, (1 - 1 / (x : ℚ)) = 2 * ∏ p ∈ P, (1 - 1 / (p : ℚ)) := by
    rw [hG, Finset.prod_image hinj]
    have hab : abundancy N = 2 := (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
    rw [abundancy_eq_prod_primeFactors h.ne_zero] at hab
    rw [← hab, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun p hp => by
      simp only [hf]
      rw [UpperBoundSharp.abundancy_mul_one_sub (Nat.prime_of_mem_primeFactors hp)])
  have hEq : ∏ x ∈ G, (1 - 1 / (x : ℚ)) =
      ((2 * ∏ p ∈ P, (p - 1) : ℕ) : ℚ) / ((∏ p ∈ P, p : ℕ) : ℚ) := by
    rw [hprodQ, UpperBoundSharp.prod_one_sub_inv_eq h2P, Nat.cast_mul, Nat.cast_two]
    ring
  have hPne : P.Nonempty := Nat.nonempty_primeFactors.mpr hN1'
  have hGne : G.Nonempty := hPne.image f
  have hmG := G.max'_mem hGne
  have ha : 0 < 2 * ∏ p ∈ P, (p - 1) :=
    Nat.mul_pos two_pos (UpperBoundSharp.prod_sub_one_pos P h2P)
  have hlt : ((2 * ∏ p ∈ P, (p - 1) : ℕ) : ℚ) / ((∏ p ∈ P, p : ℕ) : ℚ) <
      ∏ x ∈ G.erase (G.max' hGne), (1 - 1 / (x : ℚ)) := by
    have hs := Finset.mul_prod_erase G (fun x : ℕ => 1 - 1 / (x : ℚ)) hmG
    rw [← hEq, ← hs]
    have hpos : 0 < ∏ x ∈ G.erase (G.max' hGne), (1 - 1 / (x : ℚ)) :=
      Finset.prod_pos (fun x hx =>
        UpperBoundSharp.one_sub_inv_pos (h2G x (Finset.mem_of_mem_erase hx)))
    have hm2 := h2G _ hmG
    have : (0 : ℚ) < 1 / ((G.max' hGne : ℕ) : ℚ) := by positivity
    nlinarith
  have hc := UpperBound.cook_lemma ha h2G hmG (fun x hx => G.le_max' x hx) hEq.le hlt
  rw [hGprod, hGcard] at hc
  exact hc

/-- Nielsen, Math. Comp. 84 (2015), Corollary 1.7, inequality (18): an odd perfect number
with `k` distinct prime factors is below `2^((2^k - 1)^2)`. -/
theorem lt_two_pow_sq {N : ℕ} (h : OddPerfect N) :
    N < 2 ^ ((2 ^ N.primeFactors.card - 1) ^ 2) := by
  have h19 := two_mul_prod_sub_one_mul_lt h
  have h16 := two_mul_mul_prod_lt_two_pow_four_pow h
  have hAP := two_mul_prod_sub_one_lt_prod h.perfect
  have hU : 0 < ∏ p ∈ N.primeFactors, (p - 1) :=
    UpperBoundSharp.prod_sub_one_pos _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  generalize hk : N.primeFactors.card = k at h19 h16 ⊢
  generalize hUd : ∏ p ∈ N.primeFactors, (p - 1) = U at h19 h16 hAP hU
  generalize hPd : ∏ p ∈ N.primeFactors, p = Pi at h19 h16 hAP
  have hk1 : 1 ≤ k := by have := three_le_card_primeFactors h; omega
  obtain ⟨e, he⟩ : ∃ e, 2 ^ k = e + 2 :=
    ⟨2 ^ k - 2, by have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right two_pos hk1; omega⟩
  have hB2 : 2 ≤ 2 ^ (2 ^ k) := by
    have : 2 ^ 1 ≤ 2 ^ (2 ^ k) := Nat.pow_le_pow_right two_pos (Nat.one_le_two_pow)
    simpa using this
  have hgoal : 2 ^ ((2 ^ k - 1) ^ 2) = 2 * (2 ^ (2 ^ k)) ^ e := by
    have : (2 ^ k - 1) ^ 2 = 1 + 2 ^ k * e := by
      rw [show 2 ^ k - 1 = e + 1 by omega, he]; ring
    rw [this, pow_add, pow_mul]; ring
  have h4 : 2 ^ (4 ^ k) = (2 ^ (2 ^ k)) ^ (e + 2) := by
    rw [← he, ← pow_mul, ← mul_pow]; norm_num
  rw [hgoal]
  rw [h4] at h16
  rw [he] at h19
  rcases le_or_gt (2 * U + 1) (2 ^ (2 ^ k)) with hAB | hAB
  · have hlt : N * ((2 * U + 1 - 1) * (2 * U + 1)) < (2 * U + 1) ^ (e + 2) := by
      have e1 : 2 * U + 1 - 1 = 2 * U := by omega
      rw [e1]
      calc N * (2 * U * (2 * U + 1)) ≤ N * (2 * U * Pi) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hAP)
        _ = 2 * U * (Pi * N) := by ring
        _ < _ := h19
    exact lt_of_lt_of_le (UpperBoundSharp.lt_two_mul_pow (by omega) hlt)
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hAB _))
  · apply UpperBoundSharp.lt_two_mul_pow hB2
    calc N * ((2 ^ (2 ^ k) - 1) * 2 ^ (2 ^ k)) ≤ N * (2 * U * (2 * U + 1)) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul (by omega) hAB.le
      _ ≤ N * (2 * U * Pi) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hAP)
      _ = 2 * N * (Pi * U) := by ring
      _ < _ := h16

end OddPerfect

#print axioms OddPerfect.UpperBoundSharp.general
#print axioms OddPerfect.mul_mul_prod_lt_succ_pow_four_pow
#print axioms OddPerfect.two_mul_mul_prod_lt_two_pow_four_pow
#print axioms OddPerfect.two_mul_prod_sub_one_mul_lt
#print axioms OddPerfect.lt_two_pow_sq
