import OddPerfect.SpecialRankSharp
import OddPerfect.PaletteGlue
import OddPerfect.DefectRules
import OddPerfect.RankTwoPaletteAux

/-!
# The special exponent and the number of prime factors above the special prime

Restricted result; no published source was checked; novelty not verified.

Let `N` be an odd perfect number with special prime `q` and special exponent `a = v_q(N)`, let
every other prime factor have exponent at most `E`, let the rows of the prime factors below `q`
carry at most `β` at `q` in total, and let `k` prime factors exceed `q`. Then the special
exponent is bounded in terms of `E`, `β` and `k` alone (`special_exponent_ladder`). The landed
results cover one and two prime factors above `q`; this module covers every `k`. The family
is not excluded, and the bound grows exponentially with `k`.

* `sigma_sub_mul_pred_lt_card_mul`: for a nonempty finite set `T` of primes, all at least
  `R ≥ 2`, and `M = ∏ p ∈ T, p ^ e p`, `(σ(M) - M) (R - 1) < |T| M`. The proof adds the
  largest element at each step: `∏ p / (p - 1) ≤ (R + |T| - 1) / (R - 1)`.
* `special_exponent_ladder`: let `B 0 = β` and `B (i + 1) = B i + E (B i + 1 + t) - 1`, and
  assume `k ≤ (q - 2) q ^ t`. Add the primes above `q` one at a time, least first among those
  not yet used. If `a > B k`, then after `i` steps the used set `S` carries at most `B i` at
  `q`, together with the rows below `q`, and every `p ∈ S` has `(p + 1) ^ E ≤ q ^ (B i + 1 + t)`.
  Let `R` be the least unused prime and `T` the unused set. If an ordinary row outside `T`
  meets `T`, then `R < q ^ (B i + 1 + t)`. Otherwise `M = ∏ p ∈ T, p ^ v_p(N)` and
  `q ^ (a - b) M` divide `σ(q ^ a) σ(M)`, and the sharp gap `lt_pow_mul_sigma_sub_sharp`
  together with the product bound gives `(q - 2) (R - 1) < q ^ (b + 1) k`, so again
  `R + 1 ≤ q ^ (B i + 1 + t)`. Then `v_q(σ(R ^ v_R(N))) < E (B i + 1 + t)`, which is the step.
  At the end all `k` primes are used and `a ≤ B k`, against the assumption. The closed form
  `E B i + E t + E - 1 = (E + 1) ^ i (E β + E t + E - 1)` gives the statement.
* Palette corollaries (exponents `2` or `4` off `q`, so `E = 4`, `β = 8`):
  `4 a + 4 t + 3 ≤ 5 ^ k (4 t + 35)`, `4 a + 4 k + 3 ≤ 5 ^ k (4 k + 35)`, and `a ≤ 1093` when at
  most three prime factors exceed `q`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ### The product bound -/

private theorem srl_sigma_mul_lt {p e : ℕ} (hp : p.Prime) :
    σ 1 (p ^ e) * (p - 1) < p * p ^ e := by
  have h := rankTwo_sigma_mul_sub_one (k := e) hp
  have h1 : 1 ≤ p := hp.one_lt.le
  have e2 : (p : ℤ) ^ (e + 1) = (p : ℤ) * (p : ℤ) ^ e := pow_succ' _ _
  zify [h1]
  linarith

private theorem srl_le_sigma {M : ℕ} (hM : M ≠ 0) : M ≤ σ 1 M := by
  rw [sigma_one_apply]
  exact Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors_self M hM)

private theorem srl_prod_le {R : ℕ} (hR : 2 ≤ R) (T : Finset ℕ) :
    (∀ p ∈ T, R ≤ p) → (R - 1) * ∏ p ∈ T, p ≤ (R + T.card - 1) * ∏ p ∈ T, (p - 1) := by
  induction T using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s has ih =>
    intro hT
    have hs : ∀ p ∈ s, R ≤ p := fun p hp => hT p (Finset.mem_insert_of_mem hp)
    have hnot : a ∉ s := fun h => lt_irrefl a (has a h)
    have hcard : R + s.card ≤ a := by
      have hsub : s ⊆ Finset.Ico R a := fun x hx => Finset.mem_Ico.mpr ⟨hs x hx, has x hx⟩
      have := Finset.card_le_card hsub
      rw [Nat.card_Ico] at this
      have := hT a (Finset.mem_insert_self a s)
      omega
    rw [Finset.prod_insert hnot, Finset.prod_insert hnot, Finset.card_insert_of_notMem hnot]
    have ih' := ih hs
    set P := ∏ p ∈ s, p
    set Q := ∏ p ∈ s, (p - 1)
    set n := s.card
    obtain ⟨r, rfl⟩ : ∃ r, R = r + 2 := ⟨R - 2, by omega⟩
    obtain ⟨d, rfl⟩ : ∃ d, a = r + 2 + n + d := ⟨a - (r + 2 + n), by omega⟩
    rw [show r + 2 - 1 = r + 1 by omega, show r + 2 + n - 1 = r + 1 + n by omega] at ih'
    rw [show r + 2 - 1 = r + 1 by omega, show r + 2 + (n + 1) - 1 = r + 2 + n by omega,
      show r + 2 + n + d - 1 = r + 1 + n + d by omega]
    have h1 := Nat.mul_le_mul_left (r + 2 + n + d) ih'
    have e1 : (r + 1) * ((r + 2 + n + d) * P) = (r + 2 + n + d) * ((r + 1) * P) := by ring
    have e2 : (r + 2 + n) * ((r + 1 + n + d) * Q) =
        (r + 2 + n + d) * ((r + 1 + n) * Q) + d * Q := by ring
    rw [e1, e2]
    exact h1.trans (Nat.le_add_right _ _)

/-- Product bound. Let `T` be a nonempty finite set of primes, all at least `R ≥ 2`, let
`e : ℕ → ℕ` be any exponents and `M = ∏ p ∈ T, p ^ e p`. Then
`(σ(M) - M) (R - 1) < |T| M`. Pure arithmetic; no perfect number is involved. -/
theorem sigma_sub_mul_pred_lt_card_mul {T : Finset ℕ} {R : ℕ} {e : ℕ → ℕ}
    (hT : ∀ p ∈ T, p.Prime) (hR : 2 ≤ R) (hRT : ∀ p ∈ T, R ≤ p) (hne : T.Nonempty) :
    (σ 1 (∏ p ∈ T, p ^ e p) - ∏ p ∈ T, p ^ e p) * (R - 1) < T.card * ∏ p ∈ T, p ^ e p := by
  set M := ∏ p ∈ T, p ^ e p with hM
  have hcop : (T : Set ℕ).Pairwise (Function.onFun Nat.Coprime fun p => p ^ e p) :=
    fun a ha b hb hab => Nat.coprime_pow_primes _ _ (hT a ha) (hT b hb) hab
  have hσ : σ 1 M = ∏ p ∈ T, σ 1 (p ^ e p) := isMultiplicative_sigma.map_prod _ T hcop
  have h1 : ∏ p ∈ T, (σ 1 (p ^ e p) * (p - 1)) < ∏ p ∈ T, (p * p ^ e p) :=
    Finset.prod_lt_prod_of_nonempty₀
      (fun p hp => Nat.mul_pos (sigma_pos 1 _ (pow_ne_zero _ (hT p hp).ne_zero))
        (by have := (hT p hp).two_le; omega))
      (fun p hp => srl_sigma_mul_lt (hT p hp)) hne
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← hσ] at h1
  have h2 := srl_prod_le hR T hRT
  set P := ∏ p ∈ T, p
  set Q := ∏ p ∈ T, (p - 1)
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hT p hp).ne_zero
  have h3 : σ 1 M * (R - 1) * Q < M * (R + T.card - 1) * Q :=
    calc σ 1 M * (R - 1) * Q = (R - 1) * (σ 1 M * Q) := by ring
      _ < (R - 1) * (P * M) := mul_lt_mul_of_pos_left h1 (by omega)
      _ = M * ((R - 1) * P) := by ring
      _ ≤ M * ((R + T.card - 1) * Q) := Nat.mul_le_mul_left _ h2
      _ = M * (R + T.card - 1) * Q := by ring
  have h4 := lt_of_mul_lt_mul_right h3 (Nat.zero_le Q)
  have hle : M * (R - 1) ≤ σ 1 M * (R - 1) := Nat.mul_le_mul_right _ (srl_le_sigma hM0)
  have e3 : M * (R + T.card - 1) = M * (R - 1) + T.card * M := by
    rw [show R + T.card - 1 = (R - 1) + T.card by omega]
    ring
  rw [Nat.sub_mul]
  omega

/-! ### The ledger and one step of the ladder -/

private theorem srl_succ_pow_le {q P m : ℕ} (hq : q.Prime) (hP : P.Prime) (hqP : q < P)
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

/-- The ledger at an odd prime `r`, split into the rows below `q`, the row of `q`, a set `S` of
prime factors above `q`, and the rest of the prime factors above `q`. -/
private theorem srl_ledger {N q r : ℕ} (h : OddPerfect N) (hr : r.Prime) (hr2 : r ≠ 2)
    (hq : q ∈ N.primeFactors) {S : Finset ℕ} (hS : S ⊆ N.primeFactors.filter (q < ·)) :
    ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p r + sigmaWeight N q r +
      ∑ p ∈ S, sigmaWeight N p r +
      ∑ p ∈ N.primeFactors.filter (q < ·) \ S, sigmaWeight N p r = N.factorization r := by
  have hs := sigmaWeight_sum_eq h.2 hr hr2
  have hrest : N.primeFactors.filter (fun p => ¬ p < q) =
      insert q (N.primeFactors.filter (q < ·)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hp, hpq⟩
      rcases Nat.lt_or_ge q p with h1 | h1
      · exact Or.inr ⟨hp, h1⟩
      · exact Or.inl (by omega)
    · rintro (rfl | ⟨hp, hpq⟩)
      · exact ⟨hq, lt_irrefl _⟩
      · exact ⟨hp, by omega⟩
  rw [← Finset.sum_filter_add_sum_filter_not N.primeFactors (· < q), hrest,
    Finset.sum_insert (by simp), ← Finset.sum_sdiff hS] at hs
  omega

/-- One step of the ladder. `S` is a set of prime factors above `q` whose rows, with the rows
below `q`, carry at most `X < a` at `q`; `R` is the least prime factor above `q` outside `S`.
Then `R + 1 ≤ q ^ (X + 1 + t)`. -/
private theorem srl_step {N q E t k X R : ℕ} {S : Finset ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hq5 : 5 ≤ q)
    (hE : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p ≤ E)
    (hk : (N.primeFactors.filter (q < ·)).card = k) (ht : k ≤ (q - 2) * q ^ t)
    (hS : S ⊆ N.primeFactors.filter (q < ·))
    (hW : ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p q +
      ∑ p ∈ S, sigmaWeight N p q ≤ X)
    (hXa : X < N.factorization q) (hEX : E ≤ X + 1 + t)
    (hSp : ∀ p ∈ S, (p + 1) ^ E ≤ q ^ (X + 1 + t))
    (hR : R ∈ N.primeFactors.filter (q < ·) \ S)
    (hRmin : ∀ r ∈ N.primeFactors.filter (q < ·) \ S, R ≤ r) :
    R + 1 ≤ q ^ (X + 1 + t) := by
  set A := N.primeFactors.filter (q < ·) with hA
  set T := A \ S with hT
  have hqm : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by obtain ⟨j, hj⟩ := hodd; omega)
  have hoddN : ∀ p ∈ N.primeFactors, p % 2 = 1 := fun p hp =>
    Nat.odd_iff.mp (h.1.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
  have hTA : T ⊆ A := Finset.sdiff_subset
  have hTmem : ∀ p ∈ T, p ∈ N.primeFactors ∧ q < p := fun p hp =>
    Finset.mem_filter.mp (hTA hp)
  have hTp : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hTmem p hp).1
  obtain ⟨hRN, hqR⟩ := hTmem R hR
  have hRp := Nat.prime_of_mem_primeFactors hRN
  have hq2 : q ≠ 2 := by omega
  have hexp2 : ∀ p ∈ N.primeFactors, p ≠ q → 2 ≤ N.factorization p := by
    intro p hp hpq
    have hpp := Nat.prime_of_mem_primeFactors hp
    obtain ⟨j, hj⟩ := even_factorization_of_ne h hq hodd hpp hpq
    have := (hpp.dvd_iff_one_le_factorization h.ne_zero).mp (Nat.dvd_of_mem_primeFactors hp)
    omega
  by_cases hfeed : ∃ u ∈ N.primeFactors, u ≠ q ∧ u ∉ T ∧
      ∃ r ∈ T, r ∣ σ 1 (u ^ N.factorization u)
  · -- an ordinary row outside `T` meets `T`
    obtain ⟨u, hu, huq, huT, r, hr, hrd⟩ := hfeed
    have hup := Nat.prime_of_mem_primeFactors hu
    have hσ0 : 0 < σ 1 (u ^ N.factorization u) := sigma_pos 1 _ (pow_ne_zero _ hup.ne_zero)
    have hRr : R ≤ r := hRmin r hr
    have hrσ : r ≤ σ 1 (u ^ N.factorization u) := Nat.le_of_dvd hσ0 hrd
    have h1 := sigma_prime_pow_lt_succ_pow hup (hexp2 u hu huq)
    have h2 : (u + 1) ^ N.factorization u ≤ (u + 1) ^ E :=
      Nat.pow_le_pow_right (by omega) (hE u hu huq)
    have h3 : (u + 1) ^ E ≤ q ^ (X + 1 + t) := by
      rcases Nat.lt_or_ge u q with huq' | huq'
      · exact (Nat.pow_le_pow_left (show u + 1 ≤ q by omega) E).trans
          (Nat.pow_le_pow_right hq.pos hEX)
      · have huS : u ∈ S := by
          by_contra hn
          exact huT (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hu, by omega⟩, hn⟩)
        exact hSp u huS
    omega
  · -- no ordinary row outside `T` meets `T`
    push Not at hfeed
    set a := N.factorization q with ha
    set b := ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p q +
      ∑ p ∈ S, sigmaWeight N p q with hb
    have hba : b < a := by omega
    set M := ∏ p ∈ T, p ^ N.factorization p with hM
    have hcop : (T : Set ℕ).Pairwise
        (Function.onFun Nat.Coprime fun p => p ^ N.factorization p) :=
      fun x hx y hy hxy => Nat.coprime_pow_primes _ _ (hTp x hx) (hTp y hy) hxy
    have hσM : σ 1 M = ∏ p ∈ T, σ 1 (p ^ N.factorization p) :=
      isMultiplicative_sigma.map_prod _ T hcop
    have hσp0 : ∀ p ∈ T, σ 1 (p ^ N.factorization p) ≠ 0 := fun p hp =>
      (sigma_pos 1 _ (pow_ne_zero _ (hTp p hp).ne_zero)).ne'
    have hσM0 : σ 1 M ≠ 0 := by rw [hσM]; exact Finset.prod_ne_zero_iff.mpr hσp0
    have hσq0 : σ 1 (q ^ a) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hq.ne_zero)).ne'
    have hfacM : ∀ r, (σ 1 M).factorization r = ∑ p ∈ T, sigmaWeight N p r := by
      intro r
      rw [hσM, Nat.factorization_prod hσp0, Finsupp.finsetSum_apply]
      rfl
    have hledq := srl_ledger h hq hq2 hqm hS
    rw [sigmaWeight_self hq, ← hA, ← hT] at hledq
    have hqdvd : q ^ (a - b) ∣ σ 1 M := by
      have := Nat.ordProj_dvd (σ 1 M) q
      rwa [hfacM q, show ∑ p ∈ T, sigmaWeight N p q = a - b by omega] at this
    have hMdvd : M ∣ σ 1 (q ^ a) * σ 1 M := by
      refine prod_pow_dvd_of_le_factorization (mul_ne_zero hσq0 hσM0) hTp ?_
      intro r hr
      obtain ⟨hrN, hqr⟩ := hTmem r hr
      have hrp := Nat.prime_of_mem_primeFactors hrN
      have hr2 : r ≠ 2 := by have := hoddN r hrN; omega
      have hled := srl_ledger h hrp hr2 hqm hS
      rw [← hA, ← hT] at hled
      rw [Nat.factorization_mul hσq0 hσM0, Finsupp.add_apply, hfacM r]
      have hz1 : ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p r = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        obtain ⟨hp', hpq⟩ := Finset.mem_filter.mp hp
        refine Nat.factorization_eq_zero_of_not_dvd (hfeed p hp' (by omega) ?_ r hr)
        intro hpT
        have := (hTmem p hpT).2
        omega
      have hz2 : ∑ p ∈ S, sigmaWeight N p r = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        have hpA := Finset.mem_filter.mp (hS hp)
        refine Nat.factorization_eq_zero_of_not_dvd (hfeed p hpA.1 (by omega) ?_ r hr)
        intro hpT
        exact (Finset.mem_sdiff.mp hpT).2 hp
      have e : (σ 1 (q ^ a)).factorization r = sigmaWeight N q r := rfl
      omega
    have hcopq : (q ^ (a - b)).Coprime M :=
      Nat.Coprime.pow_left _ (Nat.Coprime.prod_right fun p hp => Nat.Coprime.pow_right _
        ((Nat.coprime_primes hq (hTp p hp)).mpr (by have := (hTmem p hp).2; omega)))
    have hfull : q ^ (a - b) * M ∣ σ 1 (q ^ a) * σ 1 M :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd hcopq (Dvd.dvd.mul_left hqdvd _) hMdvd
    -- `σ(M) < 2 M`: `M ∣ N` and `σ(M)` is odd
    have hMN : M ∣ N := prod_pow_dvd_of_le_factorization h.ne_zero hTp (fun p _ => le_rfl)
    have hM2le := sigma_le_two_mul_of_dvd h hMN
    have hodd2 : ¬ 2 ∣ σ 1 M := by
      intro h2
      have hpos : 1 ≤ (σ 1 M).factorization 2 :=
        Nat.Prime.factorization_pos_of_dvd Nat.prime_two hσM0 h2
      rw [hfacM] at hpos
      have hs2 := sigmaWeight_sum_two h
      have hq2w : 1 ≤ sigmaWeight N q 2 :=
        le_sigmaWeight_special_of_pow_dvd hq hodd Nat.prime_two
          (by rw [pow_one]; exact Nat.dvd_of_mod_eq_zero (by have := hoddN q hqm; omega))
      have hqT : q ∉ T := fun hqT => lt_irrefl q (hTmem q hqT).2
      have hsub : insert q T ⊆ N.primeFactors :=
        Finset.insert_subset hqm fun p hp => (hTmem p hp).1
      have := Finset.sum_le_sum_of_subset (f := fun p => sigmaWeight N p 2) hsub
      rw [Finset.sum_insert hqT] at this
      omega
    have hM2 : σ 1 M < 2 * M := by
      rcases lt_or_eq_of_le hM2le with h' | h'
      · exact h'
      · exact absurd (h' ▸ dvd_mul_right 2 M) hodd2
    have hgap := lt_pow_mul_sigma_sub_sharp hq hq2 hM2 hba hfull
    have hprod := sigma_sub_mul_pred_lt_card_mul (e := N.factorization) hTp
      (show 2 ≤ R by omega) hRmin ⟨R, hR⟩
    rw [← hM] at hprod
    have hTk : T.card ≤ k := hk ▸ Finset.card_le_card hTA
    have h1 : (q - 2) * (R - 1) * M < q ^ (b + 1) * T.card * M :=
      calc (q - 2) * (R - 1) * M = (R - 1) * ((q - 2) * M) := by ring
        _ ≤ (R - 1) * (q ^ (b + 1) * (σ 1 M - M)) := Nat.mul_le_mul_left _ hgap.le
        _ = q ^ (b + 1) * ((σ 1 M - M) * (R - 1)) := by ring
        _ < q ^ (b + 1) * (T.card * M) := mul_lt_mul_of_pos_left hprod (by positivity)
        _ = q ^ (b + 1) * T.card * M := by ring
    have h2 := lt_of_mul_lt_mul_right h1 (Nat.zero_le M)
    have h3 : q ^ (b + 1) * T.card ≤ q ^ (b + 1) * ((q - 2) * q ^ t) :=
      Nat.mul_le_mul_left _ (hTk.trans ht)
    have h4 : (q - 2) * (R - 1) < (q - 2) * q ^ (b + 1 + t) :=
      calc _ < _ := h2
        _ ≤ _ := h3
        _ = _ := by rw [pow_add]; ring
    have h5 := lt_of_mul_lt_mul_left h4 (Nat.zero_le _)
    have h6 : R ≤ q ^ (b + 1 + t) := by omega
    have h7 := srl_succ_pow_le hq hRp hqR h6
    have h8 : q ^ (b + 1 + t) ≤ q ^ (X + 1 + t) := Nat.pow_le_pow_right hq.pos (by omega)
    omega

/-! ### The ladder recursion -/

/-- The ladder: `B 0 = β`, `B (i + 1) = B i + E (B i + 1 + t) - 1`. -/
private def srlB (E β t : ℕ) : ℕ → ℕ
  | 0 => β
  | i + 1 => srlB E β t i + E * (srlB E β t i + 1 + t) - 1

private theorem srlB_succ (E β t i : ℕ) :
    srlB E β t (i + 1) = srlB E β t i + E * (srlB E β t i + 1 + t) - 1 := rfl

private theorem srlB_succ_ge {E β t : ℕ} (hE : 1 ≤ E) (i : ℕ) :
    srlB E β t i ≤ srlB E β t (i + 1) ∧
      E * (srlB E β t i + 1 + t) ≤ srlB E β t (i + 1) + 1 + t := by
  rw [srlB_succ]
  have : 1 ≤ E * (srlB E β t i + 1 + t) := Nat.mul_pos (by omega) (by omega)
  omega

private theorem srlB_mono {E β t : ℕ} (hE : 1 ≤ E) : Monotone (srlB E β t) :=
  monotone_nat_of_le_succ fun i => (srlB_succ_ge hE i).1

private theorem srlB_closed {E β t : ℕ} (hE : 1 ≤ E) (i : ℕ) :
    E * srlB E β t i + E * t + E = (E + 1) ^ i * (E * β + E * t + E - 1) + 1 := by
  induction i with
  | zero =>
    show E * β + E * t + E = (E + 1) ^ 0 * (E * β + E * t + E - 1) + 1
    rw [pow_zero, one_mul]
    omega
  | succ i ih =>
    rw [srlB_succ]
    set c := srlB E β t i
    set C := (E + 1) ^ i * (E * β + E * t + E - 1) with hC
    have hY : E * (c + 1 + t) = C + 1 := by rw [← ih]; ring
    rw [hY, show c + (C + 1) - 1 = c + C by omega, pow_succ]
    have e : (E + 1) ^ i * (E + 1) * (E * β + E * t + E - 1) = E * C + C := by rw [hC]; ring
    rw [e]
    nlinarith [ih]

/-! ### The main theorem -/

/-- The special exponent ladder. Let `N` be an odd perfect number with special prime `q`
(`v_q(N)` odd), let every other prime factor have exponent at most `E`, let the rows of the
prime factors below `q` carry at most `β ≥ E - 1` at `q` in total, and let `k` prime factors
of `N` exceed `q`, with `k ≤ (q - 2) q ^ t`. Then
`E v_q(N) + E t + E - 1 ≤ (E + 1) ^ k (E β + E t + E - 1)`. Restricted result; no published
source was checked; novelty not verified. -/
theorem special_exponent_ladder {N q E β t k : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hE : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p ≤ E)
    (hβ : ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p q ≤ β) (hEβ : E ≤ β + 1)
    (hk : (N.primeFactors.filter (q < ·)).card = k) (ht : k ≤ (q - 2) * q ^ t) :
    E * N.factorization q + E * t + E - 1 ≤ (E + 1) ^ k * (E * β + E * t + E - 1) := by
  rcases Nat.eq_zero_or_pos E with rfl | hE1
  · simp
  set a := N.factorization q with ha
  set A := N.primeFactors.filter (q < ·) with hA
  have hqm : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by obtain ⟨j, hj⟩ := hodd; omega)
  have hoddN : ∀ p ∈ N.primeFactors, p % 2 = 1 := fun p hp =>
    Nat.odd_iff.mp (h.1.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
  have hq5 : 5 ≤ q := by
    have h4 := (special_mod_four h hq hodd).1
    have := hq.two_le
    omega
  have hq2 : q ≠ 2 := by omega
  have hclosed := srlB_closed hE1 (β := β) (t := t) k
  by_contra hcon
  have hBa : srlB E β t k < a := by
    by_contra hle
    push Not at hle
    apply hcon
    have : E * a ≤ E * srlB E β t k := Nat.mul_le_mul_left _ hle
    omega
  have hinv : ∀ i ≤ k, ∃ S ⊆ A, S.card = i ∧
      ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p q + ∑ p ∈ S, sigmaWeight N p q ≤
        srlB E β t i ∧ ∀ p ∈ S, (p + 1) ^ E ≤ q ^ (srlB E β t i + 1 + t) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨∅, Finset.empty_subset _, rfl, ?_, by simp⟩
      rw [Finset.sum_empty, add_zero]
      exact hβ
    | succ i ih =>
      intro hi
      obtain ⟨S, hSA, hSc, hSW, hSp⟩ := ih (by omega)
      have hne : (A \ S).Nonempty := Finset.sdiff_nonempty_of_card_lt_card (by omega)
      have hR := Finset.min'_mem _ hne
      have hRmin : ∀ r ∈ A \ S, (A \ S).min' hne ≤ r := fun r hr => Finset.min'_le _ r hr
      set R := (A \ S).min' hne with hRdef
      have hBi : srlB E β t i ≤ srlB E β t k := srlB_mono hE1 (by omega)
      have hβi : β ≤ srlB E β t i := srlB_mono hE1 (Nat.zero_le i)
      have hstep := srl_step h hq hodd hq5 hE hk ht hSA hSW (by omega) (by omega) hSp hR hRmin
      obtain ⟨hRA, hRS⟩ := Finset.mem_sdiff.mp hR
      obtain ⟨hRN, hqR⟩ := Finset.mem_filter.mp hRA
      have hRp := Nat.prime_of_mem_primeFactors hRN
      have heR2 : 2 ≤ N.factorization R := by
        obtain ⟨j, hj⟩ := even_factorization_of_ne h hq hodd hRp (by omega)
        have := (hRp.dvd_iff_one_le_factorization h.ne_zero).mp (Nat.dvd_of_mem_primeFactors hRN)
        omega
      have heRE : N.factorization R ≤ E := hE R hRN (by omega)
      have hσlt := sigma_prime_pow_lt_succ_pow hRp heR2
      have hσ0 : 0 < σ 1 (R ^ N.factorization R) := sigma_pos 1 _ (pow_ne_zero _ hRp.ne_zero)
      have hqw : q ^ sigmaWeight N R q ≤ σ 1 (R ^ N.factorization R) :=
        Nat.le_of_dvd hσ0 (Nat.ordProj_dvd _ _)
      have hpow : (R + 1) ^ E ≤ q ^ ((srlB E β t i + 1 + t) * E) := by
        rw [pow_mul]
        exact Nat.pow_le_pow_left hstep E
      have hRE : (R + 1) ^ N.factorization R ≤ (R + 1) ^ E :=
        Nat.pow_le_pow_right (by omega) heRE
      have hw : sigmaWeight N R q < (srlB E β t i + 1 + t) * E :=
        (Nat.pow_lt_pow_iff_right hq.one_lt).mp (by omega)
      have hsg := srlB_succ_ge hE1 (β := β) (t := t) i
      have hcomm : (srlB E β t i + 1 + t) * E = E * (srlB E β t i + 1 + t) := Nat.mul_comm _ _
      refine ⟨insert R S, Finset.insert_subset hRA hSA, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hRS, hSc]
      · rw [Finset.sum_insert hRS, srlB_succ]
        omega
      · intro p hp
        rcases Finset.mem_insert.mp hp with hpR | hp
        · rw [hpR]
          exact hpow.trans (Nat.pow_le_pow_right hq.pos (by omega))
        · exact (hSp p hp).trans (Nat.pow_le_pow_right hq.pos (by omega))
  obtain ⟨S, hSA, hSc, hSW, -⟩ := hinv k le_rfl
  have hSeq : S = A := Finset.eq_of_subset_of_card_le hSA (by rw [hk, hSc])
  have hled := srl_ledger h hq hq2 hqm hSA
  rw [sigmaWeight_self hq, hSeq, Finset.sdiff_self, Finset.sum_empty] at hled
  rw [hSeq] at hSW
  omega

/-! ### Palette corollaries -/

/-- The ladder in the palette family: every prime factor other than the special prime `q` has
exponent `2` or `4`, and `k ≤ (q - 2) q ^ t` prime factors exceed `q`. Then
`4 v_q(N) + 4 t + 3 ≤ 5 ^ k (4 t + 35)`. Restricted family result; no published source was
checked; novelty not verified. -/
theorem special_exponent_ladder_palette {N q t k : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4)
    (hk : (N.primeFactors.filter (q < ·)).card = k) (ht : k ≤ (q - 2) * q ^ t) :
    4 * N.factorization q + 4 * t + 3 ≤ 5 ^ k * (4 * t + 35) := by
  have H := special_exponent_ladder (E := 4) (β := 8) h hq hodd
    (fun p hp hpq => by rcases hexp p hp hpq with h' | h' <;> omega)
    (sum_sigmaWeight_below_special_le_eight h hq hexp) (by norm_num) hk ht
  rw [show 4 * N.factorization q + 4 * t + 4 - 1 = 4 * N.factorization q + 4 * t + 3 by omega,
    show 4 * 8 + 4 * t + 4 - 1 = 4 * t + 35 by omega] at H
  exact H

/-- The palette ladder with `t = k`, valid for every number `k` of prime factors above the
special prime: `4 v_q(N) + 4 k + 3 ≤ 5 ^ k (4 k + 35)`. Restricted family result; no published
source was checked; novelty not verified. -/
theorem special_exponent_ladder_palette_card {N q k : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4)
    (hk : (N.primeFactors.filter (q < ·)).card = k) :
    4 * N.factorization q + 4 * k + 3 ≤ 5 ^ k * (4 * k + 35) := by
  have hq5 : 5 ≤ q := by
    have h4 := (special_mod_four h hq hodd).1
    have := hq.two_le
    omega
  have h1 : k < q ^ k := Nat.lt_pow_self (by omega)
  have h2 : q ^ k ≤ (q - 2) * q ^ k := Nat.le_mul_of_pos_left _ (by omega)
  exact special_exponent_ladder_palette h hq hodd hexp hk (by omega)

/-- At most three prime factors above the special prime in the palette family: then
`v_q(N) ≤ 1093`. Restricted family result: the family is not excluded; no published source
was checked; novelty not verified. -/
theorem special_exponent_le_1093_of_three_above {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4)
    (h3 : (N.primeFactors.filter (q < ·)).card ≤ 3) :
    N.factorization q ≤ 1093 := by
  have hq5 : 5 ≤ q := by
    have h4 := (special_mod_four h hq hodd).1
    have := hq.two_le
    omega
  have H := special_exponent_ladder_palette (t := 0) h hq hodd hexp rfl
    (by rw [pow_zero, mul_one]; omega)
  have h5 : 5 ^ (N.primeFactors.filter (q < ·)).card ≤ 5 ^ 3 :=
    Nat.pow_le_pow_right (by norm_num) h3
  omega

end OddPerfect


#print axioms OddPerfect.sigma_sub_mul_pred_lt_card_mul
#print axioms OddPerfect.special_exponent_ladder
#print axioms OddPerfect.special_exponent_ladder_palette
#print axioms OddPerfect.special_exponent_ladder_palette_card
#print axioms OddPerfect.special_exponent_le_1093_of_three_above
