import OddPerfect.Abundancy
import OddPerfect.Euler
import OddPerfect.Seed.ThreeFree
import OddPerfect.Seed.Example

/-!
# Restrained odd perfect numbers are divisible by 3

Let `N` be an odd perfect number with special prime `q`, and suppose every other prime
factor except possibly one prime `r` has exponent exactly 2 (Ochem and Zelinsky call such
numbers restrained when `r` has exponent above 2). We show `3 ∣ N`. Assume `3 ∤ N`.

* `q ≡ 1 (mod 12)`, so `q ≥ 13`: Euler gives `q ≡ 1 (mod 4)`, and `q ≡ 2 (mod 3)` would
  put `3 ∣ 1 + q ∣ σ(q^k)`.
* For an ordinary prime `p` (exponent 2, `p ≠ q, r`) every prime factor of
  `σ(p^2) = 1 + p + p^2` is `q` or `r`, so `σ(p^2) = q^a r^b`, with `a` and `b` not both
  even because `1 + p + p^2` lies strictly between consecutive squares.

Case 1: `r` divides no `σ(p^2)`. Then `σ(p^2) = q^a` with `a` odd, distinct ordinary primes
have exponents differing by at least 2, so `p < p'` forces `13 p ≤ p'`. An induction on the
least element bounds the ordinary part of the abundancy by `7/5`, and the abundancy of `N`
is below `13/12 * 5/4 * 7/5 = 91/48 < 2`.

Case 2: `r ∣ σ(p^2)` for some ordinary `p`. Then `r ≡ 1 (mod 3)` and `r ≥ 7`. The map
`p ↦ (a, b)` is injective, and `(p + 1)^2 > 13^a r^b`, in the spirit of the pair counting
of Ochem and Zelinsky (arXiv:2607.19746, Section 2). Each pair `(a, b)` with `a, b < 5`
is bounded through `p ≥ max(floor, ⌊√(13^a R^b)⌋)`, and the remaining pairs by a geometric
tail with `∏ (1 + x_i) ≤ 1 / (1 - ∑ x_i)`. If `r ≥ 31` this works with `R = 31` and the
floor `p ≥ 5`. If `r < 31` then `p = 5` and `p = 11` are impossible: since `q ≡ 1 (mod 4)`,
the prime `31` would have to be `r`, and `7` and `19` would both have to be `r`. So
`p ≥ 17`, which suffices with `R = 7`. The proof uses only elementary size bounds, with no
result on `x^2 + x + 1 = y^n` and no computer search.
-/


open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

private theorem step_ineq {a : ℕ} (ha : 5 ≤ a) :
    ((a : ℚ) ^ 2 + a + 1) / a ^ 2 * (1 + 2 / ((13 * a : ℕ) : ℚ)) ≤ 1 + 2 / (a : ℚ) := by
  have ha' : (5 : ℚ) ≤ a := by exact_mod_cast ha
  push_cast
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h0 : (0 : ℚ) < a := by linarith
  field_simp
  nlinarith [mul_pos h0 h0]

private theorem prod_sep_le (S : Finset ℕ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x < y → 13 * x ≤ y) :
    ∀ m : ℕ, 5 ≤ m → (∀ x ∈ S, m ≤ x) →
      ∏ x ∈ S, ((x : ℚ) ^ 2 + x + 1) / x ^ 2 ≤ 1 + 2 / (m : ℚ) := by
  induction S using Finset.induction_on_min with
  | empty => intro m hm _; simp; positivity
  | insert a s ha ih =>
    intro m hm hle
    have hsep' : ∀ x ∈ s, ∀ y ∈ s, x < y → 13 * x ≤ y := fun x hx y hy hxy =>
      hsep x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
    have ham : m ≤ a := hle a (Finset.mem_insert_self a s)
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [Finset.prod_insert has]
    have hs := ih hsep' (13 * a) (by omega) fun x hx =>
      hsep a (Finset.mem_insert_self a s) x (Finset.mem_insert_of_mem hx) (ha x hx)
    have hm' : (5 : ℚ) ≤ m := by exact_mod_cast hm
    have ham' : (m : ℚ) ≤ a := by exact_mod_cast ham
    calc _ ≤ ((a : ℚ) ^ 2 + a + 1) / a ^ 2 * (1 + 2 / ((13 * a : ℕ) : ℚ)) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ 1 + 2 / (a : ℚ) := step_ineq (by omega)
      _ ≤ 1 + 2 / (m : ℚ) := by
          gcongr


private theorem sigma_sq {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 2) = 1 + p + p ^ 2 := by
  simp [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]

/-- A value `1 + p + p^2` that is a power of `q` is an odd power. -/
private theorem odd_of_eq_pow {p q a : ℕ} (hp : 0 < p) (h : 1 + p + p ^ 2 = q ^ a) : Odd a := by
  rcases Nat.even_or_odd a with ⟨b, rfl⟩ | ho
  · exfalso
    rw [← two_mul, pow_mul'] at h
    have h1 : p ^ 2 < (q ^ b) ^ 2 := by rw [← h]; omega
    have h2 : (q ^ b) ^ 2 < (p + 1) ^ 2 := by rw [← h]; nlinarith
    have := (Nat.pow_lt_pow_iff_left two_ne_zero).mp h1
    have := (Nat.pow_lt_pow_iff_left two_ne_zero).mp h2
    omega
  · exact ho

/-- Shape of the divisor sum of an ordinary square when `r` is not a target. -/
private theorem shape {N q r p : ℕ} (h : OddPerfect N)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) (h3 : ¬ 3 ∣ N)
    (hp : p ∈ N.primeFactors) (hpq : p ≠ q) (hpr : p ≠ r) (hrS : ¬ r ∣ σ 1 (p ^ 2)) :
    ∃ a, Odd a ∧ 1 + p + p ^ 2 = q ^ a := by
  have hp' := Nat.prime_of_mem_primeFactors hp
  have he := hsq p hp hpq hpr
  have hne : 1 + p + p ^ 2 ≠ 0 := by positivity
  have key : ∀ {d}, Nat.Prime d → d ∣ 1 + p + p ^ 2 → d = q := by
    intro d hd hdd
    rw [← sigma_sq hp'] at hdd
    obtain ⟨-, hdN, -, -, hd2⟩ := OPNThreeFree.exact_square_transfer h.perfect h3 hp' he hd hdd
    by_contra hdq
    have hdr : d ≠ r := by rintro rfl; exact hrS hdd
    exact hd2 (hsq d (Nat.mem_primeFactors.mpr ⟨hd, hdN, h.ne_zero⟩) hdq hdr)
  have := Nat.eq_prime_pow_of_unique_prime_dvd hne key
  exact ⟨_, odd_of_eq_pow hp'.pos this, this⟩


/-- Two powers of `q ≥ 13` with odd exponents, both values of `1 + x + x^2`, force a
factor 13 between the inputs. -/
private theorem sep {p p' q a a' : ℕ} (hq : 13 ≤ q) (ha : Odd a) (ha' : Odd a')
    (h : 1 + p + p ^ 2 = q ^ a) (h' : 1 + p' + p' ^ 2 = q ^ a') (hlt : p < p') :
    13 * p ≤ p' := by
  have hlt' : q ^ a < q ^ a' := by
    rw [← h, ← h']; nlinarith
  have haa : a < a' := (pow_lt_pow_iff_right₀ (by omega)).mp hlt'
  have ha2 : a + 2 ≤ a' := by
    obtain ⟨i, rfl⟩ := ha; obtain ⟨j, rfl⟩ := ha'; omega
  have hle : q ^ a * q ^ 2 ≤ q ^ a' := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) ha2
  rw [← h, ← h'] at hle
  have hq2 : 169 ≤ q ^ 2 := by nlinarith
  have : (1 + p + p ^ 2) * 169 ≤ 1 + p' + p' ^ 2 :=
    le_trans (Nat.mul_le_mul_left _ hq2) hle
  by_contra hc
  rw [not_le] at hc
  nlinarith

private theorem five_le {N p : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N)
    (hp : p ∈ N.primeFactors) : 5 ≤ p := by
  obtain ⟨hpp, hpN, -⟩ := Nat.mem_primeFactors.mp hp
  by_contra hc
  interval_cases p
  · exact absurd hpp (by norm_num)
  · exact absurd hpp (by norm_num)
  · exact h.not_two_dvd hpN
  · exact h3 hpN
  · exact absurd hpp (by norm_num)

private theorem abundancy_nonneg (n : ℕ) : 0 ≤ abundancy n := by
  unfold abundancy; positivity

private theorem div_pred_le {p m : ℕ} (hm : 2 ≤ m) (hp : m ≤ p) :
    (p : ℚ) / (p - 1) ≤ (m : ℚ) / (m - 1) := by
  have hm' : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hp' : (m : ℚ) ≤ p := by exact_mod_cast hp
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith


/-- Without the factor 3, the special prime is `1` modulo 4 and modulo 3. -/
private theorem q_mod {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (h3 : ¬ 3 ∣ N) : q % 4 = 1 ∧ q % 3 = 1 := by
  have hqT : q ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, Nat.dvd_of_factorization_pos hodd.pos.ne', h.ne_zero⟩
  have hq4 : q % 4 = 1 := by
    obtain ⟨q', hq', -, hq4, hk, -⟩ := exists_special_prime h
    have := (existsUnique_odd_exponent h).unique ⟨hq, hodd⟩ ⟨hq', Nat.odd_iff.mpr (by omega)⟩
    rw [this]; exact hq4
  have hq3 : q % 3 = 1 := by
    have h0 : q % 3 ≠ 0 := fun h0 =>
      h3 ((Nat.dvd_of_mod_eq_zero h0).trans (Nat.dvd_of_mem_primeFactors hqT))
    have h2 : q % 3 ≠ 2 := by
      intro h2
      have hd : σ 1 (q ^ 1) ∣ σ 1 (q ^ N.factorization q) :=
        OPNExample.sigma_prime_pow_dvd hq (by
          obtain ⟨j, hj⟩ := hodd; exact ⟨j + 1, by omega⟩)
      have h1 : σ 1 (q ^ 1) = 1 + q := by
        rw [sigma_one_apply_prime_pow hq]; simp [Finset.sum_range_succ]
      have h3q : 3 ∣ σ 1 (q ^ 1) := by rw [h1]; omega
      have := (h3q.trans hd).trans (OPNStarter.component_sigma_dvd h.perfect hq rfl)
      exact h3 ((Nat.Coprime.dvd_of_dvd_mul_left (by decide) this))
    omega
  exact ⟨hq4, hq3⟩

private theorem false_of_core {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) (h3 : ¬ 3 ∣ N)
    (hrS : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → ¬ r ∣ σ 1 (p ^ 2)) : False := by
  have hN0 := h.ne_zero
  have hqT : q ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, Nat.dvd_of_factorization_pos hodd.pos.ne', hN0⟩
  obtain ⟨hq4, hq3⟩ := q_mod h hq hodd h3
  have hq13 : 13 ≤ q := by have := hq.two_le; omega
  -- the ordinary square primes and their divisor sums
  set S := (N.primeFactors.erase q).erase r with hSdef
  have hmemS : ∀ {x}, x ∈ S → x ∈ N.primeFactors ∧ x ≠ q ∧ x ≠ r := by
    intro x hx
    rw [hSdef, Finset.mem_erase, Finset.mem_erase] at hx
    exact ⟨hx.2.2, hx.2.1, hx.1⟩
  have hshape : ∀ x ∈ S, ∃ a, Odd a ∧ 1 + x + x ^ 2 = q ^ a := fun x hx => by
    obtain ⟨hxT, hxq, hxr⟩ := hmemS hx
    exact shape h hsq h3 hxT hxq hxr (hrS x hxT hxq hxr)
  have hsep : ∀ x ∈ S, ∀ y ∈ S, x < y → 13 * x ≤ y := by
    intro x hx y hy hxy
    obtain ⟨a, ha, hxa⟩ := hshape x hx
    obtain ⟨b, hb, hyb⟩ := hshape y hy
    exact sep hq13 ha hb hxa hyb hxy
  -- abundancy bookkeeping
  have hab := (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
  rw [abundancy_eq_prod_primeFactors hN0, ← Finset.mul_prod_erase _ _ hqT] at hab
  have hSprod : ∏ x ∈ S, abundancy (x ^ N.factorization x) ≤ 7 / 5 := by
    have heq : ∏ x ∈ S, abundancy (x ^ N.factorization x) =
        ∏ x ∈ S, ((x : ℚ) ^ 2 + x + 1) / x ^ 2 := by
      refine Finset.prod_congr rfl fun x hx => ?_
      obtain ⟨hxT, hxq, hxr⟩ := hmemS hx
      have hx' := Nat.prime_of_mem_primeFactors hxT
      have hx0 : (x : ℚ) ≠ 0 := by exact_mod_cast hx'.ne_zero
      rw [hsq x hxT hxq hxr, abundancy_prime_pow hx']
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      field_simp
      ring
    rw [heq]
    have := prod_sep_le S hsep 5 le_rfl fun x hx => five_le h h3 (hmemS hx).1
    norm_num at this ⊢
    linarith
  have hrest : ∏ x ∈ N.primeFactors.erase q, abundancy (x ^ N.factorization x) ≤ 7 / 4 := by
    by_cases hrT : r ∈ N.primeFactors.erase q
    · rw [← Finset.mul_prod_erase _ _ hrT]
      have hr5 := five_le h h3 (Finset.mem_of_mem_erase hrT)
      have hr' := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hrT)
      have hlt := abundancy_prime_pow_lt hr' (N.factorization r)
      have hle := div_pred_le (by norm_num) hr5
      have h0 : 0 ≤ abundancy (r ^ N.factorization r) := abundancy_nonneg _
      norm_num at hle
      nlinarith
    · have hS' : S = N.primeFactors.erase q := by rw [hSdef, Finset.erase_eq_of_notMem hrT]
      rw [← hS']
      linarith
  have hlt := abundancy_prime_pow_lt hq (N.factorization q)
  have hle := div_pred_le (by norm_num) hq13
  have h0 : 0 ≤ abundancy (q ^ N.factorization q) := abundancy_nonneg _
  have h0' : 0 ≤ ∏ x ∈ N.primeFactors.erase q, abundancy (x ^ N.factorization x) :=
    Finset.prod_nonneg fun _ _ => abundancy_nonneg _
  norm_num at hle
  nlinarith


/-- The abundancy `σ(s^2)/s^2` of an exact square, as a rational function of `s`. -/
private def fval (s : ℕ) : ℚ := ((s : ℚ) ^ 2 + s + 1) / s ^ 2

private theorem prod_one_add_mul_le {ι : Type*} [DecidableEq ι] (T : Finset ι) (x : ι → ℚ)
    (hx : ∀ i ∈ T, 0 ≤ x i) : (∏ i ∈ T, (1 + x i)) * (1 - ∑ i ∈ T, x i) ≤ 1 := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hxa := hx a (Finset.mem_insert_self a s)
    have hs := ih fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hP : 0 ≤ ∏ i ∈ s, (1 + x i) :=
      Finset.prod_nonneg fun i hi => by linarith [hx i (Finset.mem_insert_of_mem hi)]
    have hsum : 0 ≤ ∑ i ∈ s, x i :=
      Finset.sum_nonneg fun i hi => hx i (Finset.mem_insert_of_mem hi)
    nlinarith [mul_nonneg hP (add_nonneg (mul_nonneg hxa hxa) (mul_nonneg hxa hsum))]

private theorem tail_sum_le (T : Finset (ℕ × ℕ)) (M : ℕ) {α β : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hT : ∀ t ∈ T, M ≤ t.1 ∨ M ≤ t.2) :
    ∑ t ∈ T, α ^ t.1 * β ^ t.2 ≤ (α ^ M + β ^ M) / ((1 - α) * (1 - β)) := by
  set Kb := T.sup (fun t => max t.1 t.2) + 1
  have hK : ∀ t ∈ T, t.1 < Kb ∧ t.2 < Kb := fun t ht => by
    have := Finset.le_sup (f := fun t => max t.1 t.2) ht
    omega
  have hgα : ∑ i ∈ Finset.Ico M Kb, α ^ i ≤ α ^ M / (1 - α) :=
    geom_sum_Ico_le_of_lt_one hα0 hα1
  have hgβ : ∑ i ∈ Finset.Ico M Kb, β ^ i ≤ β ^ M / (1 - β) :=
    geom_sum_Ico_le_of_lt_one hβ0 hβ1
  have hrα : ∑ i ∈ Finset.range Kb, α ^ i ≤ 1 / (1 - α) := by
    have := geom_sum_Ico_le_of_lt_one (x := α) (m := 0) (n := Kb) hα0 hα1
    rwa [← Finset.range_eq_Ico, pow_zero] at this
  have hrβ : ∑ i ∈ Finset.range Kb, β ^ i ≤ 1 / (1 - β) := by
    have := geom_sum_Ico_le_of_lt_one (x := β) (m := 0) (n := Kb) hβ0 hβ1
    rwa [← Finset.range_eq_Ico, pow_zero] at this
  have hnn : ∀ t : ℕ × ℕ, 0 ≤ α ^ t.1 * β ^ t.2 := fun t => by positivity
  have hA : ∑ t ∈ T.filter (fun t => M ≤ t.1), α ^ t.1 * β ^ t.2 ≤
      α ^ M / (1 - α) * (1 / (1 - β)) := by
    calc _ ≤ ∑ t ∈ Finset.Ico M Kb ×ˢ Finset.range Kb, α ^ t.1 * β ^ t.2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun t _ _ => hnn t)
          intro t ht
          rw [Finset.mem_filter] at ht
          have := hK t ht.1
          simp only [Finset.mem_product, Finset.mem_Ico, Finset.mem_range]
          omega
      _ = (∑ i ∈ Finset.Ico M Kb, α ^ i) * ∑ j ∈ Finset.range Kb, β ^ j := by
          rw [Finset.sum_mul_sum, Finset.sum_product]
      _ ≤ _ := mul_le_mul hgα hrβ (Finset.sum_nonneg fun _ _ => by positivity)
          (by have : 0 < 1 - α := by linarith
              positivity)
  have hB : ∑ t ∈ T.filter (fun t => ¬ M ≤ t.1), α ^ t.1 * β ^ t.2 ≤
      1 / (1 - α) * (β ^ M / (1 - β)) := by
    calc _ ≤ ∑ t ∈ Finset.range Kb ×ˢ Finset.Ico M Kb, α ^ t.1 * β ^ t.2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun t _ _ => hnn t)
          intro t ht
          rw [Finset.mem_filter] at ht
          have := hK t ht.1
          have := hT t ht.1
          simp only [Finset.mem_product, Finset.mem_Ico, Finset.mem_range]
          omega
      _ = (∑ i ∈ Finset.range Kb, α ^ i) * ∑ j ∈ Finset.Ico M Kb, β ^ j := by
          rw [Finset.sum_mul_sum, Finset.sum_product]
      _ ≤ _ := mul_le_mul hrα hgβ (Finset.sum_nonneg fun _ _ => by positivity)
          (by have : 0 < 1 - α := by linarith
              positivity)
  rw [← Finset.sum_filter_add_sum_filter_not T (fun t => M ≤ t.1)]
  have h1 : 0 < 1 - α := by linarith
  have h2 : 0 < 1 - β := by linarith
  have : α ^ M / (1 - α) * (1 / (1 - β)) + 1 / (1 - α) * (β ^ M / (1 - β)) =
      (α ^ M + β ^ M) / ((1 - α) * (1 - β)) := by
    field_simp
  linarith


/-- Product of the per-pair bounds over the admissible pairs in the box `[0, M)²`. -/
private def boxProd (Q R fl M : ℕ) : ℚ :=
  ∏ t ∈ (Finset.range M ×ˢ Finset.range M).filter (fun t => ¬ (Even t.1 ∧ Even t.2)),
    fval (max fl (Nat.sqrt (Q ^ t.1 * R ^ t.2)))

private theorem fval_anti {m s : ℕ} (hm : 1 ≤ m) (h : m ≤ s) : fval s ≤ fval m := by
  have hm' : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have h' : (m : ℚ) ≤ s := by exact_mod_cast h
  have hm0 : (0 : ℚ) < m := by linarith
  have hs0 : (0 : ℚ) < s := by linarith
  unfold fval
  rw [div_le_div_iff₀ (pow_pos hs0 2) (pow_pos hm0 2)]
  nlinarith [mul_le_mul h' h' (by positivity) (by positivity), mul_nonneg (sub_nonneg.mpr h')
    (mul_nonneg (by positivity : (0 : ℚ) ≤ m) (by positivity : (0 : ℚ) ≤ s))]

private theorem one_le_fval {s : ℕ} (hs : 1 ≤ s) : 1 ≤ fval s := by
  have hs' : (1 : ℚ) ≤ s := by exact_mod_cast hs
  unfold fval
  rw [le_div_iff₀ (pow_pos (by linarith) 2)]
  nlinarith

private theorem fval_sub_le {s : ℕ} (hs : 3 ≤ s) : fval s - 1 ≤ 2 / ((s : ℚ) + 1) := by
  have hs' : (3 : ℚ) ≤ s := by exact_mod_cast hs
  unfold fval
  have hs0 : (0 : ℚ) < s := by linarith
  rw [div_sub_one (pow_pos hs0 2).ne', div_le_div_iff₀ (pow_pos hs0 2) (by positivity)]
  nlinarith

private theorem ordinary_prod_le (S : Finset ℕ) (π : ℕ → ℕ × ℕ) (hinj : Set.InjOn π S)
    {Q R fl M : ℕ} {α β : ℚ} (hfl : 3 ≤ fl) (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hαQ : 1 ≤ α ^ 2 * Q) (hβR : 1 ≤ β ^ 2 * R)
    (htail : 2 * ((α ^ M + β ^ M) / ((1 - α) * (1 - β))) < 1)
    (hS : ∀ s ∈ S, fl ≤ s ∧ Q ^ (π s).1 * R ^ (π s).2 ≤ s ^ 2 + s + 1 ∧
      ¬ (Even (π s).1 ∧ Even (π s).2)) :
    ∏ s ∈ S, fval s ≤ boxProd Q R fl M / (1 - 2 * ((α ^ M + β ^ M) / ((1 - α) * (1 - β)))) := by
  set T := (α ^ M + β ^ M) / ((1 - α) * (1 - β)) with hTdef
  set g : ℕ × ℕ → ℚ := fun t => fval (max fl (Nat.sqrt (Q ^ t.1 * R ^ t.2))) with hg
  have hfv0 : ∀ s ∈ S, 0 ≤ fval s := fun s hs =>
    le_trans zero_le_one (one_le_fval (by have := (hS s hs).1; omega))
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun s => (π s).1 < M ∧ (π s).2 < M)]
  set Sb := S.filter (fun s => (π s).1 < M ∧ (π s).2 < M)
  set St := S.filter (fun s => ¬ ((π s).1 < M ∧ (π s).2 < M))
  -- the box part
  have hb : ∏ s ∈ Sb, fval s ≤ boxProd Q R fl M := by
    calc ∏ s ∈ Sb, fval s ≤ ∏ s ∈ Sb, g (π s) := by
          apply Finset.prod_le_prod₀ (fun s hs => hfv0 s (Finset.mem_of_mem_filter s hs))
          intro s hs
          obtain ⟨hfs, hsz, -⟩ := hS s (Finset.mem_of_mem_filter s hs)
          apply fval_anti (le_trans (by omega) (le_max_left _ _))
          refine max_le hfs (Nat.lt_succ_iff.mp (Nat.sqrt_lt'.mpr ?_))
          nlinarith
      _ = ∏ t ∈ Sb.image π, g t :=
          (Finset.prod_image fun x hx y hy => hinj (Finset.mem_of_mem_filter x hx)
            (Finset.mem_of_mem_filter y hy)).symm
      _ ≤ boxProd Q R fl M := by
          apply Finset.prod_le_prod_of_subset_of_one_le₀
          · intro t ht
            obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
            rw [Finset.mem_filter] at hs
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
            exact ⟨hs.2, (hS s hs.1).2.2⟩
          · intro t _
            exact le_trans zero_le_one (one_le_fval (le_trans (by omega) (le_max_left _ _)))
          · intro t _ _
            exact one_le_fval (le_trans (by omega) (le_max_left _ _))
  -- the tail part
  have hx0 : ∀ s ∈ St, 0 ≤ fval s - 1 := fun s hs =>
    sub_nonneg.mpr (one_le_fval (by have := (hS s (Finset.mem_of_mem_filter s hs)).1; omega))
  have hxs : ∀ s ∈ St, fval s - 1 ≤ 2 * (α ^ (π s).1 * β ^ (π s).2) := by
    intro s hs
    obtain ⟨hfs, hsz, -⟩ := hS s (Finset.mem_of_mem_filter s hs)
    refine le_trans (fval_sub_le (by omega)) ?_
    set w := α ^ (π s).1 * β ^ (π s).2
    have hw0 : 0 ≤ w := by positivity
    have hV : ((Q ^ (π s).1 * R ^ (π s).2 : ℕ) : ℚ) < ((s : ℚ) + 1) ^ 2 := by
      have : Q ^ (π s).1 * R ^ (π s).2 < (s + 1) ^ 2 := by nlinarith
      exact_mod_cast this
    have hwV : 1 ≤ w ^ 2 * ((Q ^ (π s).1 * R ^ (π s).2 : ℕ) : ℚ) := by
      have : w ^ 2 * ((Q ^ (π s).1 * R ^ (π s).2 : ℕ) : ℚ) =
          (α ^ 2 * Q) ^ (π s).1 * (β ^ 2 * R) ^ (π s).2 := by
        simp only [w]; push_cast; ring
      rw [this]
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hαQ) (one_le_pow₀ hβR)
    have hws : 1 ≤ w * ((s : ℚ) + 1) := by
      have h2 : 1 ≤ (w * ((s : ℚ) + 1)) ^ 2 := by
        rw [mul_pow]
        nlinarith [sq_nonneg w]
      nlinarith [mul_nonneg hw0 (by positivity : (0 : ℚ) ≤ (s : ℚ) + 1)]
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hsum : ∑ s ∈ St, (fval s - 1) ≤ 2 * T := by
    calc ∑ s ∈ St, (fval s - 1) ≤ ∑ s ∈ St, 2 * (α ^ (π s).1 * β ^ (π s).2) :=
          Finset.sum_le_sum hxs
      _ = 2 * ∑ t ∈ St.image π, α ^ t.1 * β ^ t.2 := by
          rw [← Finset.mul_sum, Finset.sum_image fun x hx y hy =>
            hinj (Finset.mem_of_mem_filter x hx) (Finset.mem_of_mem_filter y hy)]
      _ ≤ 2 * T := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply tail_sum_le _ M hα0 hα1 hβ0 hβ1
          intro t ht
          obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
          have := (Finset.mem_filter.mp hs).2
          omega
  have hG := prod_one_add_mul_le St (fun s => fval s - 1) hx0
  simp only [add_sub_cancel] at hG
  have hP0 : 0 ≤ ∏ s ∈ St, fval s :=
    Finset.prod_nonneg fun s hs => hfv0 s (Finset.mem_of_mem_filter s hs)
  have ht : ∏ s ∈ St, fval s ≤ 1 / (1 - 2 * T) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have hb0 : 0 ≤ boxProd Q R fl M :=
    Finset.prod_nonneg fun t _ => le_trans zero_le_one
      (one_le_fval (le_trans (by omega) (le_max_left _ _)))
  calc _ ≤ boxProd Q R fl M * (1 / (1 - 2 * T)) := mul_le_mul hb ht hP0 hb0
    _ = _ := by ring


private theorem num_large :
    13 / 12 * (31 / 30 * (boxProd 13 31 5 5 / (1 - 2 * (((5 / 18 : ℚ) ^ 5 + (2 / 11) ^ 5) /
      ((1 - 5 / 18) * (1 - 2 / 11)))))) < 2 := by
  have hb : boxProd 13 31 5 5 ≤ 1717 / 1000 := by
    simp only [boxProd, Finset.prod_filter, Finset.prod_product, Finset.prod_range_succ,
      Finset.prod_range_zero]
    norm_num [fval, Nat.even_iff]
  calc _ ≤ 13 / 12 * (31 / 30 * ((1717 / 1000 : ℚ) / (1 - 2 * (((5 / 18 : ℚ) ^ 5 +
        (2 / 11) ^ 5) / ((1 - 5 / 18) * (1 - 2 / 11)))))) := by gcongr
    _ < 2 := by norm_num

private theorem num_small :
    13 / 12 * (7 / 6 * (boxProd 13 7 17 5 / (1 - 2 * (((5 / 18 : ℚ) ^ 5 + (5 / 13) ^ 5) /
      ((1 - 5 / 18) * (1 - 5 / 13)))))) < 2 := by
  have hb : boxProd 13 7 17 5 ≤ 1450 / 1000 := by
    simp only [boxProd, Finset.prod_filter, Finset.prod_product, Finset.prod_range_succ,
      Finset.prod_range_zero]
    norm_num [fval, Nat.even_iff]
  calc _ ≤ 13 / 12 * (7 / 6 * ((1450 / 1000 : ℚ) / (1 - 2 * (((5 / 18 : ℚ) ^ 5 +
        (5 / 13) ^ 5) / ((1 - 5 / 18) * (1 - 5 / 13)))))) := by gcongr
    _ < 2 := by norm_num


/-- Every prime factor of `1 + p + p^2`, for an ordinary square `p`, is `q` or `r`. -/
private theorem target_eq {N q r p : ℕ} (h : OddPerfect N)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) (h3 : ¬ 3 ∣ N)
    (hp : p ∈ N.primeFactors) (hpq : p ≠ q) (hpr : p ≠ r) {d : ℕ} (hd : d.Prime)
    (hdd : d ∣ 1 + p + p ^ 2) : d = q ∨ d = r := by
  have hp' := Nat.prime_of_mem_primeFactors hp
  rw [← sigma_sq hp'] at hdd
  obtain ⟨-, hdN, -, -, hd2⟩ :=
    OPNThreeFree.exact_square_transfer h.perfect h3 hp' (hsq p hp hpq hpr) hd hdd
  by_contra hc
  rw [not_or] at hc
  exact hd2 (hsq d (Nat.mem_primeFactors.mpr ⟨hd, hdN, h.ne_zero⟩) hc.1 hc.2)

private theorem ne_sq {p m : ℕ} (hp : 0 < p) : 1 + p + p ^ 2 ≠ m ^ 2 := by
  intro h
  have h1 : p ^ 2 < m ^ 2 := by rw [← h]; omega
  have h2 : m ^ 2 < (p + 1) ^ 2 := by rw [← h]; nlinarith
  have := (Nat.pow_lt_pow_iff_left two_ne_zero).mp h1
  have := (Nat.pow_lt_pow_iff_left two_ne_zero).mp h2
  omega

/-- Shape of `1 + p + p^2` for an ordinary square `p` in general: `q^a r^b`, with `a`
and `b` not both even. -/
private theorem shape_two {N q r p : ℕ} (h : OddPerfect N) (hqr : q ≠ r)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) (h3 : ¬ 3 ∣ N)
    (hp : p ∈ N.primeFactors) (hpq : p ≠ q) (hpr : p ≠ r) :
    1 + p + p ^ 2 = q ^ (1 + p + p ^ 2).factorization q * r ^ (1 + p + p ^ 2).factorization r ∧
    ¬ (Even ((1 + p + p ^ 2).factorization q) ∧ Even ((1 + p + p ^ 2).factorization r)) := by
  have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
  have hne : 1 + p + p ^ 2 ≠ 0 := by positivity
  have heq : 1 + p + p ^ 2 =
      q ^ (1 + p + p ^ 2).factorization q * r ^ (1 + p + p ^ 2).factorization r := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hne]
    rw [Finsupp.prod_of_support_subset _ (s := {q, r}) _ _ (fun _ _ => pow_zero _),
      Finset.prod_pair hqr]
    intro t ht
    rw [Nat.support_factorization] at ht
    have := target_eq h hsq h3 hp hpq hpr (Nat.prime_of_mem_primeFactors ht)
      (Nat.dvd_of_mem_primeFactors ht)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  refine ⟨heq, ?_⟩
  rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  apply ne_sq hp0 (m := q ^ i * r ^ j)
  rw [heq, hi, hj]
  ring

/-- The case where `r` divides the divisor sum of some ordinary square. -/
private theorem false_of_target {N q r p₀ : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) (h3 : ¬ 3 ∣ N)
    (hp₀ : p₀ ∈ N.primeFactors) (hp₀q : p₀ ≠ q) (hp₀r : p₀ ≠ r)
    (hdiv : r ∣ σ 1 (p₀ ^ 2)) : False := by
  have hN0 := h.ne_zero
  obtain ⟨hq4, hq3⟩ := q_mod h hq hodd h3
  have hq13 : 13 ≤ q := by have := hq.two_le; omega
  have hqT : q ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, Nat.dvd_of_factorization_pos hodd.pos.ne', hN0⟩
  obtain ⟨-, hrN, -, hr3, -⟩ := OPNThreeFree.exact_square_transfer h.perfect h3
    (Nat.prime_of_mem_primeFactors hp₀) (hsq p₀ hp₀ hp₀q hp₀r) hr hdiv
  have hrT : r ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hr, hrN, hN0⟩
  have hr7 : 7 ≤ r := by have := five_le h h3 hrT; omega
  -- the ordinary square primes
  set S := (N.primeFactors.erase q).erase r with hSdef
  have hmemS : ∀ {x}, x ∈ S → x ∈ N.primeFactors ∧ x ≠ q ∧ x ≠ r := by
    intro x hx
    rw [hSdef, Finset.mem_erase, Finset.mem_erase] at hx
    exact ⟨hx.2.2, hx.2.1, hx.1⟩
  set π : ℕ → ℕ × ℕ := fun s =>
    ((1 + s + s ^ 2).factorization q, (1 + s + s ^ 2).factorization r) with hπ
  have hinj : Set.InjOn π S := by
    intro x hx y hy hxy
    have ex := (shape_two h hrq.symm hsq h3 (hmemS hx).1 (hmemS hx).2.1 (hmemS hx).2.2).1
    have ey := (shape_two h hrq.symm hsq h3 (hmemS hy).1 (hmemS hy).2.1 (hmemS hy).2.2).1
    simp only [hπ, Prod.mk.injEq] at hxy
    have hF : 1 + x + x ^ 2 = 1 + y + y ^ 2 := by rw [ex, ey, hxy.1, hxy.2]
    rcases lt_trichotomy x y with hlt | heq | hgt
    · nlinarith
    · exact heq
    · nlinarith
  have hsz : ∀ R, R ≤ r → ∀ s ∈ S, 13 ^ (π s).1 * R ^ (π s).2 ≤ s ^ 2 + s + 1 := by
    intro R hR s hs
    have es := (shape_two h hrq.symm hsq h3 (hmemS hs).1 (hmemS hs).2.1 (hmemS hs).2.2).1
    have : 13 ^ (π s).1 * R ^ (π s).2 ≤ q ^ (π s).1 * r ^ (π s).2 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hq13 _) (Nat.pow_le_pow_left hR _)
    simp only [hπ] at this ⊢
    rw [← es] at this
    omega
  have hev : ∀ s ∈ S, ¬ (Even (π s).1 ∧ Even (π s).2) := fun s hs =>
    (shape_two h hrq.symm hsq h3 (hmemS hs).1 (hmemS hs).2.1 (hmemS hs).2.2).2
  -- abundancy bookkeeping
  have hab := (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
  have hrT' : r ∈ N.primeFactors.erase q := Finset.mem_erase.mpr ⟨hrq, hrT⟩
  rw [abundancy_eq_prod_primeFactors hN0, ← Finset.mul_prod_erase _ _ hqT,
    ← Finset.mul_prod_erase _ _ hrT'] at hab
  have heq : ∏ x ∈ S, abundancy (x ^ N.factorization x) = ∏ x ∈ S, fval x := by
    refine Finset.prod_congr rfl fun x hx => ?_
    obtain ⟨hxT, hxq, hxr⟩ := hmemS hx
    have hx' := Nat.prime_of_mem_primeFactors hxT
    have hx0 : (x : ℚ) ≠ 0 := by exact_mod_cast hx'.ne_zero
    rw [hsq x hxT hxq hxr, abundancy_prime_pow hx']
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, fval]
    field_simp
    ring
  rw [← hSdef, heq] at hab
  have hP0 : 0 ≤ ∏ x ∈ S, fval x := Finset.prod_nonneg fun x hx =>
    le_trans zero_le_one (one_le_fval (by have := five_le h h3 (hmemS hx).1; omega))
  have hgq := abundancy_prime_pow_lt hq (N.factorization q)
  have hlq := div_pred_le (by norm_num) hq13
  have hgr := abundancy_prime_pow_lt hr (N.factorization r)
  have hgq0 := abundancy_nonneg (q ^ N.factorization q)
  have hgr0 := abundancy_nonneg (r ^ N.factorization r)
  norm_num at hlq
  rcases le_or_gt 31 r with hr31 | hr31
  · have hP := ordinary_prod_le S π hinj (Q := 13) (R := 31) (fl := 5) (M := 5)
      (α := 5 / 18) (β := 2 / 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun s hs => ⟨five_le h h3 (hmemS hs).1, hsz 31 hr31 s hs, hev s hs⟩
    have hlr := div_pred_le (by norm_num) hr31
    norm_num at hlr
    have h1 := mul_le_mul (hgr.le.trans hlr) hP hP0 (by norm_num)
    have h2 := mul_le_mul (hgq.le.trans hlq) h1 (mul_nonneg hgr0 hP0) (by norm_num)
    have := num_large
    norm_num at h2 this
    linarith
  · have h17 : ∀ s ∈ S, 17 ≤ s := by
      intro s hs
      obtain ⟨hsT, hsq', hsr⟩ := hmemS hs
      have hs' := Nat.prime_of_mem_primeFactors hsT
      have h5 := five_le h h3 hsT
      have hm3 := OPNThreeFree.source_mod_three h.perfect h3 hs' (hsq s hsT hsq' hsr)
      have hm2 := hs'.eq_two_or_odd
      have hne5 : s ≠ 5 := by
        rintro rfl
        rcases target_eq h hsq h3 hsT hsq' hsr (d := 31) (by norm_num) (by norm_num)
          with h' | h' <;> omega
      have hne11 : s ≠ 11 := by
        rintro rfl
        rcases target_eq h hsq h3 hsT hsq' hsr (d := 7) (by norm_num) (by norm_num)
          with h' | h' <;>
        rcases target_eq h hsq h3 hsT hsq' hsr (d := 19) (by norm_num) (by norm_num)
          with h'' | h'' <;> omega
      omega
    have hP := ordinary_prod_le S π hinj (Q := 13) (R := 7) (fl := 17) (M := 5)
      (α := 5 / 18) (β := 5 / 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun s hs => ⟨h17 s hs, hsz 7 hr7 s hs, hev s hs⟩
    have hlr := div_pred_le (by norm_num) hr7
    norm_num at hlr
    have h1 := mul_le_mul (hgr.le.trans hlr) hP hP0 (by norm_num)
    have h2 := mul_le_mul (hgq.le.trans hlq) h1 (mul_nonneg hgr0 hP0) (by norm_num)
    have := num_small
    norm_num at h2 this
    linarith

/-- A restrained odd perfect number is divisible by 3. -/
theorem three_dvd_of_one_exception {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) : 3 ∣ N := by
  by_contra h3
  by_cases hT : ∃ p ∈ N.primeFactors, p ≠ q ∧ p ≠ r ∧ r ∣ σ 1 (p ^ 2)
  · obtain ⟨p, hp, hpq, hpr, hd⟩ := hT
    exact false_of_target h hq hodd hr hrq hsq h3 hp hpq hpr hd
  · exact false_of_core h hq hodd hsq h3 fun p hp hpq hpr hd => hT ⟨p, hp, hpq, hpr, hd⟩

end OddPerfect

#print axioms OddPerfect.three_dvd_of_one_exception
