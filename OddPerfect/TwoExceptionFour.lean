import OddPerfect.TwoExceptionFourCheck
import OddPerfect.TwoExceptionThreeB

/-!
# Two exceptional exponents with a general special prime: the exponents 2 and 4 at 3

Let `N` be an odd perfect number with special prime `q`, `q ≡ 2 (mod 3)`, let every prime factor
of `N` other than `q`, `r₁` and `r₂` have exponent exactly 2, and let `9 ∣ σ(q^k)` for the
exponent `k` of `q`. Then the exponent of 3 in `N` is not 2. For `q = 5` this is
`two_exceptions_five_three_ne_two`; for `q ≠ 5` we have `q ≥ 17`.

Assume `e₃ = 2`. The ledger of the prime 3 then has no room besides `q`: no other prime factor
`p` has `3 ∣ σ(p^{e_p})`. In particular `13 = σ(3^2)` divides `N` and is an exception, every prime
factor `≡ 1 (mod 3)` is `13` or the other exception `r`, and every other prime factor `t` has
exponent 2, `t ≡ 2 (mod 3)` and `σ(t^2) = t^2 + t + 1` supported on `{13, r}`. A squared `5`
forces `31 = r` and the abundant divisor `3^2 · 5^2 · 13^4 · 31^4`. The abundancy of `N` is then
below 2 by `rankin_tail`: with the generator `r` of weight `1/12` when `r ≥ 144`, with a finite
table of the values `13^a · r^b < 10^20` when `r < 144`, and with `13` alone otherwise; the case
`r = 5` with `q ∈ {17, 29, 41}` closes by the abundant divisor `3^2 · 5^4 · 13^4 · q`.
For `q ≡ 8 (mod 9)` the hypothesis `9 ∣ σ(q^k)` holds since `q + 1 ∣ σ(q^k)` for odd `k`.

For `e₃ = 4` and a special prime `q ≠ 5`, `σ(3^4) = 11^2` gives `11 ∣ N`, and the exponent `e`
of 11 is even with `e ≥ 6`, `3 ∤ e + 1` and `5 ∤ e + 1`: otherwise `σ(11^2) = 7 · 19` or
`σ(11^4) = 5 · 3221` divides `N` and the divisor `3^4 · 7^2 · 11^2 · 19`,
`3^4 · 7^2 · 11^4 · 19` or `3^4 · 5^2 · 11^4` is abundant. With at most two exceptional
exponents the exceptions are then `3` and `11`.

Whether these statements are new was not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace TwoExceptionFour

open TwoExceptionFourCheck TwoExceptionThreeA TwoExceptionThreeB RestrainedFour

/-- A prime dividing `σ(p^2)` for an exact square `p^2` divides `N`. -/
private theorem force_sq {N p t : ℕ} (h : OddPerfect N) (hp : p.Prime)
    (he : N.factorization p = 2) (ht : t.Prime) (ht2 : t ≠ 2) (hd : t ∣ phi3 p) : t ∣ N :=
  OPNStarter.force_prime h.perfect hp he ht ht2 (by rwa [sigma_prime_sq hp])

/-- An abundant divisor excludes perfection. -/
private theorem not_of_abundant_dvd {N d : ℕ} (h : OddPerfect N) (hd : d ∣ N)
    (hσ : 2 * d < σ 1 d) : False := by
  rw [sigma_one_apply] at hσ
  have hab := (Nat.abundant_iff_sum_divisors.mpr hσ).of_dvd hd h.ne_zero
  exact ((Nat.perfect_iff_not_abundant_and_not_deficient h.pos.ne).mp h.perfect).1 hab

/-- An abundant divisor built from four prime powers. -/
private theorem abundant_four {N a b c d i j k l : ℕ} (h : OddPerfect N)
    (pa : a.Prime) (pb : b.Prime) (pc : c.Prime) (pd : d.Prime)
    (ha : i ≤ N.factorization a) (hb : j ≤ N.factorization b) (hc : k ≤ N.factorization c)
    (hd : l ≤ N.factorization d)
    (c1 : Nat.Coprime (a ^ i) (b ^ j)) (c2 : Nat.Coprime (a ^ i * b ^ j) (c ^ k))
    (c3 : Nat.Coprime (a ^ i * b ^ j * c ^ k) (d ^ l))
    (hσ : 2 * (a ^ i * b ^ j * c ^ k * d ^ l) <
      σ 1 (a ^ i) * σ 1 (b ^ j) * σ 1 (c ^ k) * σ 1 (d ^ l)) : False := by
  have hN := h.ne_zero
  have hdvd := c3.mul_dvd_of_dvd_of_dvd (c2.mul_dvd_of_dvd_of_dvd (c1.mul_dvd_of_dvd_of_dvd
    ((pa.pow_dvd_iff_le_factorization hN).mpr ha) ((pb.pow_dvd_iff_le_factorization hN).mpr hb))
    ((pc.pow_dvd_iff_le_factorization hN).mpr hc)) ((pd.pow_dvd_iff_le_factorization hN).mpr hd)
  apply not_of_abundant_dvd h hdvd
  rwa [isMultiplicative_sigma.map_mul_of_coprime c3, isMultiplicative_sigma.map_mul_of_coprime c2,
    isMultiplicative_sigma.map_mul_of_coprime c1]

/-- With `e₃ = 2` and `9 ∣ σ(q^k)`, no other prime factor sends a factor 3. -/
private theorem no_sender {N q p : ℕ} (h : OddPerfect N) (h32 : N.factorization 3 = 2)
    (hq : q ∈ N.primeFactors) (h9 : 9 ∣ σ 1 (q ^ N.factorization q))
    (hp : p ∈ N.primeFactors) (hpq : p ≠ q) (h3 : 3 ∣ σ 1 (p ^ N.factorization p)) : False := by
  have hbal := OPNStarter.valuation_balance h.perfect 3
  have h23 : Nat.factorization 2 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  rw [h23, h32, zero_add] at hbal
  have hsub : ({q, p} : Finset ℕ) ⊆ N.primeFactors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun p => (σ 1 (p ^ N.factorization p)).factorization 3)
    (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_pair (Ne.symm hpq)] at hle
  have hne : ∀ x ∈ N.primeFactors, σ 1 (x ^ N.factorization x) ≠ 0 := fun x hx =>
    (sigma_pos 1 _ (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hx).ne_zero)).ne'
  have a1 : 2 ≤ (σ 1 (q ^ N.factorization q)).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization (hne q hq)).mp (by simpa using h9)
  have a2 : 1 ≤ (σ 1 (p ^ N.factorization p)).factorization 3 :=
    (Nat.prime_three.dvd_iff_one_le_factorization (hne p hp)).mp h3
  omega

/-- A squared prime factor `≡ 1 (mod 3)` would send a factor 3. -/
private theorem ne_two_of_one {N q p : ℕ} (h : OddPerfect N) (h32 : N.factorization 3 = 2)
    (hq : q ∈ N.primeFactors) (h9 : 9 ∣ σ 1 (q ^ N.factorization q))
    (hp : p ∈ N.primeFactors) (hpq : p ≠ q) (hp3 : p % 3 = 1) : N.factorization p ≠ 2 := by
  intro he
  apply no_sender h h32 hq h9 hp hpq
  rw [he, sigma_prime_sq (Nat.prime_of_mem_primeFactors hp)]
  exact (three_dvd_phi3_iff p).mpr hp3

/-- Every prime factor `≡ 1 (mod 3)` is `13` or `r`. -/
private theorem one_mod_three {N q r p : ℕ} (h : OddPerfect N) (hq3 : q % 3 = 2)
    (h32 : N.factorization 3 = 2) (hq : q ∈ N.primeFactors)
    (h9 : 9 ∣ σ 1 (q ^ N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ 13 → p ≠ r → N.factorization p = 2)
    (hp : p ∈ N.primeFactors) (hp3 : p % 3 = 1) : p = 13 ∨ p = r := by
  by_contra hc
  push Not at hc
  have hpq : p ≠ q := by omega
  exact ne_two_of_one h h32 hq h9 hp hpq hp3 (hsq p hp hpq hc.1 hc.2)

/-- An exponent other than 2 of a non-special prime factor is at least 4. -/
private theorem four_le {N q p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hp : p ∈ N.primeFactors) (hpq : p ≠ q)
    (h2 : N.factorization p ≠ 2) : 4 ≤ N.factorization p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  obtain ⟨k, hk⟩ := even_factorization_of_ne h hq hodd hpp hpq
  have : 0 < N.factorization p :=
    hpp.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hp)
  omega

/-- Support on two primes. -/
private theorem smooth_two {m u v : ℕ} (hm : m ≠ 0) (huv : u ≠ v)
    (h : m.primeFactors ⊆ {u, v}) : m = u ^ m.factorization u * v ^ m.factorization v := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm]
  rw [Finsupp.prod_of_support_subset _ (s := {u, v}) (by rwa [Nat.support_factorization]) _
    (fun _ _ => pow_zero _), Finset.prod_pair huv]

/-- The table: `t^2 + t + 1` supported on `{13, r}` is at least `10^20`. -/
private theorem big_of_table {u r : ℕ} (hr : rOK r = true) (hu : 11 ≤ u) (h2 : u % 2 = 1)
    (h5 : u % 5 ≠ 0) (h29 : u ≠ 29) (hsub : (phi3 u).primeFactors ⊆ {13, r}) :
    10 ^ 20 ≤ phi3 u := by
  have hr' : 7 ≤ r ∧ r ≠ 13 := by
    simp only [rOK, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hr
    omega
  have hV : phi3 u ≠ 0 := by unfold phi3; omega
  have heq := smooth_two hV (by omega : (13 : ℕ) ≠ r) hsub
  by_contra hc
  push Not at hc
  have hpos : 0 < phi3 u := Nat.pos_of_ne_zero hV
  have ha : (phi3 u).factorization 13 < 18 := by
    by_contra ha
    push Not at ha
    have : 13 ^ 18 ≤ phi3 u := (Nat.pow_le_pow_right (by norm_num) ha).trans
      (Nat.le_of_dvd hpos (Nat.ordProj_dvd _ _))
    exact absurd (lt_of_le_of_lt this hc) (by norm_num)
  have hb : (phi3 u).factorization r < 24 := by
    by_contra hb
    push Not at hb
    have : 7 ^ 24 ≤ phi3 u := (Nat.pow_le_pow_left hr'.1 24).trans
      ((Nat.pow_le_pow_right (by omega) hb).trans (Nat.le_of_dvd hpos (Nat.ordProj_dvd _ _)))
    exact absurd (lt_of_le_of_lt this hc) (by norm_num)
  rcases root_table hr (by omega) ha hb heq with h | h | h | h
  · omega
  · omega
  · omega
  · exact absurd h (not_le.mpr hc)

/-- `t^2 + t + 1` supported on `{13}` is at least `10^20`. -/
private theorem big13 {u : ℕ} (hu : 11 ≤ u) (h2 : u % 2 = 1) (h5 : u % 5 ≠ 0)
    (hsub : (phi3 u).primeFactors ⊆ {13}) : 10 ^ 20 ≤ phi3 u := by
  have h29 : u ≠ 29 := by
    rintro rfl
    have h67 : 67 ∈ (phi3 29).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨by norm_num, by norm_num [phi3], by norm_num [phi3]⟩
    have := hsub h67
    simp at this
  exact big_of_table (r := 7) (by decide) hu h2 h5 h29
    (hsub.trans (by simp))

/-- The value `c p` bounding the abundancy of the component of `p`. -/
private def cval (p : ℕ) : ℚ := if p = 3 then 13 / 9 else (p : ℚ) / (p - 1)

private theorem cval_le {x y : ℕ} (hx3 : x ≠ 3) (hy : 2 ≤ y) (hxy : y ≤ x) :
    cval x ≤ (y : ℚ) / (y - 1) := by
  simp only [cval, if_neg hx3]
  have hy' : (2 : ℚ) ≤ y := by exact_mod_cast hy
  have hxy' : (y : ℚ) ≤ x := by exact_mod_cast hxy
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

private theorem cval_nonneg {x : ℕ} (hx : 2 ≤ x) : 0 ≤ cval x := by
  unfold cval
  split_ifs
  · norm_num
  · have : (2 : ℚ) ≤ x := by exact_mod_cast hx
    exact div_nonneg (by linarith) (by linarith)

private theorem cval_three : cval 3 = 13 / 9 := by simp [cval]

private theorem cval_of {x : ℕ} (hx : x ≠ 3) : cval x = (x : ℚ) / (x - 1) := by
  simp [cval, hx]

/-- The abundancy bound of a component. -/
private theorem abundancy_le_cval {N p : ℕ} (h32 : N.factorization 3 = 2) (hp : p.Prime) :
    abundancy (p ^ N.factorization p) ≤ cval p := by
  by_cases p3 : p = 3
  · subst p3
    rw [cval_three, h32, abundancy_prime_pow Nat.prime_three]
    norm_num [Finset.sum_range_succ]
  · rw [cval_of p3]
    exact (abundancy_prime_pow_lt hp _).le

/-- The Rankin tail with `13` as the only generator. -/
private theorem tail_C {N : ℕ} (h : OddPerfect N) (K : Finset ℕ) (hK : K ⊆ N.primeFactors)
    (c : ℕ → ℚ) (hC : ∀ p ∈ K, abundancy (p ^ N.factorization p) ≤ c p)
    (hprod : ∏ p ∈ K, c p ≤ 1999 / 1000)
    (hT : ∀ u ∈ N.primeFactors \ K, N.factorization u = 2 ∧ 10 ≤ u ∧
      (phi3 u).primeFactors ⊆ {13} ∧ 10 ^ 20 ≤ phi3 u) : False := by
  have hS := rankin_tail (N.primeFactors \ K) (g₁ := 13) (g₂ := bigP) (g₃ := bigQ) (g₄ := bigR)
    (B := 10 ^ 20) (α₁ := 5 / 18) (α₂ := 1 / 10 ^ 15) (α₃ := 1 / 10 ^ 15) (α₄ := 1 / 10 ^ 15)
    (β₁ := 53 / 100) (β₂ := 1 / 10 ^ 7) (β := 1 / 10 ^ 5)
    prime_Q prime_R (by norm_num [bigP]) (by norm_num [bigQ]) (by norm_num [bigR])
    (by norm_num [bigP, bigQ]) (by norm_num [bigP, bigR]) (by norm_num [bigQ, bigR])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [bigP]) (by norm_num [bigQ]) (by norm_num [bigR])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [bigP]) (by norm_num)
    (fun u hu => ⟨(hT u hu).2.1, fun x hx => by
      have := (hT u hu).2.2.1 hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      exact Or.inl this, fun _ _ => (hT u hu).2.2.2⟩)
  exact abundancy_close h K hK c hC _ (fun u hu => (hT u hu).1) hS
    (lt_of_le_of_lt hprod (by norm_num))

/-- The Rankin tail with the generators `13` and a small `r`. -/
private theorem tail_B {N r : ℕ} (h : OddPerfect N) (hr7 : 7 ≤ r) (hr144 : r < 144)
    (hr13 : r ≠ 13) (K : Finset ℕ) (hK : K ⊆ N.primeFactors)
    (c : ℕ → ℚ) (hC : ∀ p ∈ K, abundancy (p ^ N.factorization p) ≤ c p)
    (hprod : ∏ p ∈ K, c p ≤ 1999 / 1000)
    (hT : ∀ u ∈ N.primeFactors \ K, N.factorization u = 2 ∧ 10 ≤ u ∧
      (phi3 u).primeFactors ⊆ {13, r} ∧ 10 ^ 20 ≤ phi3 u) : False := by
  have r7 : (7 : ℚ) ≤ r := by exact_mod_cast hr7
  have hS := rankin_tail (N.primeFactors \ K) (g₁ := 13) (g₂ := r) (g₃ := bigQ) (g₄ := bigR)
    (B := 10 ^ 20) (α₁ := 5 / 18) (α₂ := 2 / 5) (α₃ := 1 / 10 ^ 15) (α₄ := 1 / 10 ^ 15)
    (β₁ := 53 / 100) (β₂ := 13 / 20) (β := 1 / 10 ^ 5)
    prime_Q prime_R (Ne.symm hr13) (by norm_num [bigQ]) (by norm_num [bigR])
    (by unfold bigQ; omega) (by unfold bigR; omega) (by norm_num [bigQ, bigR])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num; linarith) (by norm_num [bigQ]) (by norm_num [bigR])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num; linarith) (by norm_num)
    (fun u hu => ⟨(hT u hu).2.1, fun x hx => by
      have := (hT u hu).2.2.1 hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      tauto, fun _ _ => (hT u hu).2.2.2⟩)
  exact abundancy_close h K hK c hC _ (fun u hu => (hT u hu).1) hS
    (lt_of_le_of_lt hprod (by norm_num))

/-- The Rankin tail with the generators `13` and a large `r`. -/
private theorem tail_A {N r : ℕ} (h : OddPerfect N) (hr : r.Prime) (hr144 : 144 ≤ r)
    (K : Finset ℕ) (hK : K ⊆ N.primeFactors)
    (c : ℕ → ℚ) (hC : ∀ p ∈ K, abundancy (p ^ N.factorization p) ≤ c p)
    (hprod : ∏ p ∈ K, c p ≤ 13 / 9 * (17 / 16 * (13 / 12 * (144 / 143))))
    (hT : ∀ u ∈ N.primeFactors \ K, N.factorization u = 2 ∧ 10 ≤ u ∧
      (phi3 u).primeFactors ⊆ {13, r} ∧ (¬ r ∣ phi3 u → 10 ^ 20 ≤ phi3 u)) : False := by
  obtain ⟨g2, -, h2, d2, -⟩ := dummy_avoid r r
  obtain ⟨g4, p4, h4, d4, d5⟩ := dummy_avoid r g2
  have r144 : (144 : ℚ) ≤ r := by exact_mod_cast hr144
  have hS := rankin_tail (N.primeFactors \ K) (g₁ := 13) (g₂ := g2) (g₃ := r) (g₄ := g4)
    (B := 10 ^ 20) (α₁ := 5 / 18) (α₂ := 1 / 10 ^ 15) (α₃ := 1 / 12) (α₄ := 1 / 10 ^ 15)
    (β₁ := 53 / 100) (β₂ := 1 / 10 ^ 7) (β := 1 / 10 ^ 5)
    hr p4 (by omega) (by omega) (by omega) d2 (Ne.symm d5) (Ne.symm d4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by
      have : (10 ^ 30 : ℚ) ≤ g2 := by exact_mod_cast h2
      norm_num
      linarith)
    (by norm_num; linarith)
    (by
      have : (10 ^ 30 : ℚ) ≤ g4 := by exact_mod_cast h4
      norm_num
      linarith)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by
      have : (10 ^ 30 : ℚ) ≤ g2 := by exact_mod_cast h2
      norm_num
      linarith)
    (by norm_num)
    (fun u hu => ⟨(hT u hu).2.1, fun x hx => by
      have := (hT u hu).2.2.1 hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      tauto, fun hn _ => (hT u hu).2.2.2 hn⟩)
  exact abundancy_close h K hK c hC _ (fun u hu => (hT u hu).1) hS
    (lt_of_le_of_lt hprod (by norm_num))

/-- A prime factor outside `{3, q, 13, r}`. -/
private theorem tail_fact {N q r t : ℕ} (h : OddPerfect N) (hq3 : q % 3 = 2)
    (h32 : N.factorization 3 = 2) (hqN : q ∈ N.primeFactors)
    (h9 : 9 ∣ σ 1 (q ^ N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ 13 → p ≠ r → N.factorization p = 2)
    (h5r : 5 ∈ N.primeFactors → 5 = r)
    (ht : t ∈ N.primeFactors) (t3 : t ≠ 3) (tq : t ≠ q) (t13 : t ≠ 13) (tr : t ≠ r) :
    N.factorization t = 2 ∧ 11 ≤ t ∧ t % 2 = 1 ∧ t % 5 ≠ 0 ∧
      ∀ x, x.Prime → x ∣ phi3 t → x = 13 ∨ (x = r ∧ r ∈ N.primeFactors ∧ r % 3 = 1) := by
  have hN := h.ne_zero
  have htp := Nat.prime_of_mem_primeFactors ht
  have he := hsq t ht tq t13 tr
  have h1 : t % 3 ≠ 1 := fun h1 => ne_two_of_one h h32 hqN h9 ht tq h1 he
  have h0 : t % 3 ≠ 0 := fun h0 =>
    t3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three htp).mp (Nat.dvd_of_mod_eq_zero h0)).symm
  have h2 : t % 2 = 1 := by
    have : t ≠ 2 := by
      rintro rfl
      exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors ht)
    exact Nat.odd_iff.mp (htp.odd_of_ne_two this)
  have h5 : t % 5 ≠ 0 := by
    intro h0
    have h5t : 5 = t :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_five htp).mp (Nat.dvd_of_mod_eq_zero h0)
    subst h5t
    exact tr (h5r ht)
  refine ⟨he, ?_, h2, h5, ?_⟩
  · have := htp.two_le
    omega
  · intro x hx hxd
    have hx3 : x ≠ 3 := by
      rintro rfl
      have := (three_dvd_phi3_iff t).mp hxd
      omega
    have hx1 := prime_dvd_phi3_mod_three hx hx3 hxd
    have hxN := force_sq h htp he hx (by omega) hxd
    have hxpf : x ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hx, hxN, hN⟩
    rcases one_mod_three h hq3 h32 hqN h9 hsq hxpf hx1 with hx' | hx'
    · exact Or.inl hx'
    · subst hx'
      exact Or.inr ⟨rfl, hxpf, hx1⟩

/-- A prime factor `5` is the exception `r`. -/
private theorem five_eq {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hq3 : q % 3 = 2) (hq17 : 17 ≤ q)
    (h32 : N.factorization 3 = 2) (hqN : q ∈ N.primeFactors)
    (h9 : 9 ∣ σ 1 (q ^ N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ 13 → p ≠ r → N.factorization p = 2)
    (h13 : 13 ∈ N.primeFactors) (h5 : 5 ∈ N.primeFactors) : 5 = r := by
  by_contra h5r
  have hN := h.ne_zero
  have he5 := hsq 5 h5 (by omega) (by norm_num) h5r
  have p13 : Nat.Prime 13 := by norm_num
  have p31 : Nat.Prime 31 := by norm_num
  have h31 : 31 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨p31,
    force_sq h Nat.prime_five he5 p31 (by norm_num) (by norm_num [phi3]), hN⟩
  have e13 := four_le h hq hodd h13 (by omega)
    (ne_two_of_one h h32 hqN h9 h13 (by omega) (by norm_num))
  have e31 := four_le h hq hodd h31 (by omega)
    (ne_two_of_one h h32 hqN h9 h31 (by omega) (by norm_num))
  exact abundant_four h Nat.prime_three Nat.prime_five p13 p31 (i := 2) (j := 2) (k := 4) (l := 4)
    (by omega) (by omega) e13 e31 (by norm_num) (by norm_num) (by norm_num)
    (by
      rw [sigma_one_apply_prime_pow Nat.prime_three, sigma_one_apply_prime_pow Nat.prime_five,
        sigma_one_apply_prime_pow p13, sigma_one_apply_prime_pow p31]
      norm_num [Finset.sum_range_succ])

/-- Products of the bounds. -/
private theorem prod_le_two {x y X Y : ℚ} (hx : x ≤ X) (hy : y ≤ Y) (hx0 : 0 ≤ x)
    (hy0 : 0 ≤ y) : 13 / 9 * (x * (13 / 12 * y)) ≤ 13 / 9 * (X * (13 / 12 * Y)) := by
  nlinarith [mul_le_mul hx hy hy0 (hx0.trans hx)]

/-- The case of an exception `r ≡ 1 (mod 3)`. -/
private theorem case_one {N q r : ℕ} (h : OddPerfect N) (hq3 : q % 3 = 2) (hq17 : 17 ≤ q)
    (h32 : N.factorization 3 = 2) (hqN : q ∈ N.primeFactors)
    (h9 : 9 ∣ σ 1 (q ^ N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ 13 → p ≠ r → N.factorization p = 2)
    (h13 : 13 ∈ N.primeFactors) (h5r : 5 ∈ N.primeFactors → 5 = r)
    (hrN : r ∈ N.primeFactors) (hr3 : r % 3 = 1) (hr13 : r ≠ 13) : False := by
  have hrp := Nat.prime_of_mem_primeFactors hrN
  have hr7 : 7 ≤ r := by
    have := hrp.two_le
    have : r ≠ 4 := by rintro rfl; norm_num at hrp
    omega
  have hq' : cval q ≤ 17 / 16 := by
    have := cval_le (x := q) (y := 17) (by omega) (by norm_num) hq17
    norm_num at this
    exact this
  have hq0 := cval_nonneg (x := q) (by omega)
  have hsubR : ∀ t, (∀ x, x.Prime → x ∣ phi3 t → x = 13 ∨ (x = r ∧ r ∈ N.primeFactors ∧
      r % 3 = 1)) → (phi3 t).primeFactors ⊆ {13, r} := by
    intro t ht x hx
    have := ht x (Nat.prime_of_mem_primeFactors hx) (Nat.dvd_of_mem_primeFactors hx)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have h3K : (3 : ℕ) ∉ ({q, 13, r} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hqK : q ∉ ({13, r} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have h13K : (13 : ℕ) ∉ ({r} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    omega
  have h3N : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three,
    Nat.dvd_of_factorization_pos (by omega), h.ne_zero⟩
  have hK : ({3, q, 13, r} : Finset ℕ) ⊆ N.primeFactors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hC : ∀ p ∈ ({3, q, 13, r} : Finset ℕ), abundancy (p ^ N.factorization p) ≤ cval p :=
    fun p hp => abundancy_le_cval h32 (Nat.prime_of_mem_primeFactors (hK hp))
  have hprod4 : ∏ p ∈ ({3, q, 13, r} : Finset ℕ), cval p =
      13 / 9 * (cval q * (13 / 12 * cval r)) := by
    rw [Finset.prod_insert h3K, Finset.prod_insert hqK, Finset.prod_insert h13K,
      Finset.prod_singleton, cval_three, cval_of (by norm_num : (13 : ℕ) ≠ 3)]
    norm_num
  have hmemK : ∀ u ∈ N.primeFactors \ ({3, q, 13, r} : Finset ℕ),
      u ∈ N.primeFactors ∧ u ≠ 3 ∧ u ≠ q ∧ u ≠ 13 ∧ u ≠ r := by
    intro u hu
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hu
    tauto
  by_cases hbig : 144 ≤ r
  · -- the generator `r` of weight `1/12`
    apply tail_A h hrp hbig _ hK cval hC
    · rw [hprod4]
      exact prod_le_two hq' (by
        have := cval_le (x := r) (y := 144) (by omega) (by norm_num) hbig
        norm_num at this ⊢
        exact this) hq0 (cval_nonneg (by omega))
    · intro u hu
      obtain ⟨hu1, hu2, hu3, hu4, hu5⟩ := hmemK u hu
      obtain ⟨e, h11, o2, o5, hx⟩ := tail_fact h hq3 h32 hqN h9 hsq h5r hu1 hu2 hu3 hu4 hu5
      refine ⟨e, by omega, hsubR u hx, fun hnr => big13 h11 o2 o5 ?_⟩
      intro x hxm
      have := hx x (Nat.prime_of_mem_primeFactors hxm) (Nat.dvd_of_mem_primeFactors hxm)
      rcases this with h' | ⟨h', -⟩
      · simp [h']
      · subst h'
        exact absurd (Nat.dvd_of_mem_primeFactors hxm) hnr
  · push Not at hbig
    have hrOK : rOK r = true := by
      have h133 : r ≠ 133 := by rintro rfl; norm_num at hrp
      simp only [rOK, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq]
      omega
    by_cases h29 : 29 ∈ N.primeFactors ∧ 29 ≠ q
    · -- the prime 29 forces `r = 67`
      have p29 : Nat.Prime 29 := by norm_num
      have e29 := hsq 29 h29.1 h29.2 (by norm_num) (by omega)
      have p67 : Nat.Prime 67 := by norm_num
      have h67 : 67 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨p67,
        force_sq h p29 e29 p67 (by norm_num) (by norm_num [phi3]), h.ne_zero⟩
      have hr67 : r = 67 := by
        rcases one_mod_three h hq3 h32 hqN h9 hsq h67 (by norm_num) with h' | h'
        · norm_num at h'
        · exact h'.symm
      subst hr67
      have hK5 : ({3, q, 13, 67, 29} : Finset ℕ) ⊆ N.primeFactors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact h3N
        · exact hqN
        · exact h13
        · exact hrN
        · exact h29.1
      apply tail_B (r := 67) h (by norm_num) (by norm_num) (by norm_num) _ hK5 cval
        (fun p hp => abundancy_le_cval h32 (Nat.prime_of_mem_primeFactors (hK5 hp)))
      · rw [Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
          Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
          Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton,
          cval_three, cval_of (by norm_num : (13 : ℕ) ≠ 3), cval_of (by norm_num : (67 : ℕ) ≠ 3),
          cval_of (by norm_num : (29 : ℕ) ≠ 3)]
        norm_num
        nlinarith
      · intro u hu
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hu
        push Not at hu
        obtain ⟨e, h11, o2, o5, hx⟩ :=
          tail_fact h hq3 h32 hqN h9 hsq h5r hu.1 hu.2.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2.1
        exact ⟨e, by omega, hsubR u hx,
          big_of_table hrOK h11 o2 o5 hu.2.2.2.2.2 (hsubR u hx)⟩
    · apply tail_B h hr7 hbig hr13 _ hK cval hC
      · rw [hprod4]
        have := prod_le_two (X := 17 / 16) (Y := 7 / 6) hq' (by
          have := cval_le (x := r) (y := 7) (by omega) (by norm_num) hr7
          norm_num at this ⊢
          exact this) hq0 (cval_nonneg (by omega))
        linarith
      · intro u hu
        obtain ⟨hu1, hu2, hu3, hu4, hu5⟩ := hmemK u hu
        obtain ⟨e, h11, o2, o5, hx⟩ := tail_fact h hq3 h32 hqN h9 hsq h5r hu1 hu2 hu3 hu4 hu5
        have hu29 : u ≠ 29 := by
          rintro rfl
          exact h29 ⟨hu1, hu3⟩
        exact ⟨e, by omega, hsubR u hx, big_of_table hrOK h11 o2 o5 hu29 (hsubR u hx)⟩

/-- The case without an exception `r ≡ 1 (mod 3)` other than 13. -/
private theorem case_other {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hq3 : q % 3 = 2) (hq4 : q % 4 = 1) (hq17 : 17 ≤ q)
    (h32 : N.factorization 3 = 2) (hqN : q ∈ N.primeFactors)
    (h9 : 9 ∣ σ 1 (q ^ N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ 13 → p ≠ r → N.factorization p = 2)
    (h13 : 13 ∈ N.primeFactors) (h5r : 5 ∈ N.primeFactors → 5 = r)
    (hnr : ¬ (r ∈ N.primeFactors ∧ r % 3 = 1 ∧ r ≠ 13)) : False := by
  have hN := h.ne_zero
  have hq' : cval q ≤ 17 / 16 := by
    have := cval_le (x := q) (y := 17) (by omega) (by norm_num) hq17
    norm_num at this
    exact this
  have hq0 := cval_nonneg (x := q) (by omega)
  have h3N : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three,
    Nat.dvd_of_factorization_pos (by omega), hN⟩
  have p13 : Nat.Prime 13 := by norm_num
  have e13 := four_le h hq hodd h13 (by omega)
    (ne_two_of_one h h32 hqN h9 h13 (by omega) (by norm_num))
  by_cases hr2 : r ∈ N.primeFactors ∧ r ≠ 3 ∧ r ≠ q ∧ r ≠ 13
  · obtain ⟨hrN, hr3', hrq, hr13⟩ := hr2
    have hrp := Nat.prime_of_mem_primeFactors hrN
    have hr3 : r % 3 = 2 := by
      have h0 : r % 3 ≠ 0 := fun h0 => hr3'
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hrp).mp (Nat.dvd_of_mod_eq_zero h0)).symm
      have h1 : r % 3 ≠ 1 := fun h1 => hnr ⟨hrN, h1, hr13⟩
      omega
    have hK : ({3, q, 13, r} : Finset ℕ) ⊆ N.primeFactors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hprod4 : ∏ p ∈ ({3, q, 13, r} : Finset ℕ), cval p =
        13 / 9 * (cval q * (13 / 12 * cval r)) := by
      rw [Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.prod_insert (by simp only [Finset.mem_singleton]; omega),
        Finset.prod_singleton, cval_three, cval_of (by norm_num : (13 : ℕ) ≠ 3)]
      norm_num
    have hT : ∀ u ∈ N.primeFactors \ ({3, q, 13, r} : Finset ℕ), N.factorization u = 2 ∧
        10 ≤ u ∧ (phi3 u).primeFactors ⊆ {13} ∧ 10 ^ 20 ≤ phi3 u := by
      intro u hu
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hu
      push Not at hu
      obtain ⟨e, h11, o2, o5, hx⟩ :=
        tail_fact h hq3 h32 hqN h9 hsq h5r hu.1 hu.2.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2
      have hsub : (phi3 u).primeFactors ⊆ {13} := by
        intro x hxm
        rcases hx x (Nat.prime_of_mem_primeFactors hxm) (Nat.dvd_of_mem_primeFactors hxm) with
          h' | ⟨-, -, h'⟩
        · simp [h']
        · omega
      exact ⟨e, by omega, hsub, big13 h11 o2 o5 hsub⟩
    have hC : ∀ p ∈ ({3, q, 13, r} : Finset ℕ), abundancy (p ^ N.factorization p) ≤ cval p :=
      fun p hp => abundancy_le_cval h32 (Nat.prime_of_mem_primeFactors (hK hp))
    by_cases r5 : r = 5
    · subst r5
      have e5 : 4 ≤ N.factorization 5 := by
        refine four_le h hq hodd hrN (by omega) (fun he5 => ?_)
        have p31 : Nat.Prime 31 := by norm_num
        have h31 : 31 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨p31,
          force_sq h Nat.prime_five he5 p31 (by norm_num) (by norm_num [phi3]), hN⟩
        rcases one_mod_three h hq3 h32 hqN h9 hsq h31 (by norm_num) with h' | h' <;>
          norm_num at h'
      by_cases q47 : 47 ≤ q
      · apply tail_C h _ hK cval hC _ hT
        rw [hprod4, cval_of (by norm_num : (5 : ℕ) ≠ 3)]
        have := cval_le (x := q) (y := 47) (by omega) (by norm_num) q47
        norm_num at this ⊢
        nlinarith
      · have hq' : q = 17 ∨ q = 29 ∨ q = 41 := by omega
        have eq1 : 1 ≤ N.factorization q := hodd.pos
        rcases hq' with rfl | rfl | rfl
        all_goals
          exact abundant_four h Nat.prime_three Nat.prime_five p13 hq (i := 2) (j := 4) (k := 4)
            (l := 1) (by omega) e5 e13 eq1 (by norm_num) (by norm_num) (by norm_num)
            (by
              rw [sigma_one_apply_prime_pow Nat.prime_three, sigma_one_apply_prime_pow
                Nat.prime_five, sigma_one_apply_prime_pow p13, sigma_one_apply_prime_pow hq]
              norm_num [Finset.sum_range_succ])
    · have hr11 : 11 ≤ r := by
        have := hrp.two_le
        have : r ≠ 2 := by
          rintro rfl
          exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hrN)
        have := Nat.odd_iff.mp (hrp.odd_of_ne_two this)
        omega
      apply tail_C h _ hK cval hC _ hT
      rw [hprod4]
      have := prod_le_two (X := 17 / 16) (Y := 11 / 10) hq' (by
        have := cval_le (x := r) (y := 11) (by omega) (by norm_num) hr11
        norm_num at this ⊢
        exact this) hq0 (cval_nonneg (by omega))
      linarith
  · have hK : ({3, q, 13} : Finset ℕ) ⊆ N.primeFactors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    apply tail_C h _ hK cval
      (fun p hp => abundancy_le_cval h32 (Nat.prime_of_mem_primeFactors (hK hp)))
    · rw [Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.prod_insert (by simp only [Finset.mem_singleton]; omega),
        Finset.prod_singleton, cval_three, cval_of (by norm_num : (13 : ℕ) ≠ 3)]
      norm_num at hq' ⊢
      nlinarith
    · intro u hu
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hu
      push Not at hu
      have hur : u ≠ r := by
        rintro rfl
        exact hr2 ⟨hu.1, hu.2.1, hu.2.2.1, hu.2.2.2⟩
      obtain ⟨e, h11, o2, o5, hx⟩ :=
        tail_fact h hq3 h32 hqN h9 hsq h5r hu.1 hu.2.1 hu.2.2.1 hu.2.2.2 hur
      have hsub : (phi3 u).primeFactors ⊆ {13} := by
        intro x hxm
        rcases hx x (Nat.prime_of_mem_primeFactors hxm) (Nat.dvd_of_mem_primeFactors hxm) with
          h' | ⟨h', h1, h2⟩
        · simp [h']
        · subst h'
          by_cases hx13 : x = 13
          · simp [hx13]
          · exact absurd ⟨h1, h2, hx13⟩ hnr
      exact ⟨e, by omega, hsub, big13 h11 o2 o5 hsub⟩

end TwoExceptionFour

open TwoExceptionFour in
/-- Let `N` be an odd perfect number with special prime `q ≡ 2 (mod 3)` and exponent `k`, with
`9 ∣ σ(q^k)`, in which every prime factor other than `q`, `r₁` and `r₂` has exponent exactly 2.
Then the exponent of 3 in `N` is not 2. Whether this statement is new was not verified. -/
theorem two_exceptions_three_ne_two_of_nine_dvd {N q r₁ r₂ : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hq3 : q % 3 = 2)
    (h9 : 9 ∣ σ 1 (q ^ N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2) :
    N.factorization 3 ≠ 2 := by
  intro h32
  by_cases hq5 : q = 5
  · subst hq5
    exact two_exceptions_five_three_ne_two h hodd hsq h32
  have hN := h.ne_zero
  have hq4 := (mod_four_special h hq hodd).1
  have hq17 : 17 ≤ q := by
    have := hq.two_le
    omega
  have hqN : q ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, Nat.dvd_of_factorization_pos hodd.pos.ne', hN⟩
  have h13 : 13 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num,
    OPNStarter.thirteen_dvd_of_three_sq h.perfect h32, hN⟩
  have h13r : 13 = r₁ ∨ 13 = r₂ := by
    by_contra hc
    push Not at hc
    exact ne_two_of_one h h32 hqN h9 h13 (by omega) (by norm_num)
      (hsq 13 h13 (by omega) hc.1 hc.2)
  obtain ⟨r, hsq'⟩ : ∃ r, ∀ p ∈ N.primeFactors, p ≠ q → p ≠ 13 → p ≠ r →
      N.factorization p = 2 := by
    rcases h13r with h1 | h1
    · exact ⟨r₂, fun p hp hpq hp13 hpr => hsq p hp hpq (by rw [← h1]; exact hp13) hpr⟩
    · exact ⟨r₁, fun p hp hpq hp13 hpr => hsq p hp hpq hpr (by rw [← h1]; exact hp13)⟩
  have h5r := five_eq h hq hodd hq3 hq17 h32 hqN h9 hsq' h13
  by_cases hr : r ∈ N.primeFactors ∧ r % 3 = 1 ∧ r ≠ 13
  · exact case_one h hq3 hq17 h32 hqN h9 hsq' h13 h5r hr.1 hr.2.1 hr.2.2
  · exact case_other h hq hodd hq3 hq4 hq17 h32 hqN h9 hsq' h13 h5r hr

/-- Let `N` be an odd perfect number with special prime `q ≡ 8 (mod 9)` in which every prime
factor other than `q`, `r₁` and `r₂` has exponent exactly 2. Then the exponent of 3 in `N` is
not 2. Whether this statement is new was not verified. -/
theorem two_exceptions_three_ne_two_of_mod_nine {N q r₁ r₂ : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hq9 : q % 9 = 8)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2) :
    N.factorization 3 ≠ 2 := by
  refine two_exceptions_three_ne_two_of_nine_dvd h hq hodd (by omega) ?_ hsq
  refine dvd_trans ?_ (OPNExample.sigma_prime_pow_dvd (a := 1) hq ?_)
  · rw [sigma_one_apply_prime_pow hq]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
    exact Nat.dvd_of_mod_eq_zero (by omega)
  · obtain ⟨j, hj⟩ := hodd
    exact ⟨j + 1, by omega⟩

open TwoExceptionFour in
/-- Let `N` be an odd perfect number with special prime `q ≠ 5` and `e₃ = 4`. Then the exponent
`e` of 11 in `N` is even, at least 6, and `e + 1` is divisible by neither 3 nor 5. Whether this
statement is new was not verified. -/
theorem eleven_of_three_pow_four {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hq5 : q ≠ 5) (h34 : N.factorization 3 = 4) :
    Even (N.factorization 11) ∧ 6 ≤ N.factorization 11 ∧ ¬ 3 ∣ N.factorization 11 + 1 ∧
      ¬ 5 ∣ N.factorization 11 + 1 := by
  have hN := h.ne_zero
  have hP := h.perfect
  have hq4 := (mod_four_special h hq hodd).1
  have p7 : Nat.Prime 7 := by norm_num
  have p11 : Nat.Prime 11 := by norm_num
  have p19 : Nat.Prime 19 := by norm_num
  have h11 : 11 ∣ N := OPNStarter.force_prime hP Nat.prime_three h34 p11 (by norm_num)
    (by rw [sigma_one_apply_prime_pow Nat.prime_three]; norm_num [Finset.sum_range_succ])
  have mem : ∀ {p : ℕ}, p.Prime → p ∣ N → p ∈ N.primeFactors := fun hp hd =>
    Nat.mem_primeFactors.mpr ⟨hp, hd, hN⟩
  have hev : ∀ {p : ℕ}, p.Prime → p ∣ N → p ≠ q → Even (N.factorization p) ∧
      2 ≤ N.factorization p := by
    intro p hp hd hpq
    obtain ⟨k, hk⟩ := even_factorization_of_ne h hq hodd hp hpq
    have := hp.factorization_pos_of_dvd hN hd
    exact ⟨⟨k, hk⟩, by omega⟩
  have e11 := hev p11 h11 (by omega)
  -- the prime factors 7 and 19 of `σ(11^2)` give an abundant divisor
  have from133 : 3 ∣ N.factorization 11 + 1 → False := by
    intro h3
    have hd : σ 1 (11 ^ 2) ∣ σ 1 (11 ^ N.factorization 11) :=
      OPNExample.sigma_prime_pow_dvd (a := 2) p11 h3
    have h7 : 7 ∣ N := OPNStarter.force_prime hP p11 rfl p7 (by norm_num)
      (dvd_trans (by rw [sigma_one_apply_prime_pow p11]; norm_num [Finset.sum_range_succ]) hd)
    have h19 : 19 ∣ N := OPNStarter.force_prime hP p11 rfl p19 (by norm_num)
      (dvd_trans (by rw [sigma_one_apply_prime_pow p11]; norm_num [Finset.sum_range_succ]) hd)
    have e7 := hev p7 h7 (by omega)
    have e19 := p19.factorization_pos_of_dvd hN h19
    exact abundant_four h Nat.prime_three p7 p11 p19 (i := 4) (j := 2) (k := 2) (l := 1)
      (by omega) e7.2 e11.2 e19 (by norm_num) (by norm_num) (by norm_num)
      (by
        rw [sigma_one_apply_prime_pow Nat.prime_three, sigma_one_apply_prime_pow p7,
          sigma_one_apply_prime_pow p11, sigma_one_apply_prime_pow p19]
        norm_num [Finset.sum_range_succ])
  have n3 : ¬ 3 ∣ N.factorization 11 + 1 := from133
  have n5 : ¬ 5 ∣ N.factorization 11 + 1 := by
    intro h5
    have hd : σ 1 (11 ^ 4) ∣ σ 1 (11 ^ N.factorization 11) :=
      OPNExample.sigma_prime_pow_dvd (a := 4) p11 h5
    have h5N : 5 ∣ N := OPNStarter.force_prime hP p11 rfl Nat.prime_five (by norm_num)
      (dvd_trans (by rw [sigma_one_apply_prime_pow p11]; norm_num [Finset.sum_range_succ]) hd)
    have e5 := hev Nat.prime_five h5N (Ne.symm hq5)
    have e11' : 4 ≤ N.factorization 11 := by omega
    exact abundant_four h Nat.prime_three Nat.prime_five p11 Nat.prime_two (i := 4) (j := 2)
      (k := 4) (l := 0) (by omega) e5.2 e11' (Nat.zero_le _) (by norm_num) (by norm_num)
      (by norm_num)
      (by
        rw [sigma_one_apply_prime_pow Nat.prime_three, sigma_one_apply_prime_pow Nat.prime_five,
          sigma_one_apply_prime_pow p11, sigma_one_apply_prime_pow Nat.prime_two]
        norm_num [Finset.sum_range_succ])
  refine ⟨e11.1, ?_, n3, n5⟩
  have h2 := e11.2
  obtain ⟨k, hk⟩ := e11.1
  rcases (by omega : N.factorization 11 = 2 ∨ N.factorization 11 = 4 ∨
    6 ≤ N.factorization 11) with e | e | e
  · exact absurd (by rw [e]) n3
  · exact absurd (by rw [e]) n5
  · exact e

/-- Let `N` be an odd perfect number with special prime `q ≠ 5` and `e₃ = 4`, in which every
prime factor other than `q`, `r₁` and `r₂` has exponent exactly 2. Then the two exceptions are
`3` and `11`, and the exponent `e` of 11 is even, at least 6, with `e + 1` divisible by neither
3 nor 5. Whether this statement is new was not verified. -/
theorem two_exceptions_three_pow_four {N q r₁ r₂ : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hq5 : q ≠ 5) (h34 : N.factorization 3 = 4)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2) :
    ((r₁ = 3 ∧ r₂ = 11) ∨ (r₁ = 11 ∧ r₂ = 3)) ∧ Even (N.factorization 11) ∧
      6 ≤ N.factorization 11 ∧ ¬ 3 ∣ N.factorization 11 + 1 ∧
      ¬ 5 ∣ N.factorization 11 + 1 := by
  have hE := eleven_of_three_pow_four h hq hodd hq5 h34
  have hN := h.ne_zero
  have hq4 := (mod_four_special h hq hodd).1
  have h3 : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three,
    Nat.dvd_of_factorization_pos (by omega), hN⟩
  have h11 : 11 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num,
    Nat.dvd_of_factorization_pos (by omega), hN⟩
  refine ⟨?_, hE⟩
  have a3 : 3 = r₁ ∨ 3 = r₂ := by
    by_contra hc
    push Not at hc
    have := hsq 3 h3 (by omega) hc.1 hc.2
    omega
  have a11 : 11 = r₁ ∨ 11 = r₂ := by
    by_contra hc
    push Not at hc
    have := hsq 11 h11 (by omega) hc.1 hc.2
    omega
  omega

end OddPerfect

#print axioms OddPerfect.two_exceptions_three_ne_two_of_nine_dvd
#print axioms OddPerfect.two_exceptions_three_ne_two_of_mod_nine
#print axioms OddPerfect.eleven_of_three_pow_four
#print axioms OddPerfect.two_exceptions_three_pow_four
