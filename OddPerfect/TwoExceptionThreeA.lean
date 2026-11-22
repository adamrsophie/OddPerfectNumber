import OddPerfect.TwoExceptionThreeAData
import OddPerfect.TwoExceptionThree
import OddPerfect.RestrainedFour

/-!
# Branch A of the exponent 2 at 3: the exponent of 13 is not 2

Let `N` be an odd perfect number with special prime `5` in which at most two prime factors
other than 5 have an exponent different from 2, and let `e₃ = 2`. By
`two_exceptions_five_three_sq_shape`, if `e₁₃ = 2` the exceptions are 61 and a prime
`x ≡ 1 (mod 5)`, `x ≠ 61`, with `5 ∣ e_x + 1`. The prime 5 and the square `13^2` each send a factor
3, so no other prime `≡ 1 (mod 3)` with exponent 2 divides `N`. Hence every prime factor of
`N` that is `1 (mod 3)` lies in `{13, 61, x}`, and `Φ₅(x) = σ(x^4)` divides `2N`.

* For `x < 116281` the data module gives a prime `t ∣ Φ₅(x)` outside `{5, 13, 61, x}` that is
  `1 (mod 3)`, or whose square sends a prime `1 (mod 3)` outside `{13, 61, x}`: a third sender.
* For `x ≥ 116281 = 341^2` the abundancy of `N` is below 2: the components `3^2`, `5^k`,
  `13^2`, `61^e`, `x^f` give at most `13/9 · 5/4 · 183/169 · 61/60 · x/(x-1)`, and the squares
  `t^2` with `t ≡ 2 (mod 3)` have `σ(t^2)` supported on `{13, 61, x}`; the Rankin bound
  `rankin_tail` with the fourth generator `P = 10^30 + 469` bounds their contribution.

Whether these statements are new was not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace TwoExceptionThreeA

/-- The Pratt certificate of the auxiliary prime `10^30 + 469`. -/
def certP : List (ℕ × ℕ × List ℕ) :=
  [(9181, 2, [2, 2, 3, 3, 3, 5, 17]), (10169, 3, [2, 2, 2, 31, 41]), (1021, 10, [2, 2, 3, 5, 17]),
   (30631, 3, [2, 3, 5, 1021]), (72091, 2, [2, 3, 3, 3, 3, 5, 89]),
   (3748733, 2, [2, 2, 13, 72091]),
   (25198422513010259, 2, [2, 113, 971, 30631, 3748733]),
   (1000000000000000000000000000469, 2,
     [2, 2, 7, 17, 19, 47, 9181, 10169, 25198422513010259])]

/-- The auxiliary prime `10^30 + 469`. -/
def bigP : ℕ := 1000000000000000000000000000469

theorem prime_P : Nat.Prime bigP :=
  Pratt.prime_of_checkPrime (c := certP) (by decide +kernel)

/-- A prime dividing `σ(p^2)` for an exact square `p^2` divides `N`. -/
private theorem force_sq {N p t : ℕ} (h : OddPerfect N) (hp : p.Prime)
    (he : N.factorization p = 2) (ht : t.Prime) (ht2 : t ≠ 2) (hd : t ∣ phi3 p) : t ∣ N :=
  OPNStarter.force_prime h.perfect hp he ht ht2 (by rwa [sigma_prime_sq hp])

/-- Three distinct prime factors whose component sums are divisible by 3 contradict
`e₃ = 2`. -/
private theorem three_senders {N a b c : ℕ} (h : OddPerfect N) (h32 : N.factorization 3 = 2)
    (ha : a ∈ N.primeFactors) (hb : b ∈ N.primeFactors) (hc : c ∈ N.primeFactors)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (sa : 3 ∣ σ 1 (a ^ N.factorization a)) (sb : 3 ∣ σ 1 (b ^ N.factorization b))
    (sc : 3 ∣ σ 1 (c ^ N.factorization c)) : False := by
  have hbal := OPNStarter.valuation_balance h.perfect 3
  have h23 : Nat.factorization 2 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  rw [h23, h32, zero_add] at hbal
  have hsub : ({a, b, c} : Finset ℕ) ⊆ N.primeFactors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun p => (σ 1 (p ^ N.factorization p)).factorization 3)
    (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton] at hle
  have pos : ∀ p ∈ N.primeFactors, 3 ∣ σ 1 (p ^ N.factorization p) →
      1 ≤ (σ 1 (p ^ N.factorization p)).factorization 3 := fun p hp hd =>
    (Nat.prime_three.dvd_iff_one_le_factorization
      (sigma_pos 1 _ (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)).ne').mp hd
  have := pos a ha sa
  have := pos b hb sb
  have := pos c hc sc
  omega

/-- The special component `5^k` sends a factor 3. -/
private theorem five_sends_three {N : ℕ} (hodd : Odd (N.factorization 5)) :
    3 ∣ σ 1 (5 ^ N.factorization 5) := by
  refine dvd_trans ?_ (OPNExample.sigma_prime_pow_dvd (a := 1) Nat.prime_five ?_)
  · rw [sigma_one_apply_prime_pow Nat.prime_five]
    norm_num [Finset.sum_range_succ]
  · obtain ⟨j, hj⟩ := hodd
    exact ⟨j + 1, by omega⟩

/-- `σ(x^4) = Φ₅(x)`. -/
theorem sigma_four {x : ℕ} (hx : x.Prime) : σ 1 (x ^ 4) = phi5 x := by
  rw [sigma_one_apply_prime_pow hx]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, phi5]
  ring

/-- `Φ₅(x)` is odd for odd `x`. -/
private theorem phi5_odd {x : ℕ} (hx : x % 2 = 1) : phi5 x % 2 = 1 := by
  unfold phi5
  simp [Nat.add_mod, Nat.pow_mod, hx]

/-- A product of two prime powers from the support. -/
private theorem eq_two_pow {V p q : ℕ} (hV : V ≠ 0) (hpq : p ≠ q)
    (hs : V.primeFactors ⊆ {p, q}) :
    V = p ^ V.factorization p * q ^ V.factorization q := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hV]
  rw [Finsupp.prod_of_support_subset _ (s := {p, q}) (by rwa [Nat.support_factorization])
    _ (fun _ _ => pow_zero _), Finset.prod_pair hpq]

/-- No value `13^a 61^b < 10^20` is `t^2 + t + 1` with `t ≥ 10`. -/
private theorem no_smooth_root {t a b : ℕ} (ht : 10 ≤ t) (ha : a < 19) (hb : b < 12)
    (hz : phi3 t = 13 ^ a * 61 ^ b) : 10 ^ 20 ≤ phi3 t := by
  have hT := tabOK_true
  simp only [tabOK, List.all_eq_true, List.mem_range] at hT
  have h := hT a ha b hb
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  set r := rootTab.getD (12 * a + b) 0
  have hsq : 4 * (13 ^ a * 61 ^ b) - 3 = (2 * t + 1) * (2 * t + 1) := by
    rw [← hz]
    apply Nat.sub_eq_of_eq_add
    unfold phi3
    ring
  rcases h with (h | ⟨h1, h2⟩) | ⟨h1, h2⟩
  · rw [hz]; exact h
  · rw [hsq] at h1 h2
    have := Nat.mul_self_lt_mul_self_iff.mp h1
    have := Nat.mul_self_lt_mul_self_iff.mp h2
    omega
  · rw [hsq] at h1
    have := Nat.mul_self_inj.mp h1
    omega


/-- A square `t^2` whose `σ` is supported on `{13, 61, x}` meets the Rankin hypotheses. -/
private theorem tail_triple {t x : ℕ} (ht10 : 10 ≤ t)
    (hsub : (phi3 t).primeFactors ⊆ {13, 61, x}) :
    (phi3 t).primeFactors ⊆ {13, 61, x, bigP} ∧
      (¬ x ∣ phi3 t → ¬ bigP ∣ phi3 t → 10 ^ 20 ≤ phi3 t) := by
  refine ⟨fun u hu => ?_, fun hnx _ => ?_⟩
  · have := hsub hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
    tauto
  · have hsub2 : (phi3 t).primeFactors ⊆ {13, 61} := by
      intro u hu
      have := hsub hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      rcases this with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
      · subst h'
        exact absurd (Nat.dvd_of_mem_primeFactors hu) hnx
    have hV : phi3 t ≠ 0 := by unfold phi3; omega
    have heq := eq_two_pow hV (by norm_num) hsub2
    by_contra hc
    push Not at hc
    have ha : (phi3 t).factorization 13 < 19 := by
      by_contra ha
      push Not at ha
      have : 13 ^ 19 ≤ phi3 t := by
        calc 13 ^ 19 ≤ 13 ^ (phi3 t).factorization 13 := Nat.pow_le_pow_right (by norm_num) ha
          _ ≤ phi3 t := Nat.le_of_dvd (Nat.pos_of_ne_zero hV)
              (Nat.ordProj_dvd _ _)
      exact absurd (lt_of_le_of_lt this hc) (by norm_num)
    have hb : (phi3 t).factorization 61 < 12 := by
      by_contra hb
      push Not at hb
      have : 61 ^ 12 ≤ phi3 t := by
        calc 61 ^ 12 ≤ 61 ^ (phi3 t).factorization 61 := Nat.pow_le_pow_right (by norm_num) hb
          _ ≤ phi3 t := Nat.le_of_dvd (Nat.pos_of_ne_zero hV)
              (Nat.ordProj_dvd _ _)
      exact absurd (lt_of_le_of_lt this hc) (by norm_num)
    exact absurd (no_smooth_root ht10 ha hb heq) (not_le.mpr hc)

open RestrainedFour in
/-- The abundancy bound for `x ≥ 116281`. -/
private theorem abundant_tail {N x : ℕ} (h : OddPerfect N) (hx : x.Prime) (hlt : 116281 ≤ x)
    (hx5 : x % 5 = 1) (hx61 : x ≠ 61) (h32 : N.factorization 3 = 2)
    (h132 : N.factorization 13 = 2) (hK0 : ({3, 5, 13, 61, x} : Finset ℕ) ⊆ N.primeFactors)
    (hT0 : ∀ t ∈ N.primeFactors, t ≠ 3 → t ≠ 5 → t ≠ 13 → t ≠ 61 → t ≠ x →
      N.factorization t = 2 ∧ 10 ≤ t ∧ (phi3 t).primeFactors ⊆ {13, 61, x}) : False := by
  have p13 : Nat.Prime 13 := by norm_num
  have p61 : Nat.Prime 61 := by norm_num
  have hx3 : x ≠ 3 := by rintro rfl; norm_num at hx5
  have hx5' : x ≠ 5 := by rintro rfl; norm_num at hx5
  have hx13 : x ≠ 13 := by rintro rfl; norm_num at hx5
  have hxP : x ≠ bigP := by rintro rfl; norm_num [bigP] at hx5
  obtain ⟨K, hKd⟩ : ∃ K : Finset ℕ, K = {3, 5, 13, 61, x} := ⟨_, rfl⟩
  have hK : K ⊆ N.primeFactors := hKd ▸ hK0
  obtain ⟨c, hcd⟩ : ∃ c : ℕ → ℚ, c = fun p : ℕ => if p = 3 then 13 / 9 else
    if p = 5 then 5 / 4 else if p = 13 then 183 / 169 else if p = 61 then 61 / 60 else
    (p : ℚ) / (p - 1) := ⟨_, rfl⟩
  have hC : ∀ p ∈ K, abundancy (p ^ N.factorization p) ≤ c p := by
    intro p hp
    simp only [hKd, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · rw [h32, abundancy_prime_pow Nat.prime_three]
      norm_num [hcd, Finset.sum_range_succ]
    · have := abundancy_prime_pow_lt Nat.prime_five (N.factorization 5)
      simp only [hcd]; norm_num at this ⊢; linarith
    · rw [h132, abundancy_prime_pow p13]
      norm_num [hcd, Finset.sum_range_succ]
    · have := abundancy_prime_pow_lt p61 (N.factorization 61)
      simp only [hcd]; norm_num at this ⊢; linarith
    · simp only [hcd, if_neg hx3, if_neg hx5', if_neg hx13, if_neg hx61]
      exact (abundancy_prime_pow_lt hx _).le
  have mT : ∀ t ∈ N.primeFactors \ K, t ∈ N.primeFactors ∧ t ≠ 3 ∧ t ≠ 5 ∧ t ≠ 13 ∧ t ≠ 61 ∧
      t ≠ x := by
    intro t ht
    simp only [hKd, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at ht
    push Not at ht
    exact ht
  have hT : ∀ t ∈ N.primeFactors \ K, N.factorization t = 2 := fun t ht => by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := mT t ht
    exact (hT0 t a1 a2 a3 a4 a5 a6).1
  have hTr : ∀ t ∈ N.primeFactors \ K, 10 ≤ t ∧
      (phi3 t).primeFactors ⊆ {13, 61, x, bigP} ∧
      (¬ x ∣ phi3 t → ¬ bigP ∣ phi3 t → 10 ^ 20 ≤ phi3 t) := fun t ht => by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := mT t ht
    obtain ⟨-, b1, b2⟩ := hT0 t a1 a2 a3 a4 a5 a6
    exact ⟨b1, tail_triple b1 b2⟩
  have hS := rankin_tail (N.primeFactors \ K) (g₁ := 13) (g₂ := 61) (g₃ := x) (g₄ := bigP)
    (B := 10 ^ 20) (α₁ := 5 / 18) (α₂ := 9 / 70) (α₃ := 1 / 341) (α₄ := 1 / 10 ^ 15)
    (β₁ := 53 / 100) (β₂ := 9 / 25) (β := 1 / 10 ^ 5)
    hx prime_P (by norm_num) (by omega) (by norm_num [bigP]) (Ne.symm hx61) (by norm_num [bigP]) hxP
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by
      have : (116281 : ℚ) ≤ x := by exact_mod_cast hlt
      norm_num
      linarith)
    (by norm_num [bigP])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hTr
  have hxq : (116281 : ℚ) ≤ x := by exact_mod_cast hlt
  have hx1 : (0 : ℚ) < x - 1 := by linarith only [hxq]
  have hxb : (x : ℚ) / ((x : ℚ) - 1) ≤ 116281 / 116280 := by
    rw [div_le_div_iff₀ hx1 (by norm_num)]
    linarith only [hxq]
  have e3 : c 3 = 13 / 9 := by norm_num [hcd]
  have e5 : c 5 = 5 / 4 := by norm_num [hcd]
  have e13 : c 13 = 183 / 169 := by norm_num [hcd]
  have e61 : c 61 = 61 / 60 := by norm_num [hcd]
  have ex : c x = (x : ℚ) / ((x : ℚ) - 1) := by
    simp only [hcd, if_neg hx3, if_neg hx5', if_neg hx13, if_neg hx61]
  have hprod : ∏ p ∈ K, c p ≤ 13 / 9 * (5 / 4 * (183 / 169 * (61 / 60 * (116281 / 116280)))) := by
    rw [hKd,
      Finset.prod_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton]; clear * - hx3 hx5' hx13 hx61; omega),
      Finset.prod_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton]; clear * - hx3 hx5' hx13 hx61; omega),
      Finset.prod_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton]; clear * - hx3 hx5' hx13 hx61; omega),
      Finset.prod_insert (by
          simp only [Finset.mem_singleton]; clear * - hx3 hx5' hx13 hx61; omega),
      Finset.prod_singleton, e3, e5, e13, e61, ex]
    gcongr
  exact abundancy_close h K hK c hC _ hT hS (lt_of_le_of_lt hprod (by norm_num))

end TwoExceptionThreeA

open TwoExceptionThreeA RestrainedFour in
/-- Let `N` be an odd perfect number with special prime `5` in which every prime factor other
than `5`, `r₁` and `r₂` has exponent exactly 2, and let `e₃ = 2`. Then `e₁₃ ≠ 2`. Whether this
statement is new was not verified. -/
theorem two_exceptions_five_three_sq_thirteen_ne_two {N r₁ r₂ : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization 5))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ 5 → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2)
    (h32 : N.factorization 3 = 2) : N.factorization 13 ≠ 2 := by
  intro h132
  have hN := h.ne_zero
  have hP := h.perfect
  have mem : ∀ {p : ℕ}, p.Prime → p ∣ N → p ∈ N.primeFactors := fun hp hd =>
    Nat.mem_primeFactors.mpr ⟨hp, hd, hN⟩
  obtain ⟨x, hx, hxN, hx5, hxe, hx61, hbr⟩ := two_exceptions_five_three_sq_shape h hodd hsq h32
  have hsq' : ∀ p ∈ N.primeFactors, p ≠ 5 → p ≠ 61 → p ≠ x → N.factorization p = 2 := by
    rcases hbr with ⟨-, hb⟩ | ⟨hne, -⟩
    · exact hb
    · exact absurd h132 hne
  have p13 : Nat.Prime 13 := by norm_num
  have p61 : Nat.Prime 61 := by norm_num
  have h13 : 13 ∣ N := OPNStarter.thirteen_dvd_of_three_sq hP h32
  have h61 : 61 ∣ N := force_sq h p13 h132 p61 (by norm_num) (by norm_num [phi3])
  have h3 : 3 ∣ N := Nat.dvd_of_factorization_pos (by omega)
  have h5 : 5 ∣ N := Nat.dvd_of_factorization_pos hodd.pos.ne'
  have m5 := mem Nat.prime_five h5
  have m13 := mem p13 h13
  have s5 := five_sends_three hodd
  have s13 : 3 ∣ σ 1 (13 ^ N.factorization 13) := by
    rw [h132, sigma_prime_sq p13]; exact (three_dvd_phi3_iff 13).mpr (by norm_num)
  -- no further square prime `≡ 1 (mod 3)`
  have nosend : ∀ p, p.Prime → p ∣ N → p % 3 = 1 → p ≠ 13 → N.factorization p = 2 → False :=
    fun p hp hd h31 hp13 he =>
      three_senders h h32 m5 m13 (mem hp hd) (by norm_num) (by omega) (Ne.symm hp13) s5 s13
        (by rw [he, sigma_prime_sq hp]; exact (three_dvd_phi3_iff p).mpr h31)
  -- the prime `x`
  have hx2 : x % 2 = 1 := by
    rcases hx.eq_two_or_odd with h2 | h2
    · omega
    · exact h2
  have hx3 : x ≠ 3 := by rintro rfl; norm_num at hx5
  have hx5' : x ≠ 5 := by rintro rfl; norm_num at hx5
  have hx13 : x ≠ 13 := by rintro rfl; norm_num at hx5
  have hΦ : ∀ t, t.Prime → t ∣ phi5 x → t ∣ N := by
    intro t ht htd
    have ht2 : t ≠ 2 := by
      rintro rfl
      have := phi5_odd hx2
      omega
    refine OPNStarter.force_prime hP hx rfl ht ht2 (dvd_trans ?_
      (OPNExample.sigma_prime_pow_dvd (a := 4) hx hxe))
    rwa [sigma_four hx]
  -- a square prime `t ≡ 2 (mod 3)`: every prime factor of `σ(t^2)` lies in `{13, 61, x}`
  have supp : ∀ t, t.Prime → t ∣ N → N.factorization t = 2 → t % 3 ≠ 1 →
      ∀ u, u.Prime → u ∣ phi3 t → u = 13 ∨ u = 61 ∨ u = x := by
    intro t ht htN het ht3 u hu hut
    have hu2 : u ≠ 2 := by
      rintro rfl
      exact absurd (Nat.mod_eq_zero_of_dvd hut) (by have := Nat.odd_iff.mp (phi3_odd t); omega)
    have hu3 : u ≠ 3 := by
      rintro rfl
      exact ht3 ((three_dvd_phi3_iff t).mp hut)
    have huN := force_sq h ht het hu hu2 hut
    have hu1 := prime_dvd_phi3_mod_three hu hu3 hut
    by_contra hc
    push Not at hc
    exact nosend u hu huN hu1 hc.1 (hsq' u (mem hu huN) (by omega) hc.2.1 hc.2.2)
  by_cases hlt : x < 116281
  · -- the data module
    obtain ⟨t, ht, htd, ht5, ht61, htx, ht13, hcase⟩ :=
      good_of_lt hx (by omega) hx61 (by have := hx.two_le; omega) hlt
    have htN := hΦ t ht htd
    have het := hsq' t (mem ht htN) ht5 ht61 htx
    by_cases ht3 : t % 3 = 1
    · exact nosend t ht htN ht3 ht13 het
    · rcases hcase with h1 | ⟨u, hu, hut, hu13, hu61, hux⟩
      · exact ht3 h1
      · rcases supp t ht htN het ht3 u hu hut with h' | h' | h' <;> contradiction
  · -- the abundancy bound
    push Not at hlt
    refine abundant_tail h hx hlt hx5 hx61 h32 h132 ?_ ?_
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact mem Nat.prime_three h3
      · exact m5
      · exact m13
      · exact mem p61 h61
      · exact mem hx hxN
    · intro t htm ht3' ht5 ht13 ht61 htx
      have het := hsq' t htm ht5 ht61 htx
      have htp := Nat.prime_of_mem_primeFactors htm
      have htN := Nat.dvd_of_mem_primeFactors htm
      have ht7 : t ≠ 7 := by
        rintro rfl
        exact not_105_dvd h (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 15 7)
          (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 5) h3 h5) htN)
      have ht2 : t ≠ 2 := by
        rintro rfl
        exact h.not_two_dvd htN
      have ht10 : 10 ≤ t := by
        by_contra hc
        push Not at hc
        clear * - htp ht2 ht3' ht5 ht7 hc
        interval_cases t <;> first | omega | norm_num at htp
      have ht31 : t % 3 ≠ 1 := fun h31 => nosend t htp htN h31 ht13 het
      have hs := supp t htp htN het ht31
      have hsub : (phi3 t).primeFactors ⊆ {13, 61, x} := by
        intro u hu
        have hup := Nat.prime_of_mem_primeFactors hu
        have hud := Nat.dvd_of_mem_primeFactors hu
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact hs u hup hud
      exact ⟨het, ht10, hsub⟩

open TwoExceptionThreeA in
/-- The corollary: with special prime `5`, at most two exceptional exponents and `e₃ = 2`, the
configuration is branch B: `e₁₃ ≠ 2`, `3 ∤ e₁₃ + 1`, and there is a prime `s ≠ 61`,
`s ≡ 1 (mod 5)`, dividing `N` with `5 ∣ e_s + 1` such that every prime factor other than
`5`, `13`, `s` has exponent 2. Whether this statement is new was not verified. -/
theorem two_exceptions_five_three_sq_branch_b {N r₁ r₂ : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization 5))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ 5 → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2)
    (h32 : N.factorization 3 = 2) :
    N.factorization 13 ≠ 2 ∧ ¬ 3 ∣ N.factorization 13 + 1 ∧
      ∃ s, s.Prime ∧ s ∣ N ∧ s % 5 = 1 ∧ 5 ∣ N.factorization s + 1 ∧ s ≠ 61 ∧
        ∀ p ∈ N.primeFactors, p ≠ 5 → p ≠ 13 → p ≠ s → N.factorization p = 2 := by
  have hne := two_exceptions_five_three_sq_thirteen_ne_two h hodd hsq h32
  obtain ⟨s, hs, hsN, hs5, hse, hs61, hbr⟩ := two_exceptions_five_three_sq_shape h hodd hsq h32
  rcases hbr with ⟨h2, -⟩ | ⟨-, h3, hb⟩
  · exact absurd h2 hne
  · exact ⟨hne, h3, s, hs, hsN, hs5, hse, hs61, hb⟩

end OddPerfect

#print axioms OddPerfect.TwoExceptionThreeA.prime_P
#print axioms OddPerfect.TwoExceptionThreeA.sigma_four
#print axioms OddPerfect.two_exceptions_five_three_sq_thirteen_ne_two
#print axioms OddPerfect.two_exceptions_five_three_sq_branch_b
