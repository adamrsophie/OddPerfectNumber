import OddPerfect.TwoExceptionThreeBData
import OddPerfect.TwoExceptionThreeA

/-!
# Branch B of the exponent 2 at 3, and the exponent of 3

Let `N` be an odd perfect number with special prime `5` in which at most two prime factors
other than 5 have an exponent different from 2, and let `e₃ = 2`. By
`two_exceptions_five_three_sq_branch_b` the exceptions are 13 and a prime `s ≡ 1 (mod 5)`,
`s ≠ 61`, with `5 ∣ e_s + 1`, so `Φ₅(s) = σ(s^4)` divides `2N`.

The structure of branch B (`branch_b_ctx`): 7 does not divide `N`; the special component `5^k`
sends a factor 3, so at most one prime factor `t ≡ 1 (mod 3)` outside `{13, s}` divides `N`
(each such prime has exponent 2 and sends a factor 3); and every prime factor of `σ(p^2)`, for a
prime factor `p ∉ {5, 13, s}`, divides `N`.

* For `s < 19881` the walk over `s` of the data module closes every prime `s ≡ 1 (mod 10)` by a
  chain of forced primes ending at 7 or at two primes `≡ 1 (mod 3)` outside `{13, s}`.
* For `s ≥ 19881` the prime `t`, if it exists, has `t^2 + t + 1 = 3 · 13^a · s^b`. For
  `t < 30001` the walk over `t` excludes this; for `t ≥ 30001`, and when there is no `t`, the
  abundancy of `N` is below 2 by `rankin_tail` with the generators `13`, a large auxiliary
  prime, `s` and `t` (or a second auxiliary prime).

Whether these statements are new was not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace TwoExceptionThreeB

open TwoExceptionThreeA

/-- A second auxiliary prime. -/
def bigQ : ℕ := 1000000000000000000000000000529

/-- A third auxiliary prime. -/
def bigR : ℕ := 1000000000000000000000000000577

theorem prime_Q : Nat.Prime bigQ :=
  Pratt.prime_of_checkPrime (c := [(2549, 2, [2, 2, 7, 7, 13]), (20393, 3, [2, 2, 2, 2549]),
    (11579, 2, [2, 7, 827]), (23159, 11, [2, 11579]), (57709, 2, [2, 2, 3, 3, 7, 229]),
    (1009, 11, [2, 2, 2, 2, 3, 3, 7]), (12109, 6, [2, 2, 3, 1009]), (37013, 2, [2, 2, 19, 487]),
    (252502687, 6, [2, 3, 3, 379, 37013]),
    (2293166277662251, 2, [2, 3, 5, 5, 5, 12109, 252502687]),
    (1000000000000000000000000000529, 3, [2, 2, 2, 2, 20393, 23159, 57709, 2293166277662251])])
    (by decide +kernel)

theorem prime_R : Nat.Prime bigR :=
  Pratt.prime_of_checkPrime (c := [(422761, 7, [2, 2, 2, 3, 5, 13, 271]),
    (58481, 6, [2, 2, 2, 2, 5, 17, 43]), (350887, 5, [2, 3, 58481]),
    (16842577, 7, [2, 2, 2, 2, 3, 350887]), (1280035853, 2, [2, 2, 19, 16842577]),
    (662640146054156243, 2, [2, 7, 113, 337, 971, 1280035853]),
    (36959416786316618609569, 13, [2, 2, 2, 2, 2, 3, 7, 83, 662640146054156243]),
    (1000000000000000000000000000577, 3,
      [2, 2, 2, 2, 2, 2, 422761, 36959416786316618609569])])
    (by decide +kernel)

/-- A large prime avoiding two given numbers. -/
theorem dummy_avoid (x y : ℕ) : ∃ g, g.Prime ∧ 10 ^ 30 ≤ g ∧ g ≠ x ∧ g ≠ y := by
  by_cases h1 : bigP ≠ x ∧ bigP ≠ y
  · exact ⟨bigP, prime_P, by norm_num [bigP], h1.1, h1.2⟩
  by_cases h2 : bigQ ≠ x ∧ bigQ ≠ y
  · exact ⟨bigQ, prime_Q, by norm_num [bigQ], h2.1, h2.2⟩
  simp only [not_and_or, not_not] at h1 h2
  refine ⟨bigR, prime_R, by norm_num [bigR], ?_, ?_⟩
  all_goals
    intro h3
    simp only [bigP, bigQ, bigR] at h1 h2 h3
    omega

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

/-- `Φ₅(x)` is odd for odd `x`. -/
private theorem phi5_odd {x : ℕ} (hx : x % 2 = 1) : phi5 x % 2 = 1 := by
  unfold phi5
  simp [Nat.add_mod, Nat.pow_mod, hx]

/-- No value `13^a < 10^20` is `t^2 + t + 1` with `t ≥ 10`. -/
private theorem no_thirteen_root {t a : ℕ} (ht : 10 ≤ t) (ha : a < 19)
    (hz : phi3 t = 13 ^ a) : 10 ^ 20 ≤ phi3 t := by
  have hT := tabOK_true
  simp only [tabOK, List.all_eq_true, List.mem_range] at hT
  have h := hT a ha 0 (by norm_num)
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, pow_zero,
    mul_one, add_zero] at h
  have hsq : 4 * 13 ^ a - 3 = (2 * t + 1) * (2 * t + 1) := by
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

/-- A square `u^2` with `σ(u^2)` supported on `{13, s, g}` meets the Rankin hypotheses. -/
private theorem tail_triple {u s g : ℕ} (hu : 10 ≤ u) (hsub : (phi3 u).primeFactors ⊆ {13, s, g})
    (g2 : ℕ) : (phi3 u).primeFactors ⊆ {13, g2, s, g} ∧
      (¬ s ∣ phi3 u → ¬ g ∣ phi3 u → 10 ^ 20 ≤ phi3 u) := by
  refine ⟨fun q hq => ?_, fun hns hng => ?_⟩
  · have := hsub hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
    tauto
  have hV : phi3 u ≠ 0 := by unfold phi3; omega
  have h13 : (phi3 u).primeFactors ⊆ {13} := by
    intro q hq
    have := hsub hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
    rcases this with h' | h' | h'
    · exact h'
    · subst h'; exact absurd (Nat.dvd_of_mem_primeFactors hq) hns
    · subst h'; exact absurd (Nat.dvd_of_mem_primeFactors hq) hng
  have heq := eq_pow_of_primeFactors hV (fun q hq hqd =>
    Finset.mem_singleton.mp (h13 (Nat.mem_primeFactors.mpr ⟨hq, hqd, hV⟩)))
  by_contra hc
  push Not at hc
  have ha : (phi3 u).factorization 13 < 19 := by
    by_contra ha
    push Not at ha
    have : 13 ^ 19 ≤ phi3 u := by
      calc 13 ^ 19 ≤ 13 ^ (phi3 u).factorization 13 := Nat.pow_le_pow_right (by norm_num) ha
        _ ≤ phi3 u := Nat.le_of_dvd (Nat.pos_of_ne_zero hV) (Nat.ordProj_dvd _ _)
    exact absurd (lt_of_le_of_lt this hc) (by norm_num)
  exact absurd (no_thirteen_root hu ha heq) (not_le.mpr hc)

/-- The abundancy of a square. -/
private theorem abundancy_sq_le {t : ℕ} (ht : t.Prime) (h30 : 30000 ≤ t) :
    abundancy (t ^ 2) ≤ 1 + 1 / 30000 + 1 / 30000 ^ 2 := by
  rw [abundancy_prime_pow ht]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
  have h0 : (0 : ℚ) ≤ (t : ℚ)⁻¹ := by positivity
  have hti : (t : ℚ)⁻¹ ≤ 1 / 30000 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast h30)
  have := pow_le_pow_left₀ h0 hti 2
  linarith

open RestrainedFour in
/-- The abundancy bound for `s ≥ 19881`. -/
private theorem tail_core {N s g2 g4 : ℕ} (h : OddPerfect N) (hs : s.Prime) (hs0 : 19881 ≤ s)
    (p4 : g4.Prime) (h2 : 10 ^ 30 ≤ g2) (h4 : 30000 ≤ g4)
    (d2 : 13 ≠ s) (d4 : g2 ≠ s) (d5 : g2 ≠ g4) (d6 : s ≠ g4)
    (K : Finset ℕ) (hK : K ⊆ N.primeFactors) (c : ℕ → ℚ)
    (hC : ∀ p ∈ K, abundancy (p ^ N.factorization p) ≤ c p)
    (hprod : ∏ p ∈ K, c p ≤ 13 / 9 * (5 / 4 * (13 / 12 * (19881 / 19880 *
      (1 + 1 / 30000 + 1 / 30000 ^ 2)))))
    (hT : ∀ u ∈ N.primeFactors \ K, N.factorization u = 2 ∧ 10 ≤ u ∧
      (phi3 u).primeFactors ⊆ {13, s, g4}) : False := by
  have hS := rankin_tail (N.primeFactors \ K) (g₁ := 13) (g₂ := g2) (g₃ := s) (g₄ := g4)
    (B := 10 ^ 20) (α₁ := 5 / 18) (α₂ := 1 / 10 ^ 15) (α₃ := 1 / 141) (α₄ := 1 / 173)
    (β₁ := 53 / 100) (β₂ := 1 / 10 ^ 7) (β := 1 / 10 ^ 5)
    hs p4 (by omega) d2 (by omega) d4 d5 d6
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by
      have : (10 ^ 30 : ℚ) ≤ g2 := by exact_mod_cast h2
      norm_num
      linarith)
    (by
      have : (19881 : ℚ) ≤ s := by exact_mod_cast hs0
      norm_num
      linarith)
    (by
      have : (30000 : ℚ) ≤ g4 := by exact_mod_cast h4
      norm_num
      linarith)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by
      have : (10 ^ 30 : ℚ) ≤ g2 := by exact_mod_cast h2
      norm_num
      linarith)
    (by norm_num)
    (fun u hu => ⟨(hT u hu).2.1, tail_triple (hT u hu).2.1 (hT u hu).2.2 g2⟩)
  exact abundancy_close h K hK c hC _ (fun u hu => (hT u hu).1) hS
    (lt_of_le_of_lt hprod (by norm_num))

end TwoExceptionThreeB

open TwoExceptionThreeA TwoExceptionThreeB in
/-- The structure of branch B. Let `N` be an odd perfect number with special prime `5` and
`e₃ = 2`, let `s` be a prime with `5 ∣ e_s + 1`, and let every prime factor other than `5`, `13`
and `s` have exponent 2. Then `Ctx N s` holds: every prime
factor of `Φ₅(s)` other than 2 divides `N`, every prime factor other than 2 of `σ(v^2)` for a
prime factor `v ∉ {5, 13, s}` divides `N`, two distinct prime factors `≡ 1 (mod 3)` outside
`{13, s}` do not exist, and `7 ∤ N`. Whether this statement is new was not verified. -/
theorem branch_b_ctx {N s : ℕ} (h : OddPerfect N) (hodd : Odd (N.factorization 5))
    (h32 : N.factorization 3 = 2) (hs : s.Prime) (hse : 5 ∣ N.factorization s + 1)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ 5 → p ≠ 13 → p ≠ s → N.factorization p = 2) :
    Ctx N s := by
  have hN := h.ne_zero
  have hP := h.perfect
  have mem : ∀ {p : ℕ}, p.Prime → p ∣ N → p ∈ N.primeFactors := fun hp hd =>
    Nat.mem_primeFactors.mpr ⟨hp, hd, hN⟩
  have h3 : 3 ∣ N := Nat.dvd_of_factorization_pos (by omega)
  have h5 : 5 ∣ N := Nat.dvd_of_factorization_pos hodd.pos.ne'
  have m5 := mem Nat.prime_five h5
  have s5 := five_sends_three hodd
  refine ⟨fun w hw hw2 hwd => ?_, fun v w hv hvN hv5 hv13 hvs hw hw2 hwd => ?_,
    fun a b ha hb haN hbN hab ha3 hb3 ha13 hb13 has hbs => ?_, fun h7 => ?_⟩
  · refine OPNStarter.force_prime hP hs rfl hw hw2 (dvd_trans ?_
      (OPNExample.sigma_prime_pow_dvd (a := 4) hs hse))
    rwa [sigma_four hs]
  · exact force_sq h hv (hsq v (mem hv hvN) hv5 hv13 hvs) hw hw2 hwd
  · have sq : ∀ p, p.Prime → p ∣ N → p % 3 = 1 → p ≠ 13 → p ≠ s →
        3 ∣ σ 1 (p ^ N.factorization p) := fun p hp hpN hp3 hp13 hps => by
      rw [hsq p (mem hp hpN) (by omega) hp13 hps, sigma_prime_sq hp]
      exact (three_dvd_phi3_iff p).mpr hp3
    exact three_senders h h32 m5 (mem ha haN) (mem hb hbN) (by omega) (by omega) hab s5
      (sq a ha haN ha3 ha13 has) (sq b hb hbN hb3 hb13 hbs)
  · exact not_105_dvd h (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 15 7)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 5) h3 h5) h7)

open TwoExceptionThreeA TwoExceptionThreeB in
/-- Branch B is empty: an odd perfect number with special prime `5` in which every prime factor
other than `5`, `r₁` and `r₂` has exponent exactly 2 does not have `e₃ = 2`. Whether this
statement is new was not verified. -/
theorem two_exceptions_five_three_ne_two {N r₁ r₂ : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization 5))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ 5 → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2) :
    N.factorization 3 ≠ 2 := by
  intro h32
  obtain ⟨-, -, s, hs, hsN, hs5, hse, hs61, hsqB⟩ :=
    two_exceptions_five_three_sq_branch_b h hodd hsq h32
  have hN := h.ne_zero
  have mem : ∀ {p : ℕ}, p.Prime → p ∣ N → p ∈ N.primeFactors := fun hp hd =>
    Nat.mem_primeFactors.mpr ⟨hp, hd, hN⟩
  have hs5' : s ≠ 5 := by rintro rfl; norm_num at hs5
  have hs13 : s ≠ 13 := by rintro rfl; norm_num at hs5
  have hs3 : s ≠ 3 := by rintro rfl; norm_num at hs5
  have hc := branch_b_ctx h hodd h32 hs hse hsqB
  have hs2 : s % 2 = 1 := by
    rcases hs.eq_two_or_odd with h2 | h2
    · omega
    · exact h2
  have h3 : 3 ∣ N := Nat.dvd_of_factorization_pos (by omega)
  have h5 : 5 ∣ N := Nat.dvd_of_factorization_pos hodd.pos.ne'
  have h13 : 13 ∣ N := OPNStarter.thirteen_dvd_of_three_sq h.perfect h32
  by_cases hlt : s < 19881
  · exact s_closed hs (by omega) hs61 (by have := hs.two_le; omega) hlt N hc
  push Not at hlt
  -- the components of `3`, `5`, `13`, `s`
  obtain ⟨c, hcd⟩ : ∃ c : ℕ → ℚ, c = fun p : ℕ => if p = 3 then 13 / 9 else
      if p = 5 then 5 / 4 else if p = 13 then 13 / 12 else if p = s then 19881 / 19880 else
      1 + 1 / 30000 + 1 / 30000 ^ 2 := ⟨_, rfl⟩
  have c3 : c 3 = 13 / 9 := by simp [hcd]
  have c5 : c 5 = 5 / 4 := by simp [hcd]
  have c13 : c 13 = 13 / 12 := by simp [hcd]
  have cs : c s = 19881 / 19880 := by simp [hcd, hs3, hs5', hs13]
  have hC4 : ∀ p, p = 3 ∨ p = 5 ∨ p = 13 ∨ p = s → abundancy (p ^ N.factorization p) ≤ c p := by
    rintro p (rfl | rfl | rfl | hp)
    · rw [c3, h32, abundancy_prime_pow Nat.prime_three]
      norm_num [Finset.sum_range_succ]
    · rw [c5]
      have := abundancy_prime_pow_lt Nat.prime_five (N.factorization 5)
      norm_num at this ⊢
      linarith
    · rw [c13]
      have := abundancy_prime_pow_lt (by norm_num : Nat.Prime 13) (N.factorization 13)
      norm_num at this ⊢
      linarith
    · rw [hp, cs]
      refine (abundancy_prime_pow_lt hs _).le.trans ?_
      have hq : (19881 : ℚ) ≤ s := by exact_mod_cast hlt
      have hq1 : (0 : ℚ) < s - 1 := by linarith only [hq]
      rw [div_le_div_iff₀ hq1 (by norm_num)]
      linarith only [hq]
  have mK4 : ∀ p, p = 3 ∨ p = 5 ∨ p = 13 ∨ p = s → p ∈ N.primeFactors := by
    rintro p (rfl | rfl | rfl | rfl)
    · exact mem Nat.prime_three h3
    · exact mem Nat.prime_five h5
    · exact mem (by norm_num) h13
    · exact mem hs hsN
  -- a square prime `u ∉ {3, 5, 13, s, t}`
  have usq : ∀ u ∈ N.primeFactors, u ≠ 3 → u ≠ 5 → u ≠ 13 → u ≠ s → u % 3 ≠ 1 →
      N.factorization u = 2 ∧ 10 ≤ u ∧ ∀ q, q.Prime → q ∣ phi3 u → q ∣ N ∧ q % 3 = 1 := by
    intro u hu hu3 hu5 hu13 hus hu1
    have hup := Nat.prime_of_mem_primeFactors hu
    have huN := Nat.dvd_of_mem_primeFactors hu
    have heu := hsqB u hu hu5 hu13 hus
    refine ⟨heu, ?_, fun q hq hqd => ?_⟩
    · have hu2 : u ≠ 2 := by rintro rfl; exact h.not_two_dvd huN
      have hu7 : u ≠ 7 := by rintro rfl; exact hc.seven huN
      by_contra hlt'
      push Not at hlt'
      clear * - hup hu2 hu3 hu5 hu7 hlt'
      interval_cases u <;> first | omega | norm_num at hup
    · have hq2 : q ≠ 2 := by
        rintro rfl
        exact absurd (Nat.mod_eq_zero_of_dvd hqd) (by have := Nat.odd_iff.mp (phi3_odd u); omega)
      have hq3 : q ≠ 3 := by
        rintro rfl
        exact hu1 ((three_dvd_phi3_iff u).mp hqd)
      exact ⟨hc.sq u q hup huN hu5 hu13 hus hq hq2 hqd, prime_dvd_phi3_mod_three hq hq3 hqd⟩
  by_cases ht : ∃ t, t.Prime ∧ t ∣ N ∧ t % 3 = 1 ∧ t ≠ 13 ∧ t ≠ s
  · obtain ⟨t, ht, htN, ht3, ht13, hts⟩ := ht
    have ht7 : t ≠ 7 := by rintro rfl; exact hc.seven htN
    have ht5 : t ≠ 5 := by rintro rfl; norm_num at ht3
    have het := hsqB t (mem ht htN) ht5 ht13 hts
    have hsupp : ∀ q, q.Prime → q ∣ phi3 t → q = 3 ∨ q = 13 ∨ q = s := by
      intro q hq hqd
      by_contra hne
      push Not at hne
      have hq2 : q ≠ 2 := by
        rintro rfl
        exact absurd (Nat.mod_eq_zero_of_dvd hqd) (by have := Nat.odd_iff.mp (phi3_odd t); omega)
      have hqt : q ≠ t := by
        rintro rfl
        have := Nat.Coprime.eq_one_of_dvd (phi3_coprime_self q).symm hqd
        exact hq.one_lt.ne' this
      exact hc.two t q ht hq htN (hc.sq t q ht htN ht5 ht13 hts hq hq2 hqd) (Ne.symm hqt) ht3
        (prime_dvd_phi3_mod_three hq hne.1 hqd) ht13 hne.2.1 hts hne.2.2
    by_cases htlt : t < 30001
    · have h19 : 19 ≤ t := by
        by_contra h'
        push Not at h'
        clear * - ht ht3 ht7 ht13 h'
        interval_cases t <;> first | omega | norm_num at ht
      exact t_closed ht3 h19 htlt N s hc hs hlt hs5 ht htN hsupp
    push Not at htlt
    obtain ⟨g2, -, hg2, hg2s, hg2t⟩ := dummy_avoid s t
    refine tail_core h hs hlt ht hg2 (by omega) (Ne.symm hs13) hg2s hg2t (Ne.symm hts)
      {3, 5, 13, s, t} ?_ c ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with hp | hp | hp | hp | hp
      · exact mK4 p (Or.inl hp)
      · exact mK4 p (Or.inr (Or.inl hp))
      · exact mK4 p (Or.inr (Or.inr (Or.inl hp)))
      · exact mK4 p (Or.inr (Or.inr (Or.inr hp)))
      · exact hp ▸ mem ht htN
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with hp | hp | hp | hp | hp
      · exact hC4 p (Or.inl hp)
      · exact hC4 p (Or.inr (Or.inl hp))
      · exact hC4 p (Or.inr (Or.inr (Or.inl hp)))
      · exact hC4 p (Or.inr (Or.inr (Or.inr hp)))
      · have ct : c t = 1 + 1 / 30000 + 1 / 30000 ^ 2 := by
          have : t ≠ 3 := by omega
          simp [hcd, this, ht5, ht13, hts]
        rw [hp, ct, het]
        exact abundancy_sq_le ht (by omega)
    · have ct : c t = 1 + 1 / 30000 + 1 / 30000 ^ 2 := by
        have : t ≠ 3 := by omega
        simp [hcd, this, ht5, ht13, hts]
      rw [Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.prod_insert (by simp only [Finset.mem_singleton]; omega),
        Finset.prod_singleton, c3, c5, c13, cs, ct]
    · intro u hu
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hu
      push Not at hu
      obtain ⟨hum, hu3, hu5, hu13, hus, hut⟩ := hu
      have hup := Nat.prime_of_mem_primeFactors hum
      have huN := Nat.dvd_of_mem_primeFactors hum
      have hu1 : u % 3 ≠ 1 := fun h1 =>
        hc.two t u ht hup htN huN (Ne.symm hut) ht3 h1 ht13 hu13 hts hus
      obtain ⟨heu, hu10, hq⟩ := usq u hum hu3 hu5 hu13 hus hu1
      refine ⟨heu, hu10, fun q hqm => ?_⟩
      have hqp := Nat.prime_of_mem_primeFactors hqm
      obtain ⟨hqN, hq3⟩ := hq q hqp (Nat.dvd_of_mem_primeFactors hqm)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hne
      push Not at hne
      exact hc.two t q ht hqp htN hqN (Ne.symm hne.2.2) ht3 hq3 ht13 hne.1 hts hne.2.1
  · push Not at ht
    obtain ⟨g2, -, hg2, hg2s, -⟩ := dummy_avoid s s
    obtain ⟨g4, p4, hg4, hg4s, hg42⟩ := dummy_avoid s g2
    refine tail_core h hs hlt p4 hg2 (by omega) (Ne.symm hs13) hg2s (Ne.symm hg42)
      (Ne.symm hg4s) {3, 5, 13, s} ?_ c ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      exact mK4 p hp
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      exact hC4 p hp
    · rw [Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.prod_insert (by simp only [Finset.mem_singleton]; omega),
        Finset.prod_singleton, c3, c5, c13, cs]
      norm_num
    · intro u hu
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hu
      push Not at hu
      obtain ⟨hum, hu3, hu5, hu13, hus⟩ := hu
      have hup := Nat.prime_of_mem_primeFactors hum
      have huN := Nat.dvd_of_mem_primeFactors hum
      have hu1 : u % 3 ≠ 1 := fun h1 => hus (ht u hup huN h1 hu13)
      obtain ⟨heu, hu10, hq⟩ := usq u hum hu3 hu5 hu13 hus hu1
      refine ⟨heu, hu10, fun q hqm => ?_⟩
      have hqp := Nat.prime_of_mem_primeFactors hqm
      obtain ⟨hqN, hq3⟩ := hq q hqp (Nat.dvd_of_mem_primeFactors hqm)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hne
      push Not at hne
      exact hne.2.1 (ht q hqp hqN hq3 hne.1)

open TwoExceptionThreeB in
/-- An odd perfect number with special prime `5` in which every prime factor other than `5`,
`r₁` and `r₂` has exponent exactly 2 has `e₃ ≥ 6`. Whether this statement is new was not
verified. -/
theorem two_exceptions_five_six_le_three {N r₁ r₂ : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization 5))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ 5 → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2) :
    6 ≤ N.factorization 3 := by
  rcases two_exceptions_five_three_cases h hodd hsq with h2 | h6
  · exact absurd h2 (two_exceptions_five_three_ne_two h hodd hsq)
  · exact h6

end OddPerfect

#print axioms OddPerfect.TwoExceptionThreeB.prime_Q
#print axioms OddPerfect.TwoExceptionThreeB.prime_R
#print axioms OddPerfect.TwoExceptionThreeB.dummy_avoid
#print axioms OddPerfect.branch_b_ctx
#print axioms OddPerfect.two_exceptions_five_three_ne_two
#print axioms OddPerfect.two_exceptions_five_six_le_three
