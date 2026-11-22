import OddPerfect.ThreeFreeTwo
import OddPerfect.SpecialPrime
import OddPerfect.Phi3

/-!
# Two exceptional exponents with special prime 5: the exponent of 3 is not 4

Let `N` be an odd perfect number with special prime `5`, and suppose every prime factor of
`N` other than `5`, `r₁` and `r₂` has exponent exactly 2. Then `3 ∣ N`
(`three_dvd_of_two_exceptions`), and we show that the exponent of 3 is not 4. Whether this
statement is new was not verified.

Assume `e₃ = 4`. Then `σ(3^4) = 121 = 11^2`, so `11 ∣ N`. If `e₁₁ = 2`, then
`σ(11^2) = 133 = 7 · 19` gives `7 ∣ N`, against `105 ∤ N`. So `3` and `11` are the two
exceptions, and every other prime factor except `5` has exponent 2.

The prime `5` divides `2N = σ(N)`. It does not divide `σ(5^k)`, nor `σ(3^4) = 121`, nor
`σ(p^2) = p^2 + p + 1` (whose prime factors other than 3 are `1` modulo 3). Hence
`5 ∣ σ(11^e)` with `e = e₁₁`, and since `11 ≡ 1 (mod 5)` this means `5 ∣ e + 1`. Then
`σ(11^4) = 16105 = 5 · 3221` divides `σ(11^e)`, so the prime `3221` divides `N` with
exponent 2. The chain of exact squares continues:
`σ(3221^2) = 10378063` (a prime), `769 ∣ σ(10378063^2)`, `31 ∣ σ(769^2)`. Finally the
divisor `3^4 · 5 · 11^4 · 31^2` of `N` has abundancy `2132302/1046529 > 2`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace TwoExceptionThree

/-- A prime dividing `σ(p^2)` for an exact square `p^2` divides `N`. -/
private theorem force_sq {N p t : ℕ} (h : OddPerfect N) (hp : p.Prime)
    (he : N.factorization p = 2) (ht : t.Prime) (ht2 : t ≠ 2) (hd : t ∣ phi3 p) : t ∣ N :=
  OPNStarter.force_prime h.perfect hp he ht ht2 (by rwa [sigma_prime_sq hp])

/-- `1 + 11 + ⋯ + 11^(n-1) ≡ n (mod 5)`. -/
private theorem geom_eleven_mod_five (n : ℕ) :
    (∑ i ∈ Finset.range n, 11 ^ i) % 5 = n % 5 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, show 11 % 5 = 1 from rfl,
      one_pow]
    omega

/-- An abundant divisor excludes perfection. -/
private theorem not_of_abundant_dvd {N d : ℕ} (h : OddPerfect N) (hd : d ∣ N)
    (hσ : 2 * d < σ 1 d) : False := by
  rw [sigma_one_apply] at hσ
  have hab := (Nat.abundant_iff_sum_divisors.mpr hσ).of_dvd hd h.ne_zero
  exact ((Nat.perfect_iff_not_abundant_and_not_deficient h.pos.ne).mp h.perfect).1 hab

/-- The chain `11 → 3221 → 10378063 → 769 → 31` of exact squares. -/
private theorem chain_31 {N : ℕ} (h : OddPerfect N)
    (key : ∀ p, p.Prime → p ∣ N → p ≠ 3 → p ≠ 5 → p ≠ 11 → N.factorization p = 2)
    (h5 : 5 ∣ N.factorization 11 + 1) : N.factorization 31 = 2 := by
  have hP := h.perfect
  have p11 : Nat.Prime 11 := by norm_num
  have h3221 : 3221 ∣ N := by
    refine OPNStarter.force_prime hP p11 rfl (by norm_num) (by norm_num) ?_
    refine dvd_trans ?_ (OPNExample.sigma_prime_pow_dvd (a := 4) p11 h5)
    rw [sigma_one_apply_prime_pow p11]
    norm_num [Finset.sum_range_succ]
  have p3221 : Nat.Prime 3221 := by norm_num
  have e3221 := key 3221 p3221 h3221 (by norm_num) (by norm_num) (by norm_num)
  have pA : Nat.Prime 10378063 := by norm_num
  have hA : 10378063 ∣ N := force_sq h p3221 e3221 pA (by norm_num) (by norm_num [phi3])
  have eA := key 10378063 pA hA (by norm_num) (by norm_num) (by norm_num)
  have p769 : Nat.Prime 769 := by norm_num
  have h769 : 769 ∣ N := force_sq h pA eA p769 (by norm_num) (by norm_num [phi3])
  have e769 := key 769 p769 h769 (by norm_num) (by norm_num) (by norm_num)
  have p31 : Nat.Prime 31 := by norm_num
  have h31 : 31 ∣ N := force_sq h p769 e769 p31 (by norm_num) (by norm_num [phi3])
  exact key 31 p31 h31 (by norm_num) (by norm_num) (by norm_num)

/-- The divisor `3^4 · 5 · 11^4 · 31^2` is abundant. -/
private theorem abundant_end {N : ℕ} (h : OddPerfect N) (h34 : N.factorization 3 = 4)
    (h5 : 5 ∣ N) (h11 : 4 ≤ N.factorization 11) (e31 : N.factorization 31 = 2) : False := by
  have hN := h.ne_zero
  have p11 : Nat.Prime 11 := by norm_num
  have p31 : Nat.Prime 31 := by norm_num
  have d3 : 3 ^ 4 ∣ N := (Nat.prime_three.pow_dvd_iff_le_factorization hN).mpr (by omega)
  have d5 : 5 ^ 1 ∣ N := by simpa using h5
  have d11 : 11 ^ 4 ∣ N := (p11.pow_dvd_iff_le_factorization hN).mpr (by omega)
  have d31 : 31 ^ 2 ∣ N := (p31.pow_dvd_iff_le_factorization hN).mpr (by omega)
  have hd : 3 ^ 4 * 5 ^ 1 * 11 ^ 4 * 31 ^ 2 ∣ N :=
    (show Nat.Coprime (3 ^ 4 * 5 ^ 1 * 11 ^ 4) (31 ^ 2) by norm_num).mul_dvd_of_dvd_of_dvd
      ((show Nat.Coprime (3 ^ 4 * 5 ^ 1) (11 ^ 4) by norm_num).mul_dvd_of_dvd_of_dvd
        ((show Nat.Coprime (3 ^ 4) (5 ^ 1) by norm_num).mul_dvd_of_dvd_of_dvd d3 d5) d11) d31
  apply not_of_abundant_dvd h hd
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    sigma_one_apply_prime_pow Nat.prime_three, sigma_one_apply_prime_pow Nat.prime_five,
    sigma_one_apply_prime_pow p11, sigma_one_apply_prime_pow p31]
  norm_num [Finset.sum_range_succ]


end TwoExceptionThree

open TwoExceptionThree in
/-- Let `N` be an odd perfect number with special prime `5` in which every prime factor
other than `5`, `r₁` and `r₂` has exponent exactly 2. Then the exponent of 3 in `N` is not 4.
Whether this statement is new was not verified. -/
theorem two_exceptions_five_three_ne_four {N r₁ r₂ : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization 5))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ 5 → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2) :
    N.factorization 3 ≠ 4 := by
  intro h34
  have hN := h.ne_zero
  have hP := h.perfect
  have h3 : 3 ∣ N := three_dvd_of_two_exceptions h Nat.prime_five hodd hsq
  have h5 : 5 ∣ N := Nat.dvd_of_factorization_pos hodd.pos.ne'
  have mem : ∀ {p : ℕ}, p.Prime → p ∣ N → p ∈ N.primeFactors := fun hp hd =>
    Nat.mem_primeFactors.mpr ⟨hp, hd, hN⟩
  have p11 : Nat.Prime 11 := by norm_num
  have h11 : 11 ∣ N := OPNStarter.force_prime hP Nat.prime_three h34 p11 (by norm_num)
    (by rw [sigma_one_apply_prime_pow Nat.prime_three]; norm_num [Finset.sum_range_succ])
  have h11e : N.factorization 11 ≠ 2 := by
    intro he
    have h7 : 7 ∣ N := force_sq h p11 he (by norm_num) (by norm_num) (by decide)
    exact not_105_dvd h (by omega)
  have hr3 : 3 = r₁ ∨ 3 = r₂ := by
    by_contra hc
    push Not at hc
    have := hsq 3 (mem Nat.prime_three h3) (by norm_num) hc.1 hc.2
    omega
  have hr11 : 11 = r₁ ∨ 11 = r₂ := by
    by_contra hc
    push Not at hc
    exact h11e (hsq 11 (mem p11 h11) (by norm_num) hc.1 hc.2)
  have key : ∀ p, p.Prime → p ∣ N → p ≠ 3 → p ≠ 5 → p ≠ 11 → N.factorization p = 2 := by
    intro p hp hd h3' h5' h11'
    exact hsq p (mem hp hd) h5' (by omega) (by omega)
  -- the prime 5 is sent by the component of 11
  have h5σ : 5 ∣ σ 1 (11 ^ N.factorization 11) := by
    have hbal := OPNStarter.valuation_balance hP 5
    have h25 : Nat.factorization 2 5 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
    have hpos : N.factorization 5 ≠ 0 := hodd.pos.ne'
    rw [h25, zero_add] at hbal
    rw [hbal] at hpos
    obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    by_cases e11 : p = 11
    · subst e11
      exact Nat.dvd_of_factorization_pos hne
    exfalso
    apply hne
    apply Nat.factorization_eq_zero_of_not_dvd
    by_cases e5 : p = 5
    · subst e5
      exact Nat.prime_five.coprime_iff_not_dvd.mp
        (coprime_sigma_prime_pow Nat.prime_five _).symm
    by_cases e3 : p = 3
    · subst e3
      rw [h34, sigma_one_apply_prime_pow Nat.prime_three]
      norm_num [Finset.sum_range_succ]
    rw [key p hpp hpd e3 e5 e11, sigma_prime_sq hpp]
    intro hd
    have := prime_dvd_phi3_mod_three Nat.prime_five (by norm_num) hd
    omega
  have hmod : (N.factorization 11 + 1) % 5 = 0 := by
    rw [sigma_one_apply_prime_pow p11, Nat.dvd_iff_mod_eq_zero, geom_eleven_mod_five] at h5σ
    exact h5σ
  have hge : 1 ≤ N.factorization 11 := (p11.dvd_iff_one_le_factorization hN).mp h11
  exact abundant_end h h34 h5 (by omega)
    (chain_31 h key (by omega))

/-- The clean form: for an odd perfect number with special prime `5` and at most two
exceptional exponents `r₁`, `r₂` (every other prime factor has exponent exactly 2), the
exponent of 3 is `2` or at least `6`. Whether this statement is new was not verified. -/
theorem two_exceptions_five_three_cases {N r₁ r₂ : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization 5))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ 5 → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2) :
    N.factorization 3 = 2 ∨ 6 ≤ N.factorization 3 := by
  have h3 : 3 ∣ N := three_dvd_of_two_exceptions h Nat.prime_five hodd hsq
  have hpos := (Nat.prime_three.dvd_iff_one_le_factorization h.ne_zero).mp h3
  obtain ⟨k, hk⟩ := even_factorization_of_ne h Nat.prime_five hodd Nat.prime_three (by norm_num)
  have hne := two_exceptions_five_three_ne_four h hodd hsq
  omega


/-! ## The branch `e₃ = 2` with special prime 5

The remaining results concern `e₃ = 2`. The prime `5` sends a factor 3 (because `6 ∣ σ(5^k)`),
so by the 3 ledger at most one further component sum is divisible by 3. The prime `5` itself
is sent by an exceptional prime `s ≡ 1 (mod 5)` with `5 ∣ e_s + 1`. These partial results
force the shape of every surviving configuration (`two_exceptions_five_three_sq_shape`). -/

namespace TwoExceptionThree

/-- Twenty consecutive terms of a geometric series with ratio `1 ≤ c ≤ 4` sum to a
multiple of 5. -/
private theorem geom_shift (c r : ℕ) (hc0 : 0 < c) (hc : c < 5) (q : ℕ) :
    (∑ i ∈ Finset.range (r + 20 * q), c ^ i) % 5 = (∑ i ∈ Finset.range r, c ^ i) % 5 := by
  have h20 : 5 ∣ ∑ i ∈ Finset.range 20, c ^ i := by interval_cases c <;> decide
  obtain ⟨k, hk⟩ := h20
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show r + 20 * (q + 1) = (r + 20 * q) + 20 by ring, Finset.sum_range_add]
    have hsplit : ∑ x ∈ Finset.range 20, c ^ (r + 20 * q + x) =
        5 * (c ^ (r + 20 * q) * k) := by
      rw [show 5 * (c ^ (r + 20 * q) * k) = c ^ (r + 20 * q) * (5 * k) by ring, ← hk,
        Finset.mul_sum]
      simp only [pow_add]
    rw [hsplit, Nat.add_mul_mod_self_left, ih]

/-- Reduction of the length of a geometric series modulo 20. -/
private theorem geom_mod_red (c n : ℕ) (hc0 : 0 < c) (hc : c < 5) :
    (∑ i ∈ Finset.range n, c ^ i) % 5 = (∑ i ∈ Finset.range (n % 20), c ^ i) % 5 := by
  conv_lhs => rw [← Nat.mod_add_div n 20]
  exact geom_shift c (n % 20) hc0 hc (n / 20)

/-- The finite table behind `five_sender_mod`. -/
private theorem geom_five_table : ∀ c < 5, ∀ m < 20, 0 < c → m % 2 = 1 →
    (∑ i ∈ Finset.range m, c ^ i) % 5 = 0 → c = 1 ∧ m % 5 = 0 := by
  intro c hc m hm h0 hodd hs
  interval_cases c <;> interval_cases m <;> simp_all [Finset.sum_range_succ]

/-- If `5 ∣ σ(p^e)` with `p ≠ 5` prime and `e` even, then `p ≡ 1 (mod 5)` and `5 ∣ e + 1`. -/
theorem five_sender_mod {p e : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) (he : Even e)
    (hd : 5 ∣ σ 1 (p ^ e)) : p % 5 = 1 ∧ 5 ∣ e + 1 := by
  rw [sigma_one_apply_prime_pow hp, Nat.dvd_iff_mod_eq_zero] at hd
  have hc0 : 0 < p % 5 := by
    rcases Nat.eq_zero_or_pos (p % 5) with h0 | h0
    · exfalso
      exact hp5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp
        (Nat.dvd_of_mod_eq_zero h0)).symm
    · exact h0
  have hc5 : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hred : (∑ i ∈ Finset.range (e + 1), p ^ i) % 5 =
      (∑ i ∈ Finset.range (e + 1), (p % 5) ^ i) % 5 := by
    rw [Finset.sum_nat_mod, Finset.sum_nat_mod (f := fun i => (p % 5) ^ i)]
    congr 1
    exact Finset.sum_congr rfl fun i _ => Nat.pow_mod p i 5
  rw [hred, geom_mod_red _ _ hc0 hc5] at hd
  obtain ⟨k, hk⟩ := he
  have := geom_five_table (p % 5) hc5 ((e + 1) % 20) (Nat.mod_lt _ (by norm_num)) hc0
    (by omega) hd
  exact ⟨this.1, by omega⟩

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

/-- An exact square `p^2` with `p ≡ 1 (mod 3)` sends a factor 3. -/
private theorem sq_sends_three {N p : ℕ} (hp : p.Prime) (he : N.factorization p = 2)
    (h3 : p % 3 = 1) : 3 ∣ σ 1 (p ^ N.factorization p) := by
  rw [he, sigma_prime_sq hp]
  exact (three_dvd_phi3_iff p).mpr h3

/-- With special prime 5, some prime factor `p ≠ 5` with exponent other than 2 has
`5 ∣ σ(p^{e_p})`. -/
private theorem five_sender_exists {N : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization 5)) :
    ∃ p ∈ N.primeFactors, p ≠ 5 ∧ N.factorization p ≠ 2 ∧
      5 ∣ σ 1 (p ^ N.factorization p) := by
  have hbal := OPNStarter.valuation_balance h.perfect 5
  have h25 : Nat.factorization 2 5 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  have hpos : N.factorization 5 ≠ 0 := hodd.pos.ne'
  rw [h25, zero_add] at hbal
  rw [hbal] at hpos
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos
  have hpp := Nat.prime_of_mem_primeFactors hp
  have h5 : 5 ∣ σ 1 (p ^ N.factorization p) := Nat.dvd_of_factorization_pos hne
  refine ⟨p, hp, ?_, ?_, h5⟩
  · rintro rfl
    exact Nat.prime_five.coprime_iff_not_dvd.mp
      (coprime_sigma_prime_pow Nat.prime_five _).symm h5
  · intro he
    rw [he, sigma_prime_sq hpp] at h5
    have := prime_dvd_phi3_mod_three Nat.prime_five (by norm_num) h5
    omega

/-- With `61` among `r₁, r₂`, at most one of the primes `13, 131, 17293, 21491, 421` is
among them, so two of the three chains `13`, `131 → 17293`, `21491 → 421` are uncut. -/
private theorem chains_cut {r₁ r₂ : ℕ} (hr61 : 61 = r₁ ∨ 61 = r₂) :
    ((13 ≠ r₁ ∧ 13 ≠ r₂) ∧ (131 ≠ r₁ ∧ 131 ≠ r₂ ∧ 17293 ≠ r₁ ∧ 17293 ≠ r₂)) ∨
    ((13 ≠ r₁ ∧ 13 ≠ r₂) ∧ (21491 ≠ r₁ ∧ 21491 ≠ r₂ ∧ 421 ≠ r₁ ∧ 421 ≠ r₂)) ∨
    ((131 ≠ r₁ ∧ 131 ≠ r₂ ∧ 17293 ≠ r₁ ∧ 17293 ≠ r₂) ∧
      (21491 ≠ r₁ ∧ 21491 ≠ r₂ ∧ 421 ≠ r₁ ∧ 421 ≠ r₂)) := by
  omega

end TwoExceptionThree

open TwoExceptionThree in
/-- Let `N` be an odd perfect number with special prime `5` in which every prime factor
other than `5`, `r₁` and `r₂` has exponent exactly 2, and suppose `e₃ = 2`. Then the
component of 61 does not send the prime 5: `5 ∤ σ(61^{e₆₁})`. Whether this statement is new
was not verified.

If `5 ∣ σ(61^e)` then `5 ∣ e + 1`, so `σ(61^4) = 5 · 131 · 21491` divides `2N`, and 61 is
exceptional. The prime 13 (from `σ(3^2)`), `17293 = σ(131^2)` and `421 ∣ σ(21491^2)` are
`1 (mod 3)`; at most one of the chains `13`, `131 → 17293`, `21491 → 421` can be cut by the
second exception, so two of these exact squares send a factor 3, and with `5` this gives
three senders against `e₃ = 2`. -/
theorem two_exceptions_five_three_sq_sixty_one {N r₁ r₂ : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization 5))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ 5 → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2)
    (h32 : N.factorization 3 = 2) :
    ¬ 5 ∣ σ 1 (61 ^ N.factorization 61) := by
  intro h5σ
  have hN := h.ne_zero
  have hP := h.perfect
  have mem : ∀ {p : ℕ}, p.Prime → p ∣ N → p ∈ N.primeFactors := fun hp hd =>
    Nat.mem_primeFactors.mpr ⟨hp, hd, hN⟩
  have key : ∀ p, p.Prime → p ∣ N → p ≠ 5 → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2 :=
    fun p hp hd h5 h1 h2 => hsq p (mem hp hd) h5 h1 h2
  have p61 : Nat.Prime 61 := by norm_num
  have h61 : 61 ∣ N := by
    by_contra hn
    rw [Nat.factorization_eq_zero_of_not_dvd hn, pow_zero, isMultiplicative_sigma.map_one]
      at h5σ
    norm_num at h5σ
  have he61 : Even (N.factorization 61) :=
    even_factorization_of_ne h Nat.prime_five hodd p61 (by norm_num)
  have hmod := (five_sender_mod p61 (by norm_num) he61 h5σ).2
  have hr61 : 61 = r₁ ∨ 61 = r₂ := by
    by_contra hc
    push Not at hc
    have := key 61 p61 h61 (by norm_num) hc.1 hc.2
    omega
  have hΦ : σ 1 (61 ^ 4) ∣ σ 1 (61 ^ N.factorization 61) :=
    OPNExample.sigma_prime_pow_dvd p61 hmod
  have hσ4 : σ 1 (61 ^ 4) = 5 * 131 * 21491 := by
    rw [sigma_one_apply_prime_pow p61]
    norm_num [Finset.sum_range_succ]
  have p131 : Nat.Prime 131 := by norm_num
  have p21491 : Nat.Prime 21491 := by norm_num
  have p17293 : Nat.Prime 17293 := by norm_num
  have p421 : Nat.Prime 421 := by norm_num
  have p13 : Nat.Prime 13 := by norm_num
  have h131 : 131 ∣ N := OPNStarter.force_prime hP p61 rfl p131 (by norm_num)
    (dvd_trans (by rw [hσ4]; norm_num) hΦ)
  have h21491 : 21491 ∣ N := OPNStarter.force_prime hP p61 rfl p21491 (by norm_num)
    (dvd_trans (by rw [hσ4]; norm_num) hΦ)
  have h13 : 13 ∣ N := OPNStarter.thirteen_dvd_of_three_sq hP h32
  have s5 := five_sends_three hodd
  have m5 : 5 ∈ N.primeFactors := mem Nat.prime_five (Nat.dvd_of_factorization_pos hodd.pos.ne')
  -- the chain through 131
  have chainA : 131 ≠ r₁ → 131 ≠ r₂ → 17293 ∣ N := fun a b =>
    force_sq h p131 (key 131 p131 h131 (by norm_num) a b) p17293 (by norm_num)
      (by norm_num [phi3])
  -- the chain through 21491
  have chainB : 21491 ≠ r₁ → 21491 ≠ r₂ → 421 ∣ N := fun a b =>
    force_sq h p21491 (key 21491 p21491 h21491 (by norm_num) a b) p421 (by norm_num)
      (by norm_num [phi3])
  have send : ∀ p, p.Prime → p ∣ N → p ≠ 5 → p % 3 = 1 → p ≠ r₁ → p ≠ r₂ →
      3 ∣ σ 1 (p ^ N.factorization p) := fun p hp hd h5 h3 a b =>
    sq_sends_three hp (key p hp hd h5 a b) h3
  rcases chains_cut hr61 with ⟨⟨a1, a2⟩, b1, b2, b3, b4⟩ | ⟨⟨a1, a2⟩, b1, b2, b3, b4⟩ |
      ⟨⟨a1, a2, a3, a4⟩, b1, b2, b3, b4⟩
  · have h17 := chainA b1 b2
    exact three_senders h h32 m5 (mem p13 h13) (mem p17293 h17) (by norm_num) (by norm_num)
      (by norm_num) s5 (send _ p13 h13 (by norm_num) (by norm_num) a1 a2)
      (send _ p17293 h17 (by norm_num) (by norm_num) b3 b4)
  · have h421 := chainB b1 b2
    exact three_senders h h32 m5 (mem p13 h13) (mem p421 h421) (by norm_num) (by norm_num)
      (by norm_num) s5 (send _ p13 h13 (by norm_num) (by norm_num) a1 a2)
      (send _ p421 h421 (by norm_num) (by norm_num) b3 b4)
  · have h17 := chainA a1 a2
    have h421 := chainB b1 b2
    exact three_senders h h32 m5 (mem p17293 h17) (mem p421 h421) (by norm_num)
      (by norm_num) (by norm_num) s5 (send _ p17293 h17 (by norm_num) (by norm_num) a3 a4)
      (send _ p421 h421 (by norm_num) (by norm_num) b3 b4)

open TwoExceptionThree in
/-- With special prime `5`, at most two exceptional exponents and `e₃ = 2`: if `e₁₃ = 2`,
then `61` is exceptional with `e₆₁ ≥ 6`, `3 ∤ e₆₁ + 1` and `5 ∤ e₆₁ + 1`. Whether this
statement is new was not verified. -/
theorem two_exceptions_five_three_sq_thirteen_sq {N r₁ r₂ : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization 5))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ 5 → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2)
    (h32 : N.factorization 3 = 2) (h132 : N.factorization 13 = 2) :
    6 ≤ N.factorization 61 ∧ ¬ 3 ∣ N.factorization 61 + 1 ∧ ¬ 5 ∣ N.factorization 61 + 1 := by
  have hN := h.ne_zero
  have hP := h.perfect
  have mem : ∀ {p : ℕ}, p.Prime → p ∣ N → p ∈ N.primeFactors := fun hp hd =>
    Nat.mem_primeFactors.mpr ⟨hp, hd, hN⟩
  have p13 : Nat.Prime 13 := by norm_num
  have p61 : Nat.Prime 61 := by norm_num
  have h13 : 13 ∣ N := OPNStarter.thirteen_dvd_of_three_sq hP h32
  have h61 : 61 ∣ N := force_sq h p13 h132 p61 (by norm_num) (by norm_num [phi3])
  have m5 : 5 ∈ N.primeFactors := mem Nat.prime_five (Nat.dvd_of_factorization_pos hodd.pos.ne')
  have s5 := five_sends_three hodd
  have s13 := sq_sends_three p13 h132 (by norm_num)
  have n3 : ¬ 3 ∣ N.factorization 61 + 1 := by
    intro h3
    have s61 : 3 ∣ σ 1 (61 ^ N.factorization 61) := by
      refine dvd_trans ?_ (OPNExample.sigma_prime_pow_dvd (a := 2) p61 h3)
      rw [sigma_one_apply_prime_pow p61]
      norm_num [Finset.sum_range_succ]
    exact three_senders h h32 m5 (mem p13 h13) (mem p61 h61) (by norm_num) (by norm_num)
      (by norm_num) s5 s13 s61
  have n5 : ¬ 5 ∣ N.factorization 61 + 1 := by
    intro h5
    apply two_exceptions_five_three_sq_sixty_one h hodd hsq h32
    refine dvd_trans ?_ (OPNExample.sigma_prime_pow_dvd (a := 4) p61 h5)
    rw [sigma_one_apply_prime_pow p61]
    norm_num [Finset.sum_range_succ]
  have hpos := (p61.dvd_iff_one_le_factorization hN).mp h61
  obtain ⟨k, hk⟩ := even_factorization_of_ne h Nat.prime_five hodd p61 (by norm_num)
  refine ⟨?_, n3, n5⟩
  by_contra hlt
  have h24 : N.factorization 61 = 2 ∨ N.factorization 61 = 4 := by
    clear * - hk hpos hlt
    omega
  rcases h24 with h2 | h4
  · exact n3 (by rw [h2])
  · exact n5 (by rw [h4])

open TwoExceptionThree in
/-- With special prime `5`, at most two exceptional exponents and `e₃ = 2`: either
`e₁₃ = 2` or `3 ∤ e₁₃ + 1`. Whether this statement is new was not verified. -/
theorem two_exceptions_five_three_sq_thirteen {N r₁ r₂ : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization 5))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ 5 → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2)
    (h32 : N.factorization 3 = 2) :
    N.factorization 13 = 2 ∨ ¬ 3 ∣ N.factorization 13 + 1 := by
  by_contra hc
  push Not at hc
  obtain ⟨hne, h3⟩ := hc
  have hN := h.ne_zero
  have hP := h.perfect
  have mem : ∀ {p : ℕ}, p.Prime → p ∣ N → p ∈ N.primeFactors := fun hp hd =>
    Nat.mem_primeFactors.mpr ⟨hp, hd, hN⟩
  have key : ∀ p, p.Prime → p ∣ N → p ≠ 5 → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2 :=
    fun p hp hd h5 h1 h2 => hsq p (mem hp hd) h5 h1 h2
  have p13 : Nat.Prime 13 := by norm_num
  have p61 : Nat.Prime 61 := by norm_num
  have h13 : 13 ∣ N := OPNStarter.thirteen_dvd_of_three_sq hP h32
  have hΦ : σ 1 (13 ^ 2) ∣ σ 1 (13 ^ N.factorization 13) :=
    OPNExample.sigma_prime_pow_dvd p13 h3
  have hσ2 : σ 1 (13 ^ 2) = 3 * 61 := by
    rw [sigma_one_apply_prime_pow p13]
    norm_num [Finset.sum_range_succ]
  have s13 : 3 ∣ σ 1 (13 ^ N.factorization 13) := dvd_trans (by rw [hσ2]; norm_num) hΦ
  have h61 : 61 ∣ N := OPNStarter.force_prime hP p13 rfl p61 (by norm_num)
    (dvd_trans (by rw [hσ2]; norm_num) hΦ)
  have m5 : 5 ∈ N.primeFactors := mem Nat.prime_five (Nat.dvd_of_factorization_pos hodd.pos.ne')
  have s5 := five_sends_three hodd
  have hr13 : 13 = r₁ ∨ 13 = r₂ := by
    by_contra hc
    push Not at hc
    exact hne (key 13 p13 h13 (by norm_num) hc.1 hc.2)
  have hr61 : 61 = r₁ ∨ 61 = r₂ := by
    by_contra hc
    push Not at hc
    exact three_senders h h32 m5 (mem p13 h13) (mem p61 h61) (by norm_num) (by norm_num)
      (by norm_num) s5 s13 (sq_sends_three p61 (key 61 p61 h61 (by norm_num) hc.1 hc.2)
        (by norm_num))
  obtain ⟨p, hp, hp5, hp2, h5p⟩ := five_sender_exists h hodd
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpr : p = r₁ ∨ p = r₂ := by
    by_contra hc
    push Not at hc
    exact hp2 (hsq p hp hp5 hc.1 hc.2)
  have hev := even_factorization_of_ne h Nat.prime_five hodd hpp hp5
  have hp1 := (five_sender_mod hpp hp5 hev h5p).1
  have hp61 : p = 61 := by omega
  subst hp61
  exact two_exceptions_five_three_sq_sixty_one h hodd hsq h32 h5p

open TwoExceptionThree in
/-- The shape of every configuration that survives for `e₃ = 2`: with special prime `5` and at
most two exceptional exponents, `e₃ = 2` forces a prime `s ≠ 61`, `s ≡ 1 (mod 5)`, dividing
`N` with `5 ∣ e_s + 1`, and either `e₁₃ = 2` and every prime factor other than `5`, `61`, `s`
has exponent 2, or `e₁₃ ≠ 2`, `3 ∤ e₁₃ + 1` and every prime factor other than `5`, `13`, `s`
has exponent 2. Whether this statement is new was not verified. -/
theorem two_exceptions_five_three_sq_shape {N r₁ r₂ : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization 5))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ 5 → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2)
    (h32 : N.factorization 3 = 2) :
    ∃ s, s.Prime ∧ s ∣ N ∧ s % 5 = 1 ∧ 5 ∣ N.factorization s + 1 ∧ s ≠ 61 ∧
      ((N.factorization 13 = 2 ∧
          ∀ p ∈ N.primeFactors, p ≠ 5 → p ≠ 61 → p ≠ s → N.factorization p = 2) ∨
        (N.factorization 13 ≠ 2 ∧ ¬ 3 ∣ N.factorization 13 + 1 ∧
          ∀ p ∈ N.primeFactors, p ≠ 5 → p ≠ 13 → p ≠ s → N.factorization p = 2)) := by
  have hN := h.ne_zero
  obtain ⟨s, hs, hs5, hs2, h5s⟩ := five_sender_exists h hodd
  have hsp := Nat.prime_of_mem_primeFactors hs
  have hsd := Nat.dvd_of_mem_primeFactors hs
  have hsr : s = r₁ ∨ s = r₂ := by
    by_contra hc
    push Not at hc
    exact hs2 (hsq s hs hs5 hc.1 hc.2)
  have hev := even_factorization_of_ne h Nat.prime_five hodd hsp hs5
  obtain ⟨hs1, hse⟩ := five_sender_mod hsp hs5 hev h5s
  have hs61 : s ≠ 61 := by
    rintro rfl
    exact two_exceptions_five_three_sq_sixty_one h hodd hsq h32 h5s
  refine ⟨s, hsp, hsd, hs1, hse, hs61, ?_⟩
  have p13 : Nat.Prime 13 := by norm_num
  have p61 : Nat.Prime 61 := by norm_num
  have h13 : 13 ∣ N := OPNStarter.thirteen_dvd_of_three_sq h.perfect h32
  by_cases h132 : N.factorization 13 = 2
  · left
    refine ⟨h132, fun p hp hp5 hp61 hps => hsq p hp hp5 ?_ ?_⟩
    · have h6 := (two_exceptions_five_three_sq_thirteen_sq h hodd hsq h32 h132).1
      have hr61 : 61 = r₁ ∨ 61 = r₂ := by
        by_contra hc
        push Not at hc
        have := hsq 61 (Nat.mem_primeFactors.mpr ⟨p61, (p61.dvd_iff_one_le_factorization hN).mpr
          (by omega), hN⟩) (by norm_num) hc.1 hc.2
        omega
      omega
    · have h6 := (two_exceptions_five_three_sq_thirteen_sq h hodd hsq h32 h132).1
      have hr61 : 61 = r₁ ∨ 61 = r₂ := by
        by_contra hc
        push Not at hc
        have := hsq 61 (Nat.mem_primeFactors.mpr ⟨p61, (p61.dvd_iff_one_le_factorization hN).mpr
          (by omega), hN⟩) (by norm_num) hc.1 hc.2
        omega
      omega
  · right
    have h3 := (two_exceptions_five_three_sq_thirteen h hodd hsq h32).resolve_left h132
    have hr13 : 13 = r₁ ∨ 13 = r₂ := by
      by_contra hc
      push Not at hc
      exact h132 (hsq 13 (Nat.mem_primeFactors.mpr ⟨p13, h13, hN⟩) (by norm_num) hc.1 hc.2)
    have hs13 : s ≠ 13 := by rintro rfl; omega
    exact ⟨h132, h3, fun p hp hp5 hp13 hps => hsq p hp hp5 (by omega) (by omega)⟩

end OddPerfect

#print axioms OddPerfect.two_exceptions_five_three_ne_four
#print axioms OddPerfect.two_exceptions_five_three_cases
#print axioms OddPerfect.TwoExceptionThree.five_sender_mod
#print axioms OddPerfect.two_exceptions_five_three_sq_sixty_one
#print axioms OddPerfect.two_exceptions_five_three_sq_thirteen_sq
#print axioms OddPerfect.two_exceptions_five_three_sq_thirteen
#print axioms OddPerfect.two_exceptions_five_three_sq_shape
