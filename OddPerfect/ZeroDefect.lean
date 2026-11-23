import OddPerfect.ExcessDefect

/-!
# The support defect is positive, and `ω(N) + 2 * v_3(σ(q ^ a)) ≤ 5 * T + 6`

Let `N` be an odd perfect number with special prime `q` of exponent `a`, and `T` the total
excess. The defect identity `ω(N) + 2 * s + supportDefect N q = 5 * T + 5 + H`
(`card_primeFactors_add_two_mul_add_defect_eq`, with `s = v_3(σ(q ^ a))` and `H ≤ 2` the
number of escape rows) shows that the bound `+ 7` is reached only with zero defect. Zero defect
means: `3 ∣ N` with `v_3(N) ∈ {2, 4}`, every ordinary exponent is 2 or 4, every ordinary prime
that is 2 modulo 3 has exponent 2, every square prime sends at most one unit to the ordinary
receivers and the special prime and the primes of exponent 4 send none (`zero_defect_facts`).

For `q ≡ 1 (mod 3)` a short chain of component divisor sums rules this out
(`one_le_supportDefect`): `v_3(N) = 4` puts 11 in `N` with exponent 2 and
`σ(11 ^ 2) = 7 * 19` sends two units; `v_3(N) = 2` forces the primes 13, 61, 5, 31, 331 and
ends at `σ(331 ^ 4) = 5 * 37861 * 63601` or at a third square prime that is 1 modulo 3. Whether
the literature already excludes the zero defect profile was not checked; the short chain here
is self contained.

Hence `ω(N) + 2 * s ≤ 5 * T + 6` for every special prime with no classical input
(`card_primeFactors_add_two_mul_le_five_excess_add_six`), `ω(N) ≤ 5 * T + 6` and
`N < 2 ^ 4 ^ (5 * T + 6)`; and `ω(N) ≤ 5 * T + 2` when `3 ∤ N`. Whether the bound `+ 6` is new
has not been verified. The total excess is not bounded, and the odd perfect number conjecture
remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

private theorem three_ne_special₃ {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) : (3 : ℕ) ≠ q := by
  rintro rfl
  have := (special_mod_four h hq hodd).1
  omega

private theorem special_mem₃ {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) : q ∈ N.primeFactors := by
  have : N.factorization q ≠ 0 := by obtain ⟨k, hk⟩ := hodd; omega
  exact Nat.mem_primeFactors.mpr ⟨hq, Nat.dvd_of_factorization_pos this, h.ne_zero⟩

private theorem sigma_pow_four {p : ℕ} (hp : p.Prime) :
    σ 1 (p ^ 4) = 1 + p + p ^ 2 + p ^ 3 + p ^ 4 := by
  rw [sigma_one_apply_prime_pow hp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
  ring

/-- An odd prime dividing a component divisor sum is a prime factor and receives weight. -/
private theorem mem_of_dvd_sigma {N p t : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors)
    (ht : t.Prime) (ht2 : t ≠ 2) (hd : t ∣ σ 1 (p ^ N.factorization p)) :
    t ∈ N.primeFactors ∧ 1 ≤ sigmaWeight N p t := by
  have h0 : σ 1 (p ^ N.factorization p) ≠ 0 :=
    (sigma_pos 1 _ (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)).ne'
  have hw : 1 ≤ sigmaWeight N p t := ht.factorization_pos_of_dvd h0 hd
  exact ⟨mem_primeFactors_of_sigmaWeight_ne_zero h.perfect hp ht2 (by omega), hw⟩

/-- A receiver dividing a component divisor sum. -/
private theorem recv_of_dvd_sigma {N q p t : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors)
    (ht : t.Prime) (hd : t ∣ σ 1 (p ^ N.factorization p)) (ht3 : t ≠ 3) (htq : t ≠ q)
    (ht1 : t % 3 = 1) : t ∈ ordReceivers N q ∧ 1 ≤ sigmaWeight N p t := by
  obtain ⟨htN, hw⟩ := mem_of_dvd_sigma h hp ht (by omega) hd
  exact ⟨Finset.mem_filter.mpr ⟨htN, htq, ht3, ht1⟩, hw⟩

private theorem one_le_recvWeight_of {N q p t : ℕ} (ht : t ∈ ordReceivers N q)
    (hw : 1 ≤ sigmaWeight N p t) : 1 ≤ recvWeight N q p :=
  hw.trans (Finset.single_le_sum (f := fun r => sigmaWeight N p r)
    (fun _ _ => Nat.zero_le _) ht)

private theorem two_le_recvWeight_of {N q p t u : ℕ} (ht : t ∈ ordReceivers N q)
    (hu : u ∈ ordReceivers N q) (htu : t ≠ u) (hwt : 1 ≤ sigmaWeight N p t)
    (hwu : 1 ≤ sigmaWeight N p u) : 2 ≤ recvWeight N q p := by
  have hsub : ({t, u} : Finset ℕ) ⊆ ordReceivers N q := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ht
    · exact hu
  have := Finset.sum_le_sum_of_subset (f := fun r => sigmaWeight N p r) hsub
  rw [Finset.sum_pair htu] at this
  unfold recvWeight
  omega

/-- The pointwise content of zero defect. -/
theorem zero_defect_facts {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hZ : supportDefect N q = 0) :
    3 ∣ N ∧ (N.factorization 3 = 2 ∨ N.factorization 3 = 4) ∧
      (∀ p ∈ N.primeFactors, p ≠ q → p % 3 = 2 → N.factorization p = 2) ∧
      (∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 2 ∨ N.factorization p = 4) ∧
      (∀ p ∈ squarePrimes N q \ escapeRows N q, recvWeight N q p ≤ 1) ∧
      (∀ p ∈ insert q (highPrimes N q), recvWeight N q p = 0) := by
  have h3q := three_ne_special₃ h hq hodd
  unfold supportDefect at hZ
  by_cases h3 : 3 ∣ N
  swap
  · rw [if_neg h3] at hZ
    omega
  rw [if_pos h3] at hZ
  have hW : twoModThreeMass N q = 0 := by omega
  have hD : highExcessDefect N q = 0 := by omega
  have hd3 : threeExcessDefect N = 0 := by omega
  have hmu : squareSurplus N q = 0 := by omega
  have hL : highRecvWeight N q = 0 := by omega
  have hb : N.factorization 3 = 2 ∨ N.factorization 3 = 4 := by
    obtain ⟨j, hj, hpos⟩ := even_pos_factorization_of_ne h hq hodd
      (Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, h.ne_zero⟩) h3q
    unfold threeExcessDefect at hd3
    omega
  refine ⟨h3, hb, ?_, ?_, ?_, ?_⟩
  · intro p hp hpq hp2
    obtain ⟨j, hj, hpos⟩ := even_pos_factorization_of_ne h hq hodd hp hpq
    by_contra hne
    have hmem : p ∈ (highPrimes N q).filter (fun p => p % 3 = 2) := by
      simp only [highPrimes, Finset.mem_filter, Finset.mem_erase]
      exact ⟨⟨⟨hpq, hp⟩, by omega⟩, hp2⟩
    have := (Finset.sum_eq_zero_iff.mp hW) p hmem
    omega
  · intro p hp hpq
    obtain ⟨j, hj, hpos⟩ := even_pos_factorization_of_ne h hq hodd hp hpq
    by_cases hp3 : p = 3
    · subst hp3
      exact hb
    by_contra hne
    have hmem : p ∈ (highPrimes N q).filter (fun p => p ≠ 3) := by
      simp only [highPrimes, Finset.mem_filter, Finset.mem_erase]
      exact ⟨⟨⟨hpq, hp⟩, by omega⟩, hp3⟩
    have := (Finset.sum_eq_zero_iff.mp hD) p hmem
    omega
  · intro p hp
    have := (Finset.sum_eq_zero_iff.mp hmu) p hp
    omega
  · exact Finset.sum_eq_zero_iff.mp hL

/-- Under zero defect, a square prime has no two distinct prime factors of `phi3 p` outside
`{3, q}`. -/
private theorem sq_two_absurd {N q p t u : ℕ} (h : OddPerfect N)
    (hmu : ∀ p ∈ squarePrimes N q \ escapeRows N q, recvWeight N q p ≤ 1)
    (hp : p ∈ N.primeFactors) (hpq : p ≠ q) (he : N.factorization p = 2) (ht : t.Prime)
    (hu : u.Prime) (htu : t ≠ u) (htd : t ∣ phi3 p) (hud : u ∣ phi3 p) (ht3 : t ≠ 3)
    (hu3 : u ≠ 3) (htq : t ≠ q) (huq : u ≠ q) : False := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hσ : σ 1 (p ^ N.factorization p) = phi3 p := by rw [he, sigma_prime_sq hpp]
  obtain ⟨htR, hwt⟩ := recv_of_dvd_sigma (q := q) h hp ht (hσ ▸ htd) ht3 htq
    (prime_dvd_phi3_mod_three ht ht3 htd)
  obtain ⟨huR, hwu⟩ := recv_of_dvd_sigma (q := q) h hp hu (hσ ▸ hud) hu3 huq
    (prime_dvd_phi3_mod_three hu hu3 hud)
  have hpS : p ∈ squarePrimes N q := Finset.mem_filter.mpr ⟨hp, hpq, he⟩
  have hpE : p ∉ escapeRows N q := by
    intro hpE
    rcases (mem_escapeRows.mp hpE).2 t ht htd with e | e
    · exact ht3 e
    · exact htq e
  have := hmu p (Finset.mem_sdiff.mpr ⟨hpS, hpE⟩)
  have := two_le_recvWeight_of htR huR htu hwt hwu
  omega

/-- Under zero defect, the special prime and the primes of exponent at least 4 reach no
receiver. -/
private theorem high_absurd {N q p t : ℕ} (h : OddPerfect N)
    (hL : ∀ p ∈ insert q (highPrimes N q), recvWeight N q p = 0)
    (hpX : p ∈ insert q (highPrimes N q)) (hp : p ∈ N.primeFactors) (ht : t.Prime)
    (hd : t ∣ σ 1 (p ^ N.factorization p)) (ht3 : t ≠ 3) (htq : t ≠ q) (ht1 : t % 3 = 1) :
    False := by
  obtain ⟨htR, hw⟩ := recv_of_dvd_sigma h hp ht hd ht3 htq ht1
  have := one_le_recvWeight_of htR hw
  have := hL p hpX
  omega

private theorem mem_high {N q p : ℕ} (hp : p ∈ N.primeFactors) (hpq : p ≠ q)
    (he : N.factorization p = 4) : p ∈ insert q (highPrimes N q) :=
  Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hpq, hp⟩, by omega⟩)

/-- Under zero defect, 11 does not divide `N`. -/
private theorem eleven_absurd {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hZ : supportDefect N q = 0)
    (h11 : 11 ∈ N.primeFactors) : False := by
  obtain ⟨-, -, hW, -, hmu, -⟩ := zero_defect_facts h hq hodd hZ
  have hq4 := (special_mod_four h hq hodd).1
  have hq11 : (11 : ℕ) ≠ q := by omega
  have e11 := hW 11 h11 hq11 (by norm_num)
  exact sq_two_absurd (t := 7) (u := 19) h hmu h11 hq11 e11 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [phi3]) (by norm_num [phi3]) (by norm_num) (by norm_num)
    (by omega) (by omega)

/-- Under zero defect, `v_3(N) ≠ 4`, for every special prime: `σ(3 ^ 4) = 11 ^ 2` and
`σ(11 ^ 2) = 7 * 19`. -/
theorem factorization_three_ne_four_of_supportDefect_eq_zero {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hZ : supportDefect N q = 0) :
    N.factorization 3 ≠ 4 := by
  intro hb
  obtain ⟨h3, -⟩ := zero_defect_facts h hq hodd hZ
  have h3P : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, h.ne_zero⟩
  exact eleven_absurd h hq hodd hZ (mem_of_dvd_sigma h h3P (by norm_num) (by norm_num)
    (by rw [hb, sigma_pow_four Nat.prime_three]; norm_num)).1

/-- For a special prime `q ≡ 1 (mod 3)` the support defect is positive. Whether the literature
already excludes the zero defect profile was not checked; the short chain here is self
contained. -/
theorem one_le_supportDefect {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hq3 : q % 3 = 1) : 1 ≤ supportDefect N q := by
  by_contra hZ'
  have hZ : supportDefect N q = 0 := by omega
  obtain ⟨h3, hb, hW, hexp, hmu, hL⟩ := zero_defect_facts h hq hodd hZ
  have hq4 := (special_mod_four h hq hodd).1
  have hqP := special_mem₃ h hq hodd
  have hqX : q ∈ insert q (highPrimes N q) := Finset.mem_insert_self _ _
  have h3P : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, h.ne_zero⟩
  have hb2 : N.factorization 3 = 2 := by
    rcases hb with hb | hb
    · exact hb
    · exact absurd hb (factorization_three_ne_four_of_supportDefect_eq_zero h hq hodd hZ)
  have hsp := succ_dvd_sigma_special hq hodd
  -- `σ(3 ^ 2) = 13`
  have h13 : 13 ∈ N.primeFactors := (mem_of_dvd_sigma h h3P (by norm_num) (by norm_num)
    (by rw [hb2, sigma_prime_sq Nat.prime_three]; norm_num [phi3])).1
  have hq13 : (13 : ℕ) ≠ q := by
    rintro rfl
    exact high_absurd (t := 7) h hL hqX hqP (by norm_num)
      ((by norm_num : 7 ∣ 13 + 1).trans hsp) (by norm_num) (by norm_num) (by norm_num)
  rcases hexp 13 h13 hq13 with e13 | e13
  swap
  · -- `σ(13 ^ 4) = 30941` and `σ(30941 ^ 2) = 157 * 433 * 14083`
    have h30941 : 30941 ∈ N.primeFactors := (mem_of_dvd_sigma h h13 (by norm_num) (by norm_num)
      (by rw [e13, sigma_pow_four (by norm_num)]; norm_num)).1
    have hq' : (30941 : ℕ) ≠ q := by omega
    have e' := hW 30941 h30941 hq' (by norm_num)
    by_cases hq157 : q = 157
    · exact sq_two_absurd (t := 433) (u := 14083) h hmu h30941 hq' e' (by norm_num)
        (by norm_num) (by norm_num) (by norm_num [phi3]) (by norm_num [phi3]) (by norm_num)
        (by norm_num) (by omega) (by omega)
    · exact sq_two_absurd (t := 157) (u := 14083) h hmu h30941 hq' e' (by norm_num)
        (by norm_num) (by norm_num) (by norm_num [phi3]) (by norm_num [phi3]) (by norm_num)
        (by norm_num) (by omega) (by omega)
  -- `σ(13 ^ 2) = 3 * 61`
  have h61 : 61 ∈ N.primeFactors := (mem_of_dvd_sigma h h13 (by norm_num) (by norm_num)
    (by rw [e13, sigma_prime_sq (by norm_num)]; norm_num [phi3])).1
  have hq61 : (61 : ℕ) ≠ q := by
    rintro rfl
    exact high_absurd (t := 31) h hL hqX hqP (by norm_num)
      ((by norm_num : 31 ∣ 61 + 1).trans hsp) (by norm_num) (by norm_num) (by norm_num)
  rcases hexp 61 h61 hq61 with e61 | e61
  · -- `σ(61 ^ 2) = 3 * 13 * 97`
    by_cases hq97 : q = 97
    · subst hq97
      exact high_absurd (t := 7) h hL hqX hqP (by norm_num)
        ((by norm_num : 7 ∣ 97 + 1).trans hsp) (by norm_num) (by norm_num) (by norm_num)
    · exact sq_two_absurd (t := 13) (u := 97) h hmu h61 hq61 e61 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num [phi3]) (by norm_num [phi3]) (by norm_num) (by norm_num)
        hq13 (by omega)
  -- `5 ∣ σ(61 ^ 4)`, `σ(5 ^ 2) = 31`
  have h5 : 5 ∈ N.primeFactors := (mem_of_dvd_sigma h h61 (by norm_num) (by norm_num)
    (by rw [e61, sigma_pow_four (by norm_num)]; norm_num)).1
  have e5 := hW 5 h5 (by omega) (by norm_num)
  have h31 : 31 ∈ N.primeFactors := (mem_of_dvd_sigma h h5 (by norm_num) (by norm_num)
    (by rw [e5, sigma_prime_sq (by norm_num)]; norm_num [phi3])).1
  have hq31 : (31 : ℕ) ≠ q := by omega
  rcases hexp 31 h31 hq31 with e31 | e31
  swap
  · -- `11 ∣ σ(31 ^ 4)`
    exact eleven_absurd h hq hodd hZ (mem_of_dvd_sigma h h31 (by norm_num) (by norm_num)
      (by rw [e31, sigma_pow_four (by norm_num)]; norm_num)).1
  -- `σ(31 ^ 2) = 3 * 331`
  have h331 : 331 ∈ N.primeFactors := (mem_of_dvd_sigma h h31 (by norm_num) (by norm_num)
    (by rw [e31, sigma_prime_sq (by norm_num)]; norm_num [phi3])).1
  have hq331 : (331 : ℕ) ≠ q := by omega
  rcases hexp 331 h331 hq331 with e331 | e331
  · -- three square primes that are 1 modulo 3, against `v_3(N) = 2`
    have hC := card_squarePrimes_one_add_le h hq hodd
    have hsub : ({13, 31, 331} : Finset ℕ) ⊆ (squarePrimes N q).filter fun p => p % 3 = 1 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [squarePrimes, Finset.mem_filter]
      rcases hx with rfl | rfl | rfl
      · exact ⟨⟨h13, hq13, e13⟩, by norm_num⟩
      · exact ⟨⟨h31, hq31, e31⟩, by norm_num⟩
      · exact ⟨⟨h331, hq331, e331⟩, by norm_num⟩
    have hcard := Finset.card_le_card hsub
    rw [show ({13, 31, 331} : Finset ℕ).card = 3 by decide] at hcard
    omega
  · -- `σ(331 ^ 4) = 5 * 37861 * 63601`
    have hX := mem_high h331 hq331 e331
    have hd : ∀ t, t = 37861 ∨ t = 63601 → t ∣ σ 1 (331 ^ N.factorization 331) := by
      rintro t (rfl | rfl) <;> rw [e331, sigma_pow_four (by norm_num)] <;> norm_num
    by_cases hq37861 : q = 37861
    · exact high_absurd (t := 63601) h hL hX h331 (by norm_num) (hd _ (Or.inr rfl))
        (by norm_num) (by omega) (by norm_num)
    · exact high_absurd (t := 37861) h hL hX h331 (by norm_num) (hd _ (Or.inl rfl))
        (by norm_num) (by omega) (by norm_num)

/-- Without 3: an escape row `p` has `phi3 p = q ^ j` (a shape `3 * q ^ j` would put 3 in `N`),
so there is at most one escape row. -/
theorem card_escapeRows_le_one_of_not_three_dvd {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (h3 : ¬ 3 ∣ N) : (escapeRows N q).card ≤ 1 := by
  have hq4 := (special_mod_four h hq hodd).1
  have hshape : ∀ p ∈ escapeRows N q, Odd p ∧ ∃ j, 1 ≤ j ∧ phi3 p = 1 * q ^ j := by
    intro p hp
    obtain ⟨hpo, j, hj, hs | hs⟩ := phi3_escapeRow h hp
    · exact ⟨hpo, j, hj, by rw [hs, one_mul]⟩
    · exfalso
      obtain ⟨hpS, -⟩ := mem_escapeRows.mp hp
      simp only [squarePrimes, Finset.mem_filter] at hpS
      obtain ⟨hpN, -, he⟩ := hpS
      have hpp := Nat.prime_of_mem_primeFactors hpN
      exact h3 (OPNStarter.force_prime h.perfect hpp he Nat.prime_three (by norm_num)
        (by rw [sigma_prime_sq hpp, hs]; exact dvd_mul_right 3 _))
  rw [Finset.card_le_one]
  intro a ha b hb
  obtain ⟨hao, j, hj, hsa⟩ := hshape a ha
  obtain ⟨hbo, k, hk, hsb⟩ := hshape b hb
  exact phi3_eq_mul_prime_pow_unique hq hq4 (Or.inl rfl) hao hbo hj hk hsa hsb

/-- For every special prime `q` of an odd perfect number `N` with exponent `a`, and `T` the total
excess, `ω(N) + 2 * v_3(σ(q ^ a)) ≤ 5 * T + 6`. No classical input. Whether this bound is new
has not been verified. The total excess is not bounded. -/
theorem card_primeFactors_add_two_mul_le_five_excess_add_six {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) :
    N.primeFactors.card + 2 * padicValNat 3 (σ 1 (q ^ N.factorization q)) ≤
      5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 6 := by
  have h3q := three_ne_special₃ h hq hodd
  have hq3 : q % 3 = 1 ∨ q % 3 = 2 := by
    have : q % 3 ≠ 0 := fun h0 => h3q ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp
      (Nat.dvd_of_mod_eq_zero h0))
    omega
  rcases hq3 with hq3 | hq3
  · have hI := card_primeFactors_add_two_mul_add_defect_eq h hq hodd
    have hZ := one_le_supportDefect h hq hodd hq3
    have hH := card_escapeRows_le_two h hq hodd
    omega
  · have := card_primeFactors_add_two_mul_le_five_excess_add_five h hq hodd hq3
    omega

/-- For every special prime, `ω(N) ≤ 5 * T + 6`, where `T` is the total excess. No classical
input. The total excess is not bounded. -/
theorem card_primeFactors_le_five_excess_add_six {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    N.primeFactors.card ≤ 5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 6 := by
  have := card_primeFactors_add_two_mul_le_five_excess_add_six h hq hodd
  omega

/-- If `3 ∤ N`, then `ω(N) ≤ 5 * T + 2`, where `T` is the total excess. -/
theorem card_primeFactors_le_five_excess_add_two_of_not_three_dvd {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (h3 : ¬ 3 ∣ N) :
    N.primeFactors.card ≤ 5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 2 := by
  have hI := card_primeFactors_add_two_mul_add_defect_eq h hq hodd
  have hZ : 4 ≤ supportDefect N q := by
    unfold supportDefect
    rw [if_neg h3]
    omega
  have hH := card_escapeRows_le_one_of_not_three_dvd h hq hodd h3
  omega

/-- For every special prime, `N < 2 ^ 4 ^ (5 * T + 6)`, where `T` is the total excess. No
classical input. -/
theorem lt_two_pow_four_pow_excess_add_six {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    N < 2 ^ 4 ^ (5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 6) :=
  (lt_two_pow_four_pow h).trans_le (Nat.pow_le_pow_right two_pos
    (Nat.pow_le_pow_right (by norm_num) (card_primeFactors_le_five_excess_add_six h hq hodd)))

/-- In the form `N = q ^ a * m ^ 2` with `q ∤ m`, `ω(N) ≤ 5 * (Ω(m) - ω(m)) + 6`. No
classical input. -/
theorem cardDistinctFactors_le_five_mul_sub_add_six {N q a m : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hqm : ¬ q ∣ m) (hN' : N = q ^ a * m ^ 2) :
    ArithmeticFunction.cardDistinctFactors N ≤
      5 * (ArithmeticFunction.cardFactors m - ArithmeticFunction.cardDistinctFactors m) + 6 := by
  obtain ⟨hodd, hT⟩ := euler_form_excess h hq hqm hN'
  rw [cardDistinctFactors_eq_card_primeFactors, ← hT]
  exact card_primeFactors_le_five_excess_add_six h hq hodd

end OddPerfect

#print axioms OddPerfect.zero_defect_facts
#print axioms OddPerfect.factorization_three_ne_four_of_supportDefect_eq_zero
#print axioms OddPerfect.one_le_supportDefect
#print axioms OddPerfect.card_escapeRows_le_one_of_not_three_dvd
#print axioms OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_six
#print axioms OddPerfect.card_primeFactors_le_five_excess_add_six
#print axioms OddPerfect.card_primeFactors_le_five_excess_add_two_of_not_three_dvd
#print axioms OddPerfect.lt_two_pow_four_pow_excess_add_six
#print axioms OddPerfect.cardDistinctFactors_le_five_mul_sub_add_six
