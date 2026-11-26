import OddPerfect.RestrainedTen

/-!
# Restrained odd perfect numbers: the exact prime count

Setting of `restrained_omega_le`: `N` is an odd perfect number with special prime `q` and
exponent `a = v_q(N)`, `r ≠ q` is a further prime, and every prime factor other than `q` and `r`
has exponent exactly 2. The landed results give `r = 3` and `q ≡ 1 (mod 12)`. Write
`E = v_3(N)`, `O1` for the prime factors other than 3 and `q` that are 1 modulo 3, and `O2` for
those that are 2 modulo 3.

* `restrained_three_eq`: `E = #O1 + v_3(a + 1)`. The exponent of 3 is the sum of the weights
  sent to 3: a member of `O1` sends exactly one, a member of `O2` none, the component of 3 none,
  and the special component `v_3(σ(q ^ a)) = v_3(a + 1)`.
* `restrained_omega_eq`: `ω(N) + v_3(a + 1) = E + 2 + #O2`, since the prime factors are 3, `q`,
  `O1` and `O2`.
* `restrained_prod_sq_dvd`: `∏ t ∈ O2, t ^ 2 ∣ σ(3 ^ E) (σ(q ^ a) / 2)`. A member of `O2`
  receives its exponent 2 only from the components of 3 and `q` (`restrained_two_sources`), and
  it is odd while `σ(q ^ a)` is even.
* `restrained_pow_card_le` and `restrained_pow_omega_le`: as every member of `O2` is at least
  132257, `132257 ^ (2 #O2)` and `132257 ^ (2 (ω(N) + v_3(a + 1) − E − 2))` are at most
  `σ(3 ^ E) (σ(q ^ a) / 2)`.

The counting is of the type of a lemma of Ochem and Zelinsky (arXiv 2607.19746); see the
docstring of `restrained_omega_le`. These are conditional family results checked by the kernel;
no novelty is claimed. The odd perfect number conjecture is open and nothing here decides it.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.omega ArithmeticFunction.Omega

namespace OddPerfect

open RestrainedSeven

namespace RestrainedFifteen

/-- `σ(q ^ k)` is even for an odd prime `q` and an odd exponent `k`. -/
theorem two_dvd_sigma_odd {q k : ℕ} (hq : q.Prime) (hq2 : q % 2 = 1) (hk : Odd k) :
    2 ∣ σ 1 (q ^ k) := by
  rw [sigma_one_apply_prime_pow hq, Nat.dvd_iff_mod_eq_zero, Finset.sum_nat_mod]
  simp only [Nat.pow_mod, hq2, one_pow, Nat.one_mod, Finset.sum_const, Finset.card_range,
    smul_eq_mul, mul_one]
  obtain ⟨j, rfl⟩ := hk
  omega

/-- The product of the squares of a finite set of primes divides every common multiple of the
squares. -/
theorem prod_sq_dvd {s : Finset ℕ} {n : ℕ} (hp : ∀ t ∈ s, t.Prime) (hd : ∀ t ∈ s, t ^ 2 ∣ n) :
    (∏ t ∈ s, t ^ 2) ∣ n := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx]
    have hx' := hp x (Finset.mem_insert_self _ _)
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (hd x (Finset.mem_insert_self _ _))
      (ih (fun t ht => hp t (Finset.mem_insert_of_mem ht))
        (fun t ht => hd t (Finset.mem_insert_of_mem ht)))
    refine Nat.Coprime.prod_right fun t ht => ?_
    have hne : x ≠ t := fun h => hx (h ▸ ht)
    exact Nat.Coprime.pow 2 2
      ((Nat.coprime_primes hx' (hp t (Finset.mem_insert_of_mem ht))).mpr hne)

end RestrainedFifteen

open RestrainedFifteen

/-- **Restrained family: the exponent of 3.** `v_3(N) = #O1 + v_3(a + 1)` with `a = v_q(N)` and
`O1` the prime factors other than 3 and `q` that are 1 modulo 3. Every member `s` of `O1` has
exponent 2 and `σ(s ^ 2) = s ^ 2 + s + 1` is divisible by 3 exactly once; a prime factor that is
2 modulo 3 sends nothing to 3; and `v_3(σ(q ^ a)) = v_3(a + 1)` as `q ≡ 1 (mod 3)`.
Conditional family result; no novelty is claimed. -/
theorem restrained_three_eq {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    N.factorization 3 = {p ∈ N.primeFactors | p ≠ 3 ∧ p ≠ q ∧ p % 3 = 1}.card +
      padicValNat 3 (N.factorization q + 1) := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have hq3 : q % 3 = 1 := by have := F.mod12; omega
  have hqN : q ∈ N.primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hq, Nat.dvd_of_factorization_pos ?_, h.ne_zero⟩
    obtain ⟨k, hk⟩ := hodd
    omega
  have key : ∀ p ∈ N.primeFactors, sigmaWeight N p 3 =
      (if p ≠ 3 ∧ p ≠ q ∧ p % 3 = 1 then 1 else 0) +
        (if p = q then padicValNat 3 (N.factorization q + 1) else 0) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    rw [sigmaWeight_eq_padicValNat _ _ Nat.prime_three]
    by_cases hp3 : p = 3
    · subst hp3
      have h3q : (3 : ℕ) ≠ q := by omega
      simp [padicValNat_three_sigma_three_pow, h3q]
    by_cases hpq : p = q
    · subst hpq
      simp [padicValNat_three_sigma_prime_pow_of_mod_one hpp hq3]
    rw [F.sq p hp hpq hp3]
    have hm : p % 3 ≠ 0 := fun h0 =>
      hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).mp (Nat.dvd_of_mod_eq_zero h0)).symm
    by_cases h1 : p % 3 = 1
    · rw [padicValNat_three_sigma_prime_pow_of_mod_one hpp h1]
      simp [hp3, hpq, h1, Nat.padicValNat_def, Nat.multiplicity_self (by norm_num : 1 < 3)]
    · have h2 : p % 3 = 2 := by omega
      rw [padicValNat_three_sigma_prime_pow_of_mod_two hpp h2]
      simp [hpq, h1]
  have hsum := sigmaWeight_sum_eq h.perfect Nat.prime_three (by decide)
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_boole,
    Finset.sum_ite_eq', if_pos hqN] at hsum
  simpa using hsum.symm

/-- **Restrained family: the exact prime count.** `ω(N) + v_3(a + 1) = v_3(N) + 2 + #O2` with
`a = v_q(N)` and `O2` the prime factors other than 3 and `q` that are 2 modulo 3: the prime
factors are 3, `q` and the members of `O1` and `O2`, and `v_3(N) = #O1 + v_3(a + 1)`.
Conditional family result; no novelty is claimed. -/
theorem restrained_omega_eq {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    ω N + padicValNat 3 (N.factorization q + 1) =
      N.factorization 3 + 2 + {p ∈ N.primeFactors | p ≠ 3 ∧ p ≠ q ∧ p % 3 = 2}.card := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have hq3 : q % 3 = 1 := by have := F.mod12; omega
  have hqN : q ∈ N.primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hq, Nat.dvd_of_factorization_pos ?_, h.ne_zero⟩
    obtain ⟨k, hk⟩ := hodd
    omega
  have h3N : 3 ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_three, restrained_three_dvd h hq hodd hr hrq hsq,
      h.ne_zero⟩
  have hE := restrained_three_eq h hq hodd hr hrq hsq
  have key : ∀ p ∈ N.primeFactors, 1 =
      (if p = 3 then 1 else 0) + (if p = q then 1 else 0) +
        ((if p ≠ 3 ∧ p ≠ q ∧ p % 3 = 1 then 1 else 0) +
          (if p ≠ 3 ∧ p ≠ q ∧ p % 3 = 2 then 1 else 0)) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hm : p = 3 ∨ p % 3 = 1 ∨ p % 3 = 2 := by
      by_cases hp3 : p = 3
      · exact Or.inl hp3
      have : p % 3 ≠ 0 := fun h0 => hp3
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).mp (Nat.dvd_of_mod_eq_zero h0)).symm
      omega
    split_ifs <;> omega
  have hcard : N.primeFactors.card = ∑ p ∈ N.primeFactors, 1 := Finset.card_eq_sum_ones _
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos h3N, if_pos hqN,
    Finset.sum_boole, Finset.sum_boole] at hcard
  rw [cardDistinctFactors_eq_card_primeFactors]
  simp only [Nat.cast_id] at hcard
  omega

/-- **Restrained family: the primes that are 2 modulo 3.** The product of the squares of the
members of `O2` divides `σ(3 ^ E) (σ(q ^ a) / 2)` with `E = v_3(N)` and `a = v_q(N)`: each
member `t` has exponent 2, received only from the components of 3 and `q`
(`restrained_two_sources`), and `t` is odd while `σ(q ^ a)` is even.
Conditional family result; no novelty is claimed. -/
theorem restrained_prod_sq_dvd {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    (∏ t ∈ {p ∈ N.primeFactors | p ≠ 3 ∧ p ≠ q ∧ p % 3 = 2}, t ^ 2) ∣
      σ 1 (3 ^ N.factorization 3) * (σ 1 (q ^ N.factorization q) / 2) := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have h2q : 2 ∣ σ 1 (q ^ N.factorization q) :=
    two_dvd_sigma_odd hq (by have := F.mod12; omega) hodd
  refine prod_sq_dvd (fun t ht => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp ht).1)
    fun t ht => ?_
  obtain ⟨htN, -, -, ht3⟩ := Finset.mem_filter.mp ht
  obtain ⟨htp, htd, -⟩ := Nat.mem_primeFactors.mp htN
  have : Fact t.Prime := ⟨htp⟩
  have ht2 : t ≠ 2 := by
    rintro rfl
    exact h.not_two_dvd htd
  have hs := restrained_two_sources h hq hodd hr hrq hsq htN ht3
  have hne3 : σ 1 (3 ^ N.factorization 3) ≠ 0 := (sigma_pos 1 _ (by positivity)).ne'
  have hneq : σ 1 (q ^ N.factorization q) ≠ 0 :=
    (sigma_pos 1 _ (pow_ne_zero _ hq.ne_zero)).ne'
  have hv : padicValNat t (σ 1 (3 ^ N.factorization 3) * σ 1 (q ^ N.factorization q)) = 2 := by
    rw [Nat.padicValNat_def, padicValNat.mul hne3 hneq]
    simpa only [Nat.padicValNat_def] using hs
  have hdvd : t ^ 2 ∣ σ 1 (3 ^ N.factorization 3) * σ 1 (q ^ N.factorization q) := by
    have : t ^ padicValNat t (σ 1 (3 ^ N.factorization 3) * σ 1 (q ^ N.factorization q)) ∣
        σ 1 (3 ^ N.factorization 3) * σ 1 (q ^ N.factorization q) := by
      rw [Nat.padicValNat_def]; exact pow_multiplicity_dvd _ _
    rwa [hv] at this
  have hcop : Nat.Coprime (t ^ 2) 2 :=
    Nat.Coprime.pow_left 2 ((Nat.coprime_primes htp Nat.prime_two).mpr ht2)
  refine hcop.dvd_of_dvd_mul_left ?_
  have he : σ 1 (q ^ N.factorization q) = 2 * (σ 1 (q ^ N.factorization q) / 2) :=
    (Nat.mul_div_cancel' h2q).symm
  rw [he] at hdvd
  rwa [mul_left_comm] at hdvd

/-- **Restrained family: size bound for the primes that are 2 modulo 3.**
`132257 ^ (2 #O2) ≤ σ(3 ^ E) (σ(q ^ a) / 2)`: every member of `O2` is at least 132257
(`restrained_le_of_ne_three`), and the right side is positive.
Conditional family result; no novelty is claimed. -/
theorem restrained_pow_card_le {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    132257 ^ (2 * {p ∈ N.primeFactors | p ≠ 3 ∧ p ≠ q ∧ p % 3 = 2}.card) ≤
      σ 1 (3 ^ N.factorization 3) * (σ 1 (q ^ N.factorization q) / 2) := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have h2q : 2 ∣ σ 1 (q ^ N.factorization q) :=
    two_dvd_sigma_odd hq (by have := F.mod12; omega) hodd
  have hneq : σ 1 (q ^ N.factorization q) ≠ 0 :=
    (sigma_pos 1 _ (pow_ne_zero _ hq.ne_zero)).ne'
  have hpos3 : 0 < σ 1 (3 ^ N.factorization 3) := sigma_pos 1 _ (by positivity)
  have hposq : 0 < σ 1 (q ^ N.factorization q) / 2 := by
    obtain ⟨c, hc⟩ := h2q
    rw [hc] at hneq ⊢
    omega
  refine le_trans ?_ (Nat.le_of_dvd (Nat.mul_pos hpos3 hposq)
    (restrained_prod_sq_dvd h hq hodd hr hrq hsq))
  rw [pow_mul]
  refine Finset.pow_card_le_prod _ _ _ fun t ht => ?_
  obtain ⟨htN, ht3, -, -⟩ := Finset.mem_filter.mp ht
  exact Nat.pow_le_pow_left (restrained_le_of_ne_three h hq hodd hr hrq hsq htN ht3) 2

/-- **Restrained family: size bound in terms of the prime count.**
`132257 ^ (2 (ω(N) + v_3(a + 1) − E − 2)) ≤ σ(3 ^ E) (σ(q ^ a) / 2)`, from
`restrained_omega_eq` and `restrained_pow_card_le`.
Conditional family result; no novelty is claimed. -/
theorem restrained_pow_omega_le {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    132257 ^ (2 * (ω N + padicValNat 3 (N.factorization q + 1) - N.factorization 3 - 2)) ≤
      σ 1 (3 ^ N.factorization 3) * (σ 1 (q ^ N.factorization q) / 2) := by
  have h1 := restrained_omega_eq h hq hodd hr hrq hsq
  have h2 := restrained_pow_card_le h hq hodd hr hrq hsq
  have he : ω N + padicValNat 3 (N.factorization q + 1) - N.factorization 3 - 2 =
      {p ∈ N.primeFactors | p ≠ 3 ∧ p ≠ q ∧ p % 3 = 2}.card := by omega
  rwa [he]

end OddPerfect

#print axioms OddPerfect.RestrainedFifteen.two_dvd_sigma_odd
#print axioms OddPerfect.RestrainedFifteen.prod_sq_dvd
#print axioms OddPerfect.restrained_three_eq
#print axioms OddPerfect.restrained_omega_eq
#print axioms OddPerfect.restrained_prod_sq_dvd
#print axioms OddPerfect.restrained_pow_card_le
#print axioms OddPerfect.restrained_pow_omega_le
