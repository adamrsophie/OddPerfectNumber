import OddPerfect.ClosedLoop
import OddPerfect.SteuerwaldThree
import OddPerfect.Seed.Example

/-!
# Steuerwald's theorem and its prime length generalization

Steuerwald (1937): in an odd perfect number the primes other than the special prime
cannot all have exponent exactly two. The case `3 ∣ N` is `steuerwald_of_three_dvd`.
For an odd prime `l` with `l ∤ N` and every ordinary exponent `e` satisfying `l ∣ e + 1`,
every prime divisor of `σ(p ^ (l - 1))` is forced to be the special prime, so each
`σ(p ^ (l - 1))` is a power of it. When all ordinary exponents equal `l - 1` this closes
the loop of `not_all_components_special_powers`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- If `r ≡ 1 (mod m)` then the geometric sum `∑_{i < n} r ^ i` is `≡ n (mod m)`. -/
private lemma geom_sum_mod_of_mod_eq_one {r m : ℕ} (hr : r % m = 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, r ^ i) % m = n % m := by
  rw [Finset.sum_nat_mod]
  have : ∀ i ∈ Finset.range n, r ^ i % m = 1 % m := fun i _ => by
    rw [Nat.pow_mod, hr, one_pow]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul,
    ← Nat.mod_mod_of_dvd _ (dvd_refl m), Nat.mul_mod, Nat.mod_mod, Nat.mod_mod,
    ← Nat.mul_mod, mul_one]

/-- If an odd prime `l` does not divide `N` and `l ∣ e + 1` for every ordinary exponent `e`,
then every ordinary prime `p` has `σ(p ^ (l - 1))` equal to a positive power of the special
prime. -/
theorem sigma_pred_prime_eq_special_pow {N q l p : ℕ} (h : OddPerfect N) (_hq : q.Prime)
    (_hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2) (hlN : ¬ l ∣ N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1)
    (hp : p ∈ N.primeFactors) (hpq : p ≠ q) : ∃ c : ℕ, 0 < c ∧ σ 1 (p ^ (l - 1)) = q ^ c := by
  have hN0 := h.ne_zero
  have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl.one_lt.le
  -- (1) no ordinary prime is `1 (mod l)`
  have hnot1 : ∀ r ∈ N.primeFactors, r ≠ q → r % l ≠ 1 := by
    intro r hr hrq hr1
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hdvd : σ 1 (r ^ (l - 1)) ∣ σ 1 (r ^ N.factorization r) :=
      OPNExample.sigma_prime_pow_dvd hrp (hl1 ▸ hexp r hr hrq)
    have hl0 : l ∣ σ 1 (r ^ (l - 1)) := by
      rw [sigma_one_apply_prime_pow hrp, hl1, Nat.dvd_iff_mod_eq_zero,
        geom_sum_mod_of_mod_eq_one hr1, Nat.mod_self]
    exact hlN (OPNStarter.force_prime h.perfect hrp rfl hl hl2 (hl0.trans hdvd))
  -- (2) every prime divisor of `σ(p ^ (l - 1))` is `q`
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpodd : p % 2 = 1 :=
    Nat.odd_iff.mp (h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
  have hlodd : l % 2 = 1 := Nat.odd_iff.mp (hl.odd_of_ne_two hl2)
  have hσodd : σ 1 (p ^ (l - 1)) % 2 = 1 := by
    rw [sigma_one_apply_prime_pow hpp, hl1, geom_sum_mod_of_mod_eq_one hpodd, hlodd]
  have hall : ∀ {t : ℕ}, t.Prime → t ∣ σ 1 (p ^ (l - 1)) → t = q := by
    intro t ht htd
    have ht2 : t ≠ 2 := by
      rintro rfl
      omega
    have htN : t ∣ N := OPNStarter.force_prime h.perfect hpp rfl ht ht2
      (htd.trans (OPNExample.sigma_prime_pow_dvd hpp (hl1 ▸ hexp p hp hpq)))
    have htl : t % l = 1 :=
      (prime_dvd_sigma_prime_pow_of_prime_length hpp ht hl htd).resolve_left
        (by rintro rfl; exact hlN htN)
    by_contra htq
    exact hnot1 t (Nat.mem_primeFactors.mpr ⟨ht, htN, hN0⟩) htq htl
  -- (3) hence a positive power of `q`
  have hge : p ≤ σ 1 (p ^ (l - 1)) := by
    rw [sigma_one_apply_prime_pow hpp]
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ _ := Finset.single_le_sum (f := fun i => p ^ i) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (by have := hl.two_le; omega))
  have hσ0 : σ 1 (p ^ (l - 1)) ≠ 0 := by have := hpp.two_le; omega
  refine ⟨_, ?_, Nat.eq_prime_pow_of_unique_prime_dvd hσ0 hall⟩
  rw [List.length_pos_iff, ne_eq, Nat.primeFactorsList_eq_nil]
  have := hpp.two_le
  omega

/-- If an odd prime `l` does not divide `N`, the ordinary exponents cannot all equal `l - 1`. -/
theorem not_all_exponents_eq_pred_prime {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2) (hlN : ¬ l ∣ N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) : False := by
  have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl.one_lt.le
  have hexp' : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1 := fun p hp hpq => by
    rw [hexp p hp hpq, hl1]
  refine not_all_components_special_powers h hq hodd fun p hp hpq => ?_
  obtain ⟨c, -, hc⟩ := sigma_pred_prime_eq_special_pow h hq hodd hl hl2 hlN hexp' hp hpq
  exact ⟨c, by rw [hexp p hp hpq, hc]⟩

/-- Steuerwald's theorem, case `3 ∤ N`. -/
theorem steuerwald_of_not_three_dvd {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 2) (h3 : ¬ 3 ∣ N) : False :=
  not_all_exponents_eq_pred_prime h hq hodd Nat.prime_three (by decide) h3 hsq

/-- Steuerwald: the primes other than the special prime cannot all have exponent two. -/
theorem steuerwald {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 2) : False := by
  by_cases h3 : 3 ∣ N
  · exact steuerwald_of_three_dvd h hq hodd hsq h3
  · exact steuerwald_of_not_three_dvd h hq hodd hsq h3

/-- Unconditional form: some prime factor has an even exponent at least four. -/
theorem exists_even_exponent_ge_four {N : ℕ} (h : OddPerfect N) :
    ∃ p ∈ N.primeFactors, Even (N.factorization p) ∧ 4 ≤ N.factorization p := by
  obtain ⟨q, hq, -, -, hk, hev⟩ := exists_special_prime h
  by_contra hne
  simp only [not_exists, not_and, not_le] at hne
  refine steuerwald h hq (Nat.odd_iff.mpr (by omega)) fun p hp hpq => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  have he := hev p hpp hpq
  have h1 := (hpp.dvd_iff_one_le_factorization h.ne_zero).mp (Nat.dvd_of_mem_primeFactors hp)
  have h4 := hne p hp he
  obtain ⟨j, hj⟩ := he
  omega

/-- In Euler's form `N = q^k m^2`, the number `m` is not squarefree. -/
theorem not_squarefree_of_euler_form {N q k m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) : ¬ Squarefree m := by
  intro hsf
  have hN0 := h.ne_zero
  have hm0 : m ≠ 0 := by rintro rfl; simp [hN] at hN0
  have hq0 : q ^ k ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hfac : ∀ p, N.factorization p = k * q.factorization p + 2 * m.factorization p := by
    intro p
    rw [hN, Nat.factorization_mul hq0 (pow_ne_zero _ hm0), Finsupp.add_apply,
      Nat.factorization_pow, Nat.factorization_pow]
    rfl
  have hkq : N.factorization q = k := by
    rw [hfac, hq.factorization_self, Nat.factorization_eq_zero_of_not_dvd hqm]
    ring
  have hk : Odd k := by
    by_contra hk
    obtain ⟨j, rfl⟩ := Nat.not_odd_iff_even.mp hk
    exact not_isSquare h ⟨q ^ j * m, by rw [hN]; ring⟩
  refine steuerwald h hq (hkq ▸ hk) fun p hp hpq => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpm : p ∣ m := by
    have hpN := Nat.dvd_of_mem_primeFactors hp
    rw [hN] at hpN
    rcases (Nat.Prime.dvd_mul hpp).mp hpN with h1 | h1
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp hq).mp (hpp.dvd_of_dvd_pow h1)) hpq
    · exact hpp.dvd_of_dvd_pow h1
  have h1 := hpp.factorization_pos_of_dvd hm0 hpm
  have h2 := hsf.natFactorization_le_one p
  rw [hfac, hq.factorization, Finsupp.single_apply, if_neg (Ne.symm hpq)]
  omega

end OddPerfect

#print axioms OddPerfect.sigma_pred_prime_eq_special_pow
#print axioms OddPerfect.not_all_exponents_eq_pred_prime
#print axioms OddPerfect.steuerwald_of_not_three_dvd
#print axioms OddPerfect.steuerwald
#print axioms OddPerfect.exists_even_exponent_ge_four
#print axioms OddPerfect.not_squarefree_of_euler_form
