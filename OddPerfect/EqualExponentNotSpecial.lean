import OddPerfect.ExponentTenTwelve

/-!
# Equal exponents `l - 1`: the prime `l` is ordinary

Let `N` be an odd perfect number with special prime `q` and let `l` be an odd prime such that
every ordinary exponent (the exponent of every prime factor other than `q`) equals `l - 1`.

Restricted family result. The statement that `l` is not the special prime is attributed in
the literature to Kanold (1941); that source was not checked. No published source was checked
for the interface statements; novelty not verified.

The core statement (the special prime `q` cannot have all ordinary exponents equal to
`q - 1`) is already landed as `not_all_exponents_pred_of_special` (module
`ExponentTenTwelve`), and in the more general form `false_of_special_succ_eq_pow` (module
`EqualExponentsBound`). This module packages it with Steuerwald's prime length argument
`not_all_exponents_eq_pred_prime` into interface statements:

* `ordinary_of_all_exponents_eq_pred`: `l` is an ordinary prime factor of `N`.
* `card_mod_one_le_of_all_exponents_eq_pred`: at most `l` prime factors of `N` are `1`
  modulo `l` (at most `l - 1` ordinary ones, plus possibly `q`).
* `sigma_pred_dvd_of_ordinary`: `σ(p ^ (l - 1)) ∣ N` for every ordinary `p` with
  `v_p(N) = l - 1`.

The prime factors of `σ(p ^ (l - 1))` are `l` or `1` modulo `l` by the landed
`prime_dvd_sigma_prime_pow_of_prime_length` (module `Cyclotomic`).
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- If `r ≡ 1 (mod m)` then the geometric sum `∑_{i < n} r ^ i` is `≡ n (mod m)`. (A copy
of a private lemma of `Steuerwald`.) -/
private lemma eqExpNotSpecial_geom_sum_mod {r m : ℕ} (hr : r % m = 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, r ^ i) % m = n % m := by
  rw [Finset.sum_nat_mod]
  have : ∀ i ∈ Finset.range n, r ^ i % m = 1 % m := fun i _ => by
    rw [Nat.pow_mod, hr, one_pow]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul,
    ← Nat.mod_mod_of_dvd _ (dvd_refl m), Nat.mul_mod, Nat.mod_mod, Nat.mod_mod,
    ← Nat.mul_mod, mul_one]

/-- If every ordinary exponent of the odd perfect number `N` equals `l - 1` for an odd prime
`l`, then `l` is an ordinary prime factor of `N`: `l ∣ N` by Steuerwald's prime length
argument, and `l ≠ q` by Kanold's congruence modulo `l`. -/
theorem ordinary_of_all_exponents_eq_pred {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    l ∈ N.primeFactors ∧ l ≠ q := by
  have hlN : l ∣ N := by
    by_contra hlN
    exact not_all_exponents_eq_pred_prime h hq hodd hl hl2 hlN hexp
  refine ⟨Nat.mem_primeFactors.mpr ⟨hl, hlN, h.ne_zero⟩, ?_⟩
  rintro rfl
  exact not_all_exponents_pred_of_special h hl hodd hexp

/-- If every ordinary exponent of the odd perfect number `N` equals `l - 1` for an odd prime
`l`, then at most `l` prime factors of `N` are `1` modulo `l`. -/
theorem card_mod_one_le_of_all_exponents_eq_pred {N q l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    (N.primeFactors.filter (fun p => p % l = 1)).card ≤ l := by
  obtain ⟨hlN, hlq⟩ := ordinary_of_all_exponents_eq_pred h hq hodd hl hl2 hexp
  have hc := card_erase_special_le h hl hl2 (hexp l hlN hlq) hexp
    (N.primeFactors.filter (fun p => p % l = 1)) fun p hp => by
      obtain ⟨hpN, hp1⟩ := Finset.mem_filter.mp hp
      exact ⟨Nat.prime_of_mem_primeFactors hpN, Nat.dvd_of_mem_primeFactors hpN, hp1⟩
  have := Finset.pred_card_le_card_erase (s := N.primeFactors.filter (fun p => p % l = 1))
    (a := q)
  have := hl.two_le
  omega

/-- For an ordinary prime factor `p` of the odd perfect number `N` with `v_p(N) = l - 1`, the
divisor sum `σ(p ^ (l - 1))` divides `N` (it divides `σ N = 2 N` and is odd, since `l - 1`
is even). -/
theorem sigma_pred_dvd_of_ordinary {N q l p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hp : p ∈ N.primeFactors) (hpq : p ≠ q)
    (he : N.factorization p = l - 1) : σ 1 (p ^ (l - 1)) ∣ N := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hev := even_factorization_of_ne h hq hodd hpp hpq
  rw [he] at hev
  obtain ⟨r, hr⟩ := hev
  have hpodd : p % 2 = 1 :=
    Nat.odd_iff.mp (h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
  have hσodd : Odd (σ 1 (p ^ (l - 1))) := by
    rw [Nat.odd_iff, sigma_one_apply_prime_pow hpp, eqExpNotSpecial_geom_sum_mod hpodd]
    omega
  exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hσodd)
    (OPNStarter.component_sigma_dvd h.perfect hpp he)

end OddPerfect

#print axioms OddPerfect.ordinary_of_all_exponents_eq_pred
#print axioms OddPerfect.card_mod_one_le_of_all_exponents_eq_pred
#print axioms OddPerfect.sigma_pred_dvd_of_ordinary
