import OddPerfect.EulerIndexPair
import OddPerfect.Zsigmondy
import OddPerfect.PureRows

/-!
# The two rows of an Euler index supported on two primes

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly two prime factors.
`eulerIndex_pair_sender` (in `OddPerfect/EulerIndexPair.lean`) labels them `(t, u)` with
`σ(t ^ e) = q u ^ v` and `σ(u ^ f) = t ^ j`, `j > 0`, where `e = v_t(N)` and `f = v_u(N)`.
This module adds the shape of both rows.

* `sigma_prime_pow_eq_prime_pow_row` (pure row): for odd primes `u`, `t`, `f ≥ 1` and
  `σ(u ^ f) = t ^ j`, the exponent `f` is even, `f + 1` is prime, the order of `u` modulo `t`
  is `f + 1` and `t ≡ 1 (mod 2 (f + 1))`. That a prime power divisor sum has prime length is
  classical; the primality is `prime_succ_of_sigma_prime_pow_eq_prime_pow` from
  `OddPerfect/PureRows.lean`.
* `succ_prime_or_prime_sq_of_sigma_eq_mul_prime_pow` (sender row): for an odd prime `t`, an
  even `e ≥ 2` and `σ(t ^ e) = q u ^ v` with `q`, `u` prime, `e + 1` is prime or the square of a
  prime, and prime when `v = 0`.
* `eulerIndex_pair_rows`: both facts for the labeling of `eulerIndex_pair_sender`.

These are restricted results (special exponent 1, index supported on exactly two primes).
They do not exclude this case: infinitely many pairs of prime indices remain possible. Their
novelty has not been verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace EulerIndexPairRows

/-- `t ≡ 1 (mod n)` with `t` and `n` odd gives `t ≡ 1 (mod 2 n)`. -/
private lemma mod_two_mul_eq_one {t n : ℕ} (ht : Odd t) (hn : Odd n) (h : t % n = 1) :
    t % (2 * n) = 1 := by
  have hn3 : 3 ≤ n := by
    have h1 : n ≠ 1 := by
      rintro rfl
      rw [Nat.mod_one] at h
      exact absurd h (by decide)
    obtain ⟨k, hk⟩ := hn
    omega
  have hk : t = n * (t / n) + 1 := by
    have := Nat.div_add_mod t n
    rw [h] at this
    exact this.symm
  obtain ⟨c, hc⟩ : Even (t / n) := by
    have ht' := ht
    rw [hk, Nat.odd_add_one, Nat.not_odd_iff_even, Nat.even_mul] at ht'
    rcases ht' with he | he
    · exact absurd he (Nat.not_even_iff_odd.mpr hn)
    · exact he
  rw [hk, hc, show n * (c + c) + 1 = 1 + 2 * n * c by ring, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (by omega)]

end EulerIndexPairRows

open EulerIndexPairRows

/-- **Pure row of an odd prime.** Let `u` and `t` be odd primes, `f ≥ 1` and
`σ(u ^ f) = t ^ j`. Then `f` is even, `f + 1` is prime, the order of `u` modulo `t` is `f + 1`,
and `t ≡ 1 (mod 2 (f + 1))`. That a prime power divisor sum has prime length is classical;
nothing new is claimed. -/
theorem sigma_prime_pow_eq_prime_pow_row {u f t j : ℕ} (hu : u.Prime) (hu2 : u ≠ 2)
    (ht : t.Prime) (ht2 : t ≠ 2) (hf : f ≠ 0) (hrow : σ 1 (u ^ f) = t ^ j) :
    Even f ∧ (f + 1).Prime ∧ orderOf (u : ZMod t) = f + 1 ∧ t % (2 * (f + 1)) = 1 := by
  have huo := hu.odd_of_ne_two hu2
  have hto := ht.odd_of_ne_two ht2
  -- parity: `σ(u ^ f) ≡ f + 1 (mod 2)` and `t ^ j` is odd
  have hfe : Even f := by
    have hL : ((σ 1 (u ^ f) : ℕ) : ZMod 2) = ((f + 1 : ℕ) : ZMod 2) := by
      rw [sigma_one_apply_prime_pow hu]
      push_cast
      rw [ZMod.natCast_eq_one_iff_odd.mpr huo]
      simp
    have hR : ((t ^ j : ℕ) : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.mpr hto.pow
    rw [hrow, hR] at hL
    have := ZMod.natCast_eq_one_iff_odd.mp hL.symm
    rwa [Nat.odd_add_one, Nat.not_odd_iff_even] at this
  have hf2 : 2 ≤ f := by obtain ⟨c, hc⟩ := hfe; omega
  have hu3 : 3 ≤ u := by have := hu.two_le; omega
  have hprime := prime_succ_of_sigma_prime_pow_eq_prime_pow hu hu2 hfe hf ht hrow
  have hmod := receiver_mod_index_of_pure hu hu2 hf2 ht hrow
  obtain ⟨w, hw, hwd, ho, -⟩ :=
    exists_prime_dvd_sigma_orderOf_eq hu hu3 (by omega : 3 ≤ f + 1) (dvd_refl _)
  rw [hrow] at hwd
  rw [(Nat.prime_dvd_prime_iff_eq hw ht).mp (hw.dvd_of_dvd_pow hwd)] at ho
  have hfo : Odd (f + 1) := by
    rw [Nat.odd_add_one, Nat.not_odd_iff_even]; exact hfe
  exact ⟨hfe, hprime, ho, mod_two_mul_eq_one hto hfo hmod⟩

/-- **Sender row.** Let `t ≥ 3` be a prime, `e ≥ 2` even, `q` and `u` primes, and
`σ(t ^ e) = q u ^ v`. Then `e + 1` is prime or the square of a prime, and `e + 1` is prime when
`v = 0`. Each divisor `d ≥ 3` of `e + 1` yields a prime of `{q, u}` in which `t` has order `d`
(`exists_prime_dvd_sigma_orderOf_eq`), so `e + 1` has at most two divisors above 1. -/
theorem succ_prime_or_prime_sq_of_sigma_eq_mul_prime_pow {t e q u v : ℕ} (ht : t.Prime)
    (ht3 : 3 ≤ t) (he : Even e) (he2 : 2 ≤ e) (hq : q.Prime) (hu : u.Prime)
    (hrow : σ 1 (t ^ e) = q * u ^ v) :
    ((e + 1).Prime ∨ ∃ p, p.Prime ∧ e + 1 = p ^ 2) ∧ (v = 0 → (e + 1).Prime) := by
  have hmem : ∀ d, 3 ≤ d → d ∣ e + 1 →
      ∃ w, (w = q ∨ w = u) ∧ orderOf (t : ZMod w) = d := by
    intro d hd3 hd
    obtain ⟨w, hw, hwd, ho, -⟩ := exists_prime_dvd_sigma_orderOf_eq ht ht3 hd3 hd
    rw [hrow] at hwd
    refine ⟨w, ?_, ho⟩
    rcases (Nat.Prime.dvd_mul hw).mp hwd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hw hq).mp h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hw hu).mp (hw.dvd_of_dvd_pow h))
  refine ⟨?_, fun hv => ?_⟩
  · have hodd : ¬ 2 ∣ e + 1 := by obtain ⟨k, hk⟩ := he; omega
    have hn3 : 3 ≤ e + 1 := by omega
    have hp : (e + 1).minFac.Prime := Nat.minFac_prime (by omega)
    have hpd : (e + 1).minFac ∣ e + 1 := Nat.minFac_dvd _
    set p := (e + 1).minFac
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      rcases (show p = 2 ∨ 3 ≤ p by omega) with h | h
      · exact absurd (h ▸ hpd) hodd
      · exact h
    by_cases hpn : p = e + 1
    · left; rw [← hpn]; exact hp
    right
    refine ⟨p, hp, ?_⟩
    obtain ⟨c, hc⟩ := hpd
    have hcd : c ∣ e + 1 := ⟨p, by rw [hc, mul_comm]⟩
    have hc3 : 3 ≤ c := by
      rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ 3 ≤ c by omega) with h | h | h | h
      · rw [h, mul_zero] at hc; omega
      · rw [h, mul_one] at hc; exact absurd hc.symm hpn
      · rw [h] at hc; exact absurd ⟨p, by rw [hc, mul_comm]⟩ hodd
      · exact h
    obtain ⟨w1, hw1, ho1⟩ := hmem p hp3 ⟨c, hc⟩
    obtain ⟨w2, hw2, ho2⟩ := hmem (e + 1) hn3 (dvd_refl _)
    obtain ⟨w3, hw3, ho3⟩ := hmem c hc3 hcd
    have h12 : w1 ≠ w2 := by
      rintro rfl; exact hpn (ho1.symm.trans ho2)
    rcases (show w3 = w1 ∨ w3 = w2 by omega) with rfl | rfl
    · rw [ho1] at ho3
      rw [hc, ← ho3, sq]
    · rw [ho2] at ho3
      have h1 : p * c = 1 * c := by rw [← hc, one_mul, ho3]
      have := Nat.eq_of_mul_eq_mul_right (by omega : 0 < c) h1
      omega
  · exact prime_succ_of_sigma_prime_pow_eq_prime_pow ht (by omega) he (by omega) hq
      (by rw [hrow, hv, pow_zero, mul_one, pow_one])

variable {N q m r s : ℕ}

/-- **Two prime index, both rows.** Let `N = q m ^ 2` be an odd perfect number with special
prime `q` of exponent 1, `q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly
the two prime factors `r ≠ s`. For the labeling `(t, u)` of `eulerIndex_pair_sender`, with
`e = v_t(N)` and `f = v_u(N)`, all conclusions of that theorem hold, and moreover `f + 1` is
prime, the order of `u` modulo `t` is `f + 1`, `t ≡ 1 (mod 2 (f + 1))`, and `e + 1` is prime
or the square of a prime. This is a restricted result (special exponent 1, index supported on
exactly two primes); it does not exclude this case, since infinitely many pairs of prime
indices remain possible. Its novelty has not been verified. -/
theorem eulerIndex_pair_rows (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧
      (∃ v, σ 1 (t ^ N.factorization t) = q * u ^ v) ∧
      (∃ j, 0 < j ∧ σ 1 (u ^ N.factorization u) = t ^ j) ∧ ¬ t ∣ q + 1 ∧
      (eulerIndex q 1 m).factorization t = N.factorization t ∧
      (N.factorization u + 1).Prime ∧ orderOf (u : ZMod t) = N.factorization u + 1 ∧
      t % (2 * (N.factorization u + 1)) = 1 ∧
      ((N.factorization t + 1).Prime ∨ ∃ p, p.Prime ∧ N.factorization t + 1 = p ^ 2) := by
  obtain ⟨t, u, htu, hne, ⟨v, hA⟩, ⟨j, hj, hB⟩, h3, h4⟩ :=
    eulerIndex_pair_sender h hq hN hqm hr hs hrs hJ
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hJm := eulerIndex_dvd_sq h hq hN1 hqm
  have hfacts : ∀ p ∈ ({t, u} : Finset ℕ),
      p.Prime ∧ p ≠ 2 ∧ Even (N.factorization p) ∧ N.factorization p ≠ 0 := by
    intro p hp
    rw [htu, ← hJ] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpJ := Nat.dvd_of_mem_primeFactors hp
    have hpm : p ∣ m := hpp.dvd_of_dvd_pow (hpJ.trans hJm)
    have hpq : p ≠ q := by
      rintro rfl; exact hqm hpm
    have hfac : N.factorization p = 2 * m.factorization p := by
      rw [hN, Nat.factorization_mul hq.ne_zero (pow_ne_zero _ hm), Finsupp.add_apply,
        hq.factorization, Finsupp.single_apply, if_neg (Ne.symm hpq), zero_add,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    have hpos := hpp.factorization_pos_of_dvd hm hpm
    refine ⟨hpp, ?_, ⟨m.factorization p, by omega⟩, by omega⟩
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr (odd_eulerIndex h hq hN1 hqm)) (even_iff_two_dvd.mpr hpJ)
  obtain ⟨ht, ht2, hte, ht0⟩ := hfacts t (by simp)
  obtain ⟨hu, hu2, -, hu0⟩ := hfacts u (by simp)
  obtain ⟨-, hf1, hord, hmod⟩ := sigma_prime_pow_eq_prime_pow_row hu hu2 ht ht2 hu0 hB
  have he2 : 2 ≤ N.factorization t := by obtain ⟨c, hc⟩ := hte; omega
  exact ⟨t, u, htu, hne, ⟨v, hA⟩, ⟨j, hj, hB⟩, h3, h4, hf1, hord, hmod,
    (succ_prime_or_prime_sq_of_sigma_eq_mul_prime_pow ht (by have := ht.two_le; omega) hte he2
      hq hu hA).1⟩

end OddPerfect

#print axioms OddPerfect.sigma_prime_pow_eq_prime_pow_row
#print axioms OddPerfect.succ_prime_or_prime_sq_of_sigma_eq_mul_prime_pow
#print axioms OddPerfect.eulerIndex_pair_rows
