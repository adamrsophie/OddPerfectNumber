import OddPerfect.AttackPrimality
import OddPerfect.AttackSize
import OddPerfect.SmallestPrime

/-!
# Orders modulo a safe prime in the rows `σ(p ^ a)`, and size from excluded small primes

For primes `p` and `t` with `t ∣ σ(p ^ a)`, the order `d` of `p` modulo `t` exceeds `1` and
divides both `a + 1` and `t - 1`, unless `p ≡ 1 (mod t)`, in which case `t ∣ a + 1`. This is
`prime_dvd_sigma_prime_pow` (`OddPerfect/Cyclotomic.lean`); `dvd_succ_of_mod_eq_one` below
only isolates the second case. Fermat receivers are `eq_one_of_fermat_receiver`
(`OddPerfect/AttackPrimality.lean`); `fermat_row` restates it with `p % r = 1` and without
the hypothesis `p ≠ r`.

* `safe_prime_row_cases`: for a safe prime `t = 2 s + 1` (with `s` prime) the order is one of
  `1`, `2`, `s`, `2 s`; order `2` means `t ∣ p + 1`.
* `safe_prime_row_of_even`: for even `a`, `s ∣ a + 1` or `t ∣ a + 1`, so `s ≤ a + 1`.
* `exists_safe_prime_row`, `exists_pow_dvd_of_safe_prime`: if a safe prime `t = 2 s + 1`
  divides an odd perfect number `N`, some prime factor `p ≠ t` has `s ≤ v_p(N) + 1` and
  `p ^ (s - 1) ∣ N`, or `p` is the special prime (odd exponent) and `t ∣ p + 1`.
* `size_of_forall_lt`: if every prime factor of `N` exceeds `L`, then
  `(L + 1) ^ (2 ω + 1) ≤ N` (`pow_two_mul_card_add_one_le`), `3 (L + 1) < 2 ω + 6`
  (`three_mul_minFac_lt`) and hence `(L + 1) ^ (3 L - 1) ≤ N`. The bound
  `2 L ^ ω < (L + 1) ^ ω` from the abundancy is weaker than `three_mul_minFac_lt` and is not
  restated.

All of this is elementary and standard (orders modulo a prime; their use for odd perfect
numbers goes back to the factor chain literature). No novelty is claimed.
-/

namespace OddPerfect

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Companion of `prime_dvd_sigma_prime_pow`: if `p ≡ 1 (mod t)` and `t ∣ σ(p ^ a)` for
primes `p` and `t`, then `t ∣ a + 1`. -/
theorem dvd_succ_of_mod_eq_one {p t a : ℕ} (hp : p.Prime) (ht : t.Prime) (hpt : p % t = 1)
    (hd : t ∣ σ 1 (p ^ a)) : t ∣ a + 1 := by
  rcases (prime_dvd_sigma_prime_pow hp ht hd).2 with h | ⟨h1, -, -⟩
  · exact h.2
  · have h' : (p : ZMod t) = 1 := by rw [← ZMod.natCast_mod, hpt, Nat.cast_one]
    rw [orderOf_eq_one_iff.mpr h'] at h1
    exact absurd h1 (lt_irrefl 1)

/-- The divisors of `2 s` for a prime `s`. -/
private theorem eq_of_dvd_two_mul {s d : ℕ} (hs : s.Prime) (hd : d ∣ 2 * s) :
    d = 1 ∨ d = 2 ∨ d = s ∨ d = 2 * s := by
  obtain ⟨d1, d2, h1, h2, rfl⟩ := Nat.dvd_mul.mp hd
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with rfl | rfl <;>
    rcases (Nat.dvd_prime hs).mp h2 with rfl | rfl <;> omega

/-- Rows at a safe prime. Let `t = 2 s + 1` with `s` and `t` prime, `p` a prime and
`t ∣ σ(p ^ a)`. Then `p ≡ 1 (mod t)` and `t ∣ a + 1`, or the order of `p` modulo `t` is `2`
(and then `t ∣ p + 1` and `a` is odd), `s` or `2 s`, dividing `a + 1`. -/
theorem safe_prime_row_cases {p s t a : ℕ} (hp : p.Prime) (hs : s.Prime) (ht : t.Prime)
    (hts : t = 2 * s + 1) (hd : t ∣ σ 1 (p ^ a)) :
    (p % t = 1 ∧ t ∣ a + 1) ∨
      (orderOf (p : ZMod t) = 2 ∧ t ∣ p + 1 ∧ 2 ∣ a + 1) ∨
      (orderOf (p : ZMod t) = s ∧ s ∣ a + 1) ∨
      (orderOf (p : ZMod t) = 2 * s ∧ 2 * s ∣ a + 1) := by
  have : Fact t.Prime := ⟨ht⟩
  rcases (prime_dvd_sigma_prime_pow hp ht hd).2 with h1 | ⟨h1, hda, hdt⟩
  · exact Or.inl h1
  right
  have hdt' : orderOf (p : ZMod t) ∣ 2 * s := by rwa [show t - 1 = 2 * s by omega] at hdt
  rcases eq_of_dvd_two_mul hs hdt' with h | h | h | h
  · omega
  · refine Or.inl ⟨h, ?_, by rwa [h] at hda⟩
    have hp1 : (p : ZMod t) ≠ 1 := fun h' => absurd (orderOf_eq_one_iff.mpr h') (by omega)
    have hsq : (p : ZMod t) * (p : ZMod t) = 1 := by
      rw [← sq, ← h]
      exact pow_orderOf_eq_one _
    rcases mul_self_eq_one_iff.mp hsq with h' | h'
    · exact absurd h' hp1
    · rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [h', neg_add_cancel]
  · exact Or.inr (Or.inl ⟨h, by rwa [h] at hda⟩)
  · exact Or.inr (Or.inr ⟨h, by rwa [h] at hda⟩)

/-- Even exponent at a safe prime. If `t = 2 s + 1` with `s` and `t` prime, `p` is a prime,
`a` is even and `t ∣ σ(p ^ a)`, then `s ∣ a + 1` or `t ∣ a + 1`. -/
theorem safe_prime_row_of_even {p s t a : ℕ} (hp : p.Prime) (hs : s.Prime) (ht : t.Prime)
    (hts : t = 2 * s + 1) (ha : Even a) (hd : t ∣ σ 1 (p ^ a)) :
    s ∣ a + 1 ∨ t ∣ a + 1 := by
  have hodd : Odd (a + 1) := ha.add_one
  rcases safe_prime_row_cases hp hs ht hts hd with h | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inr h.2
  · exact absurd (hodd.of_dvd_nat h) (Nat.not_odd_iff_even.mpr even_two)
  · exact Or.inl h
  · exact absurd (hodd.of_dvd_nat h) (Nat.not_odd_iff_even.mpr (even_two_mul s))

/-- Even exponent at a safe prime, size form: `s ≤ a + 1`. -/
theorem le_succ_of_safe_prime_row {p s t a : ℕ} (hp : p.Prime) (hs : s.Prime) (ht : t.Prime)
    (hts : t = 2 * s + 1) (ha : Even a) (hd : t ∣ σ 1 (p ^ a)) : s ≤ a + 1 := by
  rcases safe_prime_row_of_even hp hs ht hts ha hd with h | h
  · exact Nat.le_of_dvd (Nat.succ_pos _) h
  · have := Nat.le_of_dvd (Nat.succ_pos _) h
    omega

/-- Fermat rows. If `r = 2 ^ k + 1` is prime, `p` is a prime, `e` is even and
`r ∣ σ(p ^ e)`, then `p ≡ 1 (mod r)` and `r ∣ e + 1`. A restatement of
`eq_one_of_fermat_receiver`, which also needs `p ≠ r`; here that follows from
`prime_dvd_sigma_prime_pow`. -/
theorem fermat_row {p r e k : ℕ} (hp : p.Prime) (hr : r.Prime) (hrk : r = 2 ^ k + 1)
    (he : Even e) (hd : r ∣ σ 1 (p ^ e)) : p % r = 1 ∧ r ∣ e + 1 := by
  have hpr : p ≠ r := fun h => (prime_dvd_sigma_prime_pow hp hr hd).1 h.symm
  have hrj : r - 1 = 2 ^ k := by rw [hrk, Nat.add_sub_cancel]
  obtain ⟨h1, h2⟩ := eq_one_of_fermat_receiver hp hr hrj hpr he hd
  refine ⟨?_, h2⟩
  rcases (prime_dvd_sigma_prime_pow hp hr hd).2 with h | ⟨h3, -, -⟩
  · exact h.1
  · rw [orderOf_eq_one_iff.mpr h1] at h3
    exact absurd h3 (lt_irrefl 1)

variable {N : ℕ}

/-- A safe prime factor of an odd perfect number. Let `t = 2 s + 1 ∣ N` with `s` and `t`
prime. Some prime factor `p ≠ t` has `t ∣ σ(p ^ v_p(N))`, and either `s ∣ v_p(N) + 1` or
`t ∣ v_p(N) + 1`, or `v_p(N)` is odd (so `p` is the special prime), `p` has order `2` modulo
`t` and `t ∣ p + 1`. -/
theorem exists_safe_prime_row (h : OddPerfect N) {s t : ℕ} (hs : s.Prime) (ht : t.Prime)
    (hts : t = 2 * s + 1) (htN : t ∣ N) :
    ∃ p ∈ N.primeFactors, p ≠ t ∧ t ∣ σ 1 (p ^ N.factorization p) ∧
      ((s ∣ N.factorization p + 1 ∨ t ∣ N.factorization p + 1) ∨
        (Odd (N.factorization p) ∧ orderOf (p : ZMod t) = 2 ∧ t ∣ p + 1)) := by
  have htm : t ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨ht, htN, h.ne_zero⟩
  have := hs.two_le
  obtain ⟨p, hpt, hp, -, hd⟩ := exists_sigmaEdge_into h.perfect htm (by omega)
  refine ⟨p, hp, hpt, hd, ?_⟩
  have hpp := Nat.prime_of_mem_primeFactors hp
  rcases Nat.even_or_odd (N.factorization p) with he | he
  · exact Or.inl (safe_prime_row_of_even hpp hs ht hts he hd)
  · rcases safe_prime_row_cases hpp hs ht hts hd with h1 | ⟨h1, h2, -⟩ | ⟨-, h1⟩ | ⟨-, h1⟩
    · exact Or.inl (Or.inr h1.2)
    · exact Or.inr ⟨he, h1, h2⟩
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inl ((dvd_mul_left s 2).trans h1))

/-- Size form of `exists_safe_prime_row`: some prime factor `p ≠ t` of `N` has
`s ≤ v_p(N) + 1` and `p ^ (s - 1) ∣ N`, or has odd exponent (the special prime) and
`t ∣ p + 1`. -/
theorem exists_pow_dvd_of_safe_prime (h : OddPerfect N) {s t : ℕ} (hs : s.Prime)
    (ht : t.Prime) (hts : t = 2 * s + 1) (htN : t ∣ N) :
    ∃ p ∈ N.primeFactors, p ≠ t ∧
      ((s ≤ N.factorization p + 1 ∧ p ^ (s - 1) ∣ N) ∨
        (Odd (N.factorization p) ∧ t ∣ p + 1)) := by
  obtain ⟨p, hp, hpt, -, hc⟩ := exists_safe_prime_row h hs ht hts htN
  refine ⟨p, hp, hpt, ?_⟩
  rcases hc with hc | ⟨he, -, h2⟩
  · have hle : s ≤ N.factorization p + 1 := by
      rcases hc with hc | hc
      · exact Nat.le_of_dvd (Nat.succ_pos _) hc
      · have := Nat.le_of_dvd (Nat.succ_pos _) hc
        omega
    exact Or.inl ⟨hle, (pow_dvd_pow p (by omega)).trans (Nat.ordProj_dvd N p)⟩
  · exact Or.inr ⟨he, h2⟩

/-- If every prime factor of an odd perfect number `N` exceeds `L ≥ 1`, then
`L ^ (2 ω - 1) < N` with `ω` the number of prime factors. A weak form of
`pow_two_mul_card_add_one_le`. -/
theorem pow_lt_of_forall_lt (h : OddPerfect N) {L : ℕ} (hL : 1 ≤ L)
    (hp : ∀ p ∈ N.primeFactors, L < p) : L ^ (2 * N.primeFactors.card - 1) < N := by
  have h1 := pow_two_mul_card_add_one_le h (p := L + 1) fun r hr => Nat.succ_le_of_lt (hp r hr)
  calc L ^ (2 * N.primeFactors.card - 1) ≤ L ^ (2 * N.primeFactors.card + 1) :=
        Nat.pow_le_pow_right hL (by omega)
    _ < (L + 1) ^ (2 * N.primeFactors.card + 1) := Nat.pow_lt_pow_left (by omega) (by omega)
    _ ≤ N := h1

/-- Size from excluded small primes. If every prime factor of an odd perfect number `N`
exceeds `L`, then `(L + 1) ^ (2 ω + 1) ≤ N`, `3 (L + 1) < 2 ω + 6`, and so
`(L + 1) ^ (3 L - 1) ≤ N`. -/
theorem size_of_forall_lt (h : OddPerfect N) {L : ℕ} (hp : ∀ p ∈ N.primeFactors, L < p) :
    (L + 1) ^ (2 * N.primeFactors.card + 1) ≤ N ∧
      3 * (L + 1) < 2 * N.primeFactors.card + 6 ∧ (L + 1) ^ (3 * L - 1) ≤ N := by
  have h1 := pow_two_mul_card_add_one_le h (p := L + 1) fun r hr => Nat.succ_le_of_lt (hp r hr)
  have hN1 : N ≠ 1 := by
    rintro rfl
    have := h.sigma_eq
    simp at this
  have hm : N.minFac ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime hN1, Nat.minFac_dvd N, h.ne_zero⟩
  have h2 := three_mul_minFac_lt h
  have hLm := hp _ hm
  have h3 : 3 * (L + 1) < 2 * N.primeFactors.card + 6 := by omega
  exact ⟨h1, h3, (Nat.pow_le_pow_right (by omega) (by omega)).trans h1⟩

/-- The instance `L = 1000`: if every prime factor of an odd perfect number `N` exceeds
`1000`, then `N` has at least `1499` prime factors and `1001 ^ 2999 ≤ N`. -/
theorem size_of_forall_gt_thousand (h : OddPerfect N) (hp : ∀ p ∈ N.primeFactors, 1000 < p) :
    1499 ≤ N.primeFactors.card ∧ 1001 ^ 2999 ≤ N := by
  obtain ⟨-, h2, h3⟩ := size_of_forall_lt h hp
  rw [show (1000 : ℕ) + 1 = 1001 from rfl, show 3 * 1000 - 1 = 2999 from rfl] at h3
  exact ⟨by omega, h3⟩

end OddPerfect

#print axioms OddPerfect.dvd_succ_of_mod_eq_one
#print axioms OddPerfect.safe_prime_row_cases
#print axioms OddPerfect.safe_prime_row_of_even
#print axioms OddPerfect.le_succ_of_safe_prime_row
#print axioms OddPerfect.fermat_row
#print axioms OddPerfect.exists_safe_prime_row
#print axioms OddPerfect.exists_pow_dvd_of_safe_prime
#print axioms OddPerfect.pow_lt_of_forall_lt
#print axioms OddPerfect.size_of_forall_lt
#print axioms OddPerfect.size_of_forall_gt_thousand
