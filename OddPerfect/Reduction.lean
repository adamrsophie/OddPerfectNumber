import OddPerfect.Euler
import OddPerfect.Abundancy
import OddPerfect.Network

/-!
# The odd perfect number problem as a finite network problem

A `Candidate` is a finitely supported exponent function `p ↦ e_p`. It is `Balanced` when
the local conservation laws of the divisor sum network hold exactly. We prove that the
balanced candidates are exactly the factorizations of odd perfect numbers, so
`OddPerfectConjecture` is equivalent to the nonexistence of a balanced candidate.

This equivalence is a reformulation, not progress toward a proof. The open problem is
exactly whether a balanced candidate exists; nothing here decides that, and nothing here
assumes the conjecture. We also collect, in `Candidate.Necessary`, every necessary
condition proved in this project, transported to the language of candidates.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- Finite data of a candidate: a finitely supported exponent function. Its support is
the set of primes, and every prime in the support has positive exponent by definition of
the support. -/
structure Candidate where
  exponent : ℕ →₀ ℕ

namespace Candidate

/-- The set of primes of the candidate: the support of the exponent function. -/
def support (C : Candidate) : Finset ℕ := C.exponent.support

/-- The number `∏ p ∈ support, p ^ exponent p`. -/
def value (C : Candidate) : ℕ := C.exponent.prod (· ^ ·)

/-- Weight of the edge `p → q`: exponent of `q` in `σ(p ^ exponent p)`. -/
def weight (C : Candidate) (p q : ℕ) : ℕ := (σ 1 (p ^ C.exponent p)).factorization q

/-- The exact local conditions: every element of the support is an odd prime (with
positive exponent, automatic for a support), the weights into every odd prime `q` add up
to `exponent q` (so zero when `q` is outside the support), and
the weights into 2 add up to exactly one. -/
structure Balanced (C : Candidate) : Prop where
  /-- Every element of the support is prime. -/
  prime : ∀ p ∈ C.support, p.Prime
  /-- No element of the support is 2. -/
  ne_two : ∀ p ∈ C.support, p ≠ 2
  /-- Conservation at every odd prime. -/
  balance_odd : ∀ q : ℕ, q.Prime → q ≠ 2 → ∑ p ∈ C.support, C.weight p q = C.exponent q
  /-- The weights into 2 add up to exactly one. -/
  balance_two : ∑ p ∈ C.support, C.weight p 2 = 1

variable {C : Candidate}

/-- The factorization of the value of a balanced candidate is its exponent function. -/
theorem Balanced.factorization_value (hC : C.Balanced) : C.value.factorization = C.exponent :=
  Nat.prod_pow_factorization_eq_self hC.prime

/-- The value of a balanced candidate is nonzero. -/
theorem Balanced.value_ne_zero (hC : C.Balanced) : C.value ≠ 0 := by
  unfold value Finsupp.prod
  exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hC.prime p hp).ne_zero

/-- The prime factors of the value of a balanced candidate form its support. -/
theorem Balanced.primeFactors_value (hC : C.Balanced) : C.value.primeFactors = C.support := by
  rw [← Nat.support_factorization, hC.factorization_value]; rfl

/-- Candidate weights agree with the network weights `sigmaWeight` of the value. -/
theorem Balanced.weight_eq (hC : C.Balanced) (p q : ℕ) :
    C.weight p q = sigmaWeight C.value p q := by
  simp [weight, sigmaWeight, hC.factorization_value]

/-- A balanced candidate gives an odd perfect number. -/
theorem Balanced.oddPerfect (hC : C.Balanced) : OddPerfect C.value := by
  have h0 := hC.value_ne_zero
  have hf := hC.factorization_value
  have h2 : C.exponent 2 = 0 :=
    Finsupp.notMem_support_iff.mp fun h => hC.ne_two 2 h rfl
  have hodd : ¬ 2 ∣ C.value := by
    intro hd
    have := (Nat.prime_two.dvd_iff_one_le_factorization h0).mp hd
    rw [hf, h2] at this
    omega
  refine ⟨Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd), ?_⟩
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul (Nat.pos_of_ne_zero h0), ← sigma_one_apply]
  have hs0 : σ 1 C.value ≠ 0 := (sigma_pos 1 _ h0).ne'
  refine Nat.eq_of_factorization_eq hs0 (by omega) fun q => ?_
  have hsum : (σ 1 C.value).factorization q = ∑ p ∈ C.support, C.weight p q := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ h0,
      Nat.prod_factorization_eq_prod_primeFactors, Nat.factorization_prod_apply, hC.primeFactors_value]
    · simp [weight, hf]
    · intro p hp
      exact (sigma_pos 1 _ (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)).ne'
  rw [hsum, Nat.factorization_mul (by decide) h0, Finsupp.add_apply, hf]
  by_cases hq : q.Prime
  · by_cases hq2 : q = 2
    · subst hq2
      rw [hC.balance_two, Nat.prime_two.factorization_self, h2]
    · rw [hC.balance_odd q hq hq2,
        Nat.factorization_eq_zero_of_not_dvd fun hd => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hd),
        zero_add]
  · have hq0 : C.exponent q = 0 := Finsupp.notMem_support_iff.mp fun h => hq (hC.prime q h)
    rw [hq0, Nat.factorization_eq_zero_of_not_prime _ hq, add_zero]
    refine Finset.sum_eq_zero fun p _ => Nat.factorization_eq_zero_of_not_prime _ hq

end Candidate

/-- An odd perfect number gives a balanced candidate: its own factorization. -/
theorem exists_balanced {N : ℕ} (h : OddPerfect N) :
    ∃ C : Candidate, C.Balanced ∧ C.value = N := by
  refine ⟨⟨N.factorization⟩, ⟨?_, ?_, ?_, ?_⟩, Nat.prod_factorization_pow_eq_self h.ne_zero⟩
  · intro p hp
    exact Nat.prime_of_mem_primeFactors hp
  · rintro p hp rfl
    exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hp)
  · intro q hq hq2
    exact sigmaWeight_sum_eq h.perfect hq hq2
  · exact sigmaWeight_sum_two h

/-- The conjecture is equivalent to the nonexistence of a balanced finite prime network.
This is a reformulation, not progress toward a proof: the open problem is exactly whether
a balanced candidate exists. -/
theorem conjecture_iff_no_balanced : OddPerfectConjecture ↔ ¬ ∃ C : Candidate, C.Balanced := by
  constructor
  · rintro hc ⟨C, hC⟩
    exact hc _ hC.oddPerfect
  · intro hn N hN
    obtain ⟨C, hC, -⟩ := exists_balanced hN
    exact hn ⟨C, hC⟩

namespace Candidate

/-- The edge relation of a candidate: `p → q` between support primes with nonzero weight. -/
def Edge (C : Candidate) (p q : ℕ) : Prop := p ∈ C.support ∧ q ∈ C.support ∧ C.weight p q ≠ 0

/-- All necessary conditions proved in this project for a balanced candidate. These are
consequences of balance, not a solution: no combination of them is known to be
contradictory, and the open problem remains whether a balanced candidate exists. -/
structure Necessary (C : Candidate) : Prop where
  /-- At least three primes (Abundancy). -/
  three_le_card : 3 ≤ C.support.card
  /-- Euler: a special prime `q ≡ 1 (mod 4)` with exponent `≡ 1 (mod 4)`; every other
  exponent is even. -/
  euler : ∃ q ∈ C.support, q % 4 = 1 ∧ C.exponent q % 4 = 1 ∧
    ∀ p, p ≠ q → Even (C.exponent p)
  /-- Exactly one prime has odd exponent. -/
  existsUnique_odd : ∃! q, Odd (C.exponent q)
  /-- Touchard's congruence. -/
  touchard : C.value % 12 = 1 ∨ C.value % 36 = 9
  /-- No self loops. -/
  weight_self : ∀ p, C.weight p p = 0
  /-- Strong connectivity of the edge relation on the support. -/
  connected : ∀ p ∈ C.support, ∀ q ∈ C.support, Relation.ReflTransGen C.Edge p q
  /-- The abundancy of the value is exactly two. -/
  abundancy_eq_two : abundancy C.value = 2
  /-- The support alone has enough room: `2 < ∏ p/(p-1)`. -/
  two_lt_prod : 2 < ∏ p ∈ C.support, ((p : ℚ) / (p - 1))

variable {C : Candidate}

/-- Every necessary condition proved in this project holds for a balanced candidate. Each
is obtained from the corresponding theorem about odd perfect numbers through
`Balanced.oddPerfect`. -/
theorem Balanced.necessary (hC : C.Balanced) : C.Necessary := by
  have h := hC.oddPerfect
  have hf := hC.factorization_value
  have hpf := hC.primeFactors_value
  have hn1 : 1 < C.value := by
    have := h.pos
    rcases Nat.lt_or_ge 1 C.value with h1 | h1
    · exact h1
    · have : C.value = 1 := by omega
      have h3 := three_le_card_primeFactors h
      rw [this] at h3
      simp at h3
  have heuler : ∃ q ∈ C.support, q % 4 = 1 ∧ C.exponent q % 4 = 1 ∧
      ∀ p, p ≠ q → Even (C.exponent p) := by
    obtain ⟨q, hq, hqN, hq4, he, hev⟩ := exists_special_prime h
    rw [hf] at he
    refine ⟨q, hpf ▸ Nat.mem_primeFactors.mpr ⟨hq, hqN, h.ne_zero⟩, hq4, he, fun p hpq => ?_⟩
    by_cases hp : p.Prime
    · simpa [hf] using hev p hp hpq
    · rw [Finsupp.notMem_support_iff.mp fun hm => hp (hC.prime p hm)]
      exact ⟨0, rfl⟩
  refine ⟨?_, heuler, ?_, touchard h, ?_, ?_, ?_, ?_⟩
  · simpa [hpf] using three_le_card_primeFactors h
  · obtain ⟨q, -, -, he, hev⟩ := heuler
    refine ⟨q, Nat.odd_iff.mpr (by omega), fun p hp => ?_⟩
    by_contra hpq
    exact (Nat.not_even_iff_odd.mpr hp) (hev p hpq)
  · intro p
    by_cases hp : p ∈ C.support
    · rw [hC.weight_eq]
      exact sigmaWeight_self (hC.prime p hp)
    · simp [weight, Finsupp.notMem_support_iff.mp hp]
  · intro p hp q hq
    rw [← hpf] at hp hq
    refine Relation.ReflTransGen.mono (fun a b hab => ?_) _ _ (sigmaEdge_reflTransGen h.perfect hp hq)
    have ha := hab.1
    have hb := hab.2.1
    refine ⟨hpf ▸ ha, hpf ▸ hb, ?_⟩
    rw [hC.weight_eq]
    exact (sigmaEdge_iff_sigmaWeight_ne_zero ha hb).mp hab
  · exact (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
  · have := abundancy_lt_prod hn1
    rw [(perfect_iff_abundancy_eq_two h.pos).mp h.perfect, hpf] at this
    exact this

end Candidate

end OddPerfect

#print axioms OddPerfect.Candidate.Balanced.factorization_value
#print axioms OddPerfect.Candidate.Balanced.value_ne_zero
#print axioms OddPerfect.Candidate.Balanced.primeFactors_value
#print axioms OddPerfect.Candidate.Balanced.weight_eq
#print axioms OddPerfect.Candidate.Balanced.oddPerfect
#print axioms OddPerfect.exists_balanced
#print axioms OddPerfect.conjecture_iff_no_balanced
#print axioms OddPerfect.Candidate.Balanced.necessary
