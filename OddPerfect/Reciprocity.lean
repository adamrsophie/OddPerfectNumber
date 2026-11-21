import OddPerfect.Network
import OddPerfect.Valuation
import OddPerfect.Cyclotomic
import OddPerfect.SpecialPrime
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Quadratic residue constraints on the divisor sum network

Following Wallace (arXiv 1610.00544). For a prime `p` and any `a`, `σ(p ^ a) ≡ 1 (mod p)`,
so the Legendre symbol of `σ(p ^ a)` modulo `p` is `1`. Expanding over the factorization of
the component divisor sum gives one sign identity per vertex of the network:

* a non-special vertex `p`: `∏ r, (r / p) ^ w(p, r) = 1`;
* the special vertex `q`: the same product is `(2 / q)`, so it is `1` for `q ≡ 1 (mod 8)` and
  `-1` for `q ≡ 5 (mod 8)` (Wallace, Theorem 1, proved here in its exact parity form).

There is also a constraint in the other direction of each edge, which is not in the paper:
if `e` is even and `r ∣ σ(p ^ e)` then `p ^ (e + 1) ≡ 1 (mod r)`, so
`p ≡ (p ^ (e / 2 + 1)) ^ 2` is a nonzero square modulo `r`. Applied to an edge into the
special prime `q ≡ 1 (mod 4)` and combined with reciprocity, it shows that every odd perfect
number has two distinct prime factors that are nonzero squares modulo each other. This
implies Wallace's Theorem 2 without its hypothesis `q ≡ 1 (mod 8)`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## Component identities -/

/-- The divisor sum of a prime power is `1` modulo the prime. -/
theorem sigma_prime_pow_cast_self {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ((σ 1 (p ^ a) : ℕ) : ZMod p) = 1 := by
  rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ', pow_zero]
  push_cast
  simp

/-- `σ(p ^ a) % p = 1` for a prime `p`. -/
theorem sigma_prime_pow_mod_self {p : ℕ} (hp : p.Prime) (a : ℕ) : σ 1 (p ^ a) % p = 1 := by
  have h := (ZMod.natCast_eq_natCast_iff' (σ 1 (p ^ a)) 1 p).mp
    (by rw [Nat.cast_one]; exact sigma_prime_pow_cast_self hp a)
  rw [h, Nat.mod_eq_of_lt hp.one_lt]

/-- The divisor sum of a prime power is a quadratic residue modulo the prime. -/
theorem legendreSym_sigma_prime_pow (p : ℕ) [Fact p.Prime] (a : ℕ) :
    legendreSym p (σ 1 (p ^ a)) = 1 := by
  rw [legendreSym, Int.cast_natCast, sigma_prime_pow_cast_self Fact.out, map_one]

/-- The Legendre symbol of a positive integer expands over its factorization. -/
theorem legendreSym_eq_prod_factorization (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    legendreSym p n = ∏ r ∈ n.primeFactors, legendreSym p r ^ n.factorization r := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization]
  push_cast
  exact (map_prod (legendreSym.hom p) (fun r : ℕ => (r : ℤ) ^ n.factorization r)
    n.primeFactors).trans (Finset.prod_congr rfl fun r _ => map_pow (legendreSym.hom p) _ _)

/-- Reverse edge constraint. If `e` is even and the prime `r` divides `σ(p ^ e)`, then `p` is
a quadratic residue modulo `r`: `p ^ (e + 1) ≡ 1 (mod r)` and `e + 1` is odd. -/
theorem legendreSym_eq_one_of_dvd_sigma_even {p r e : ℕ} [Fact r.Prime] (hp : p.Prime)
    (he : Even e) (hr : r ∣ σ 1 (p ^ e)) : legendreSym r p = 1 := by
  set x : ZMod r := (p : ZMod r) with hxdef
  have h0 : ∑ i ∈ Finset.range (e + 1), x ^ i = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ r).mpr hr
    rw [sigma_one_apply_prime_pow hp] at this
    push_cast at this
    exact this
  have h1 : x ^ (e + 1) = 1 := by
    have := geom_sum_mul x (e + 1)
    rw [h0, zero_mul] at this
    exact (sub_eq_zero.mp this.symm)
  have hx0 : x ≠ 0 := by
    rintro hx
    rw [hx, zero_pow (Nat.succ_ne_zero e)] at h1
    exact zero_ne_one h1
  obtain ⟨b, rfl⟩ := he
  have hsq : x = (x ^ (b + 1)) ^ 2 := by
    rw [← pow_mul, show (b + 1) * 2 = (b + b + 1) + 1 by ring, pow_succ, h1, one_mul]
  rw [legendreSym, Int.cast_natCast]
  change quadraticChar (ZMod r) x = 1
  rw [hsq]
  exact quadraticChar_sq_one' (pow_ne_zero _ hx0)

/-- With reciprocity, the reverse edge constraint fixes the symbol on the edge: if `e` is even
and the odd prime `r` divides `σ(p ^ e)` for an odd prime `p`, then `(r / p) = -1` exactly when
`p ≡ r ≡ 3 (mod 4)`, and `(r / p) = 1` otherwise. -/
theorem legendreSym_receiver_of_dvd_sigma_even {p r e : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hp2 : p ≠ 2) (hr2 : r ≠ 2) (he : Even e) (hr : r ∣ σ 1 (p ^ e)) :
    legendreSym p r = if p % 4 = 3 ∧ r % 4 = 3 then -1 else 1 := by
  have hp : p.Prime := Fact.out
  have hr' : r.Prime := Fact.out
  rw [legendreSym.quadratic_reciprocity' hr2 hp2,
    legendreSym_eq_one_of_dvd_sigma_even hp he hr, mul_one, pow_mul]
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by
    have := Nat.odd_iff.mp (hp.odd_of_ne_two hp2); omega
  have hr4 : r % 4 = 1 ∨ r % 4 = 3 := by
    have := Nat.odd_iff.mp (hr'.odd_of_ne_two hr2); omega
  rcases hp4 with h4 | h4 <;> rcases hr4 with h4' | h4' <;>
    simp [h4, h4', ZMod.neg_one_pow_div_two_of_one_mod_four,
      ZMod.neg_one_pow_div_two_of_three_mod_four]

/-! ## The vertex identities in an odd perfect number -/

private theorem primeFactors_sigma_subset {N p : ℕ} (h : OddPerfect N)
    (hp : p ∈ N.primeFactors) :
    (σ 1 (p ^ N.factorization p)).primeFactors ⊆ insert 2 N.primeFactors := by
  intro r hr
  rcases eq_or_ne r 2 with rfl | hr2
  · exact Finset.mem_insert_self _ _
  · refine Finset.mem_insert_of_mem (mem_primeFactors_of_sigmaWeight_ne_zero h.perfect hp hr2 ?_)
    rw [sigmaWeight, ← Finsupp.mem_support_iff, Nat.support_factorization]
    exact hr

/-- The basic vertex identity in an odd perfect number: for every prime factor `p`,
`(2 / p) ^ w(p, 2) * ∏ r ∈ N.primeFactors, (r / p) ^ w(p, r) = 1`, where
`w(p, r) = sigmaWeight N p r` is the exponent of `r` in `σ(p ^ v_p(N))`. -/
theorem legendreSym_two_pow_mul_prod_sigmaWeight {N p : ℕ} [Fact p.Prime] (h : OddPerfect N)
    (hp : p ∈ N.primeFactors) :
    legendreSym p 2 ^ sigmaWeight N p 2 *
      ∏ r ∈ N.primeFactors, legendreSym p r ^ sigmaWeight N p r = 1 := by
  have hs0 : σ 1 (p ^ N.factorization p) ≠ 0 :=
    (sigma_pos 1 _ (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)).ne'
  have h2 : 2 ∉ N.primeFactors := fun h2 => h.not_two_dvd (Nat.dvd_of_mem_primeFactors h2)
  have key := legendreSym_sigma_prime_pow p (N.factorization p)
  rw [legendreSym_eq_prod_factorization p hs0,
    Finset.prod_subset (primeFactors_sigma_subset h hp), Finset.prod_insert h2] at key
  · exact key
  · intro r _ hr
    rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hr
    rw [hr, pow_zero]

private theorem sigmaWeight_two_of_even {N p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : Even (N.factorization p)) : sigmaWeight N p 2 = 0 := by
  rw [sigmaWeight_eq_padicValNat N p Nat.prime_two, padicValNat_two_sigma_prime_pow hp hp2,
    if_pos he]

private theorem ne_two_of_mem {N p : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors) :
    p ≠ 2 := by
  rintro rfl
  exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hp)

/-- Non-special vertex (Wallace, Proposition 1): if `v_p(N)` is even then
`∏ r ∈ N.primeFactors, (r / p) ^ w(p, r) = 1`. -/
theorem prod_legendreSym_sigmaWeight_of_even {N p : ℕ} [Fact p.Prime] (h : OddPerfect N)
    (hp : p ∈ N.primeFactors) (he : Even (N.factorization p)) :
    ∏ r ∈ N.primeFactors, legendreSym p r ^ sigmaWeight N p r = 1 := by
  have := legendreSym_two_pow_mul_prod_sigmaWeight h hp
  rwa [sigmaWeight_two_of_even Fact.out (ne_two_of_mem h hp) he, pow_zero, one_mul] at this

/-- The special component carries exactly one factor `2`. -/
theorem sigmaWeight_special_two {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hqN : q ∈ N.primeFactors) (hodd : Odd (N.factorization q)) : sigmaWeight N q 2 = 1 := by
  have hs := sigmaWeight_sum_two h
  rwa [Finset.sum_eq_single_of_mem q hqN fun b hb hbq =>
    sigmaWeight_two_of_even (Nat.prime_of_mem_primeFactors hb) (ne_two_of_mem h hb)
      (even_factorization_of_ne h hq hodd (Nat.prime_of_mem_primeFactors hb) hbq)] at hs

/-- Special vertex: if `q` is the special prime, then
`∏ r ∈ N.primeFactors, (r / q) ^ w(q, r)` is `1` when `q ≡ 1 (mod 8)` and `-1` otherwise
(the only other case being `q ≡ 5 (mod 8)`). -/
theorem prod_legendreSym_sigmaWeight_special {N q : ℕ} [Fact q.Prime] (h : OddPerfect N)
    (hqN : q ∈ N.primeFactors) (hodd : Odd (N.factorization q)) :
    ∏ r ∈ N.primeFactors, legendreSym q r ^ sigmaWeight N q r =
      if q % 8 = 1 then 1 else -1 := by
  have hq : q.Prime := Fact.out
  have key := legendreSym_two_pow_mul_prod_sigmaWeight h hqN
  have h4 := (special_mod_four h hq hodd).1
  rw [sigmaWeight_special_two h hq hqN hodd, pow_one,
    legendreSym.at_two (ne_two_of_mem h hqN), ZMod.χ₈_nat_eq_if_mod_eight] at key
  have h8 : q % 8 = 1 ∨ q % 8 = 5 := by omega
  rcases h8 with h8 | h8
  · simpa [h8, show q % 2 = 1 by omega] using key
  · have h' : ¬ q % 8 = 1 := by omega
    simp only [show ¬ q % 2 = 0 by omega, h8, if_false] at key
    simp only [h', if_false]
    norm_num at key
    linarith

/-- A product of signs counts the odd exponent sign changes. -/
theorem prod_pow_eq_neg_one_pow_card (S : Finset ℕ) (f : ℕ → ℤ) (w : ℕ → ℕ)
    (hf : ∀ r ∈ S, w r ≠ 0 → f r = 1 ∨ f r = -1) :
    ∏ r ∈ S, f r ^ w r = (-1) ^ (S.filter fun r => Odd (w r) ∧ f r = -1).card := by
  rw [← Finset.prod_const, Finset.prod_filter]
  refine Finset.prod_congr rfl fun r hr => ?_
  by_cases hw : w r = 0
  · simp [hw]
  · rcases hf r hr hw with h1 | h1
    · simp [h1]
    · rcases Nat.even_or_odd (w r) with he | ho
      · simp [h1, he.neg_one_pow, Nat.not_odd_iff_even.mpr he]
      · simp [h1, ho.neg_one_pow, ho]

/-- Wallace, Theorem 1 (exact form). If the special prime `q` is `≡ 5 (mod 8)`, then an odd
number of the prime factors `r` of `N` that occur to an odd power in `σ(q ^ v_q(N))` are
quadratic non-residues modulo `q`. -/
theorem odd_card_nonresidue_of_special_mod_eight_eq_five {N q : ℕ} [Fact q.Prime]
    (h : OddPerfect N) (hqN : q ∈ N.primeFactors) (hodd : Odd (N.factorization q))
    (h8 : q % 8 = 5) :
    Odd (N.primeFactors.filter fun r => Odd (sigmaWeight N q r) ∧ legendreSym q r = -1).card := by
  have hq : q.Prime := Fact.out
  have hprod := prod_legendreSym_sigmaWeight_special h hqN hodd
  rw [if_neg (by omega), prod_pow_eq_neg_one_pow_card] at hprod
  · rcases Nat.even_or_odd (N.primeFactors.filter
        fun r => Odd (sigmaWeight N q r) ∧ legendreSym q r = -1).card with he | ho
    · rw [he.neg_one_pow] at hprod; norm_num at hprod
    · exact ho
  · intro r hr hw
    have hrq : r ≠ q := by rintro rfl; exact hw (sigmaWeight_self hq)
    apply legendreSym.eq_one_or_neg_one
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    exact hrq ((Nat.prime_dvd_prime_iff_eq hq (Nat.prime_of_mem_primeFactors hr)).mp hd).symm

/-! ## Mutual residues: Wallace's Theorem 2 without the hypothesis `q ≡ 1 (mod 8)` -/

/-- Every odd perfect number has two distinct prime factors `p` and `r` with `p` a nonzero
square modulo `r` and `r` a nonzero square modulo `p`. One can take `r` to be the special prime
and `p` any prime factor whose component divisor sum is divisible by `r`. -/
theorem exists_mutual_quadratic_residues {N : ℕ} (h : OddPerfect N) :
    ∃ p ∈ N.primeFactors, ∃ r ∈ N.primeFactors, p ≠ r ∧
      jacobiSym p r = 1 ∧ jacobiSym r p = 1 := by
  obtain ⟨q, hq, hqN, hq4, hk, hev⟩ := exists_special_prime h
  have hqm : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqN, h.ne_zero⟩
  have hsum := sigmaWeight_sum_eq h.perfect hq (ne_two_of_mem h hqm)
  obtain ⟨p, hp, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := N.primeFactors)
    (f := fun p => sigmaWeight N p q) (by rw [hsum]; omega)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpq : p ≠ q := by rintro rfl; exact hw (sigmaWeight_self hq)
  have : Fact q.Prime := ⟨hq⟩
  have : Fact p.Prime := ⟨hpp⟩
  have h1 : legendreSym q p = 1 :=
    legendreSym_eq_one_of_dvd_sigma_even hpp (hev p hpp hpq) (Nat.dvd_of_factorization_pos hw)
  have h2 : legendreSym p q = 1 := by
    rw [legendreSym.quadratic_reciprocity_one_mod_four hq4 (ne_two_of_mem h hp)]; exact h1
  refine ⟨p, hp, q, hqm, hpq, ?_, ?_⟩
  · rw [← jacobiSym.legendreSym.to_jacobiSym]; exact h1
  · rw [← jacobiSym.legendreSym.to_jacobiSym]; exact h2

/-- Wallace, Theorem 2, for every odd perfect number (the paper assumes `q ≡ 1 (mod 8)`):
it is impossible that every prime factor is a quadratic non-residue modulo every other one. -/
theorem not_forall_jacobiSym_eq_neg_one {N : ℕ} (h : OddPerfect N) :
    ¬ ∀ p ∈ N.primeFactors, ∀ r ∈ N.primeFactors, p ≠ r → jacobiSym p r = -1 := by
  intro hall
  obtain ⟨p, hp, r, hr, hpr, h1, -⟩ := exists_mutual_quadratic_residues h
  rw [hall p hp r hr hpr] at h1
  norm_num at h1

/-! ## Euler form -/

/-- In Euler's form `N = q ^ k * m ^ 2`, every odd prime dividing `σ(q ^ k)` divides `m`. -/
theorem prime_dvd_of_dvd_sigma_special {N q k m p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ σ 1 (q ^ k)) : p ∣ m := by
  have h2m := hd.trans (sigma_special_dvd h hq hN hqm)
  have hcop : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  exact hp.dvd_of_dvd_pow (hcop.dvd_of_dvd_mul_left h2m)

end OddPerfect

#print axioms OddPerfect.sigma_prime_pow_cast_self
#print axioms OddPerfect.sigma_prime_pow_mod_self
#print axioms OddPerfect.legendreSym_sigma_prime_pow
#print axioms OddPerfect.legendreSym_eq_prod_factorization
#print axioms OddPerfect.legendreSym_eq_one_of_dvd_sigma_even
#print axioms OddPerfect.legendreSym_receiver_of_dvd_sigma_even
#print axioms OddPerfect.legendreSym_two_pow_mul_prod_sigmaWeight
#print axioms OddPerfect.prod_legendreSym_sigmaWeight_of_even
#print axioms OddPerfect.sigmaWeight_special_two
#print axioms OddPerfect.prod_legendreSym_sigmaWeight_special
#print axioms OddPerfect.prod_pow_eq_neg_one_pow_card
#print axioms OddPerfect.odd_card_nonresidue_of_special_mod_eight_eq_five
#print axioms OddPerfect.exists_mutual_quadratic_residues
#print axioms OddPerfect.not_forall_jacobiSym_eq_neg_one
#print axioms OddPerfect.prime_dvd_of_dvd_sigma_special
