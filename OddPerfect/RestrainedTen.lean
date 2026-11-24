import OddPerfect.RestrainedEight
import OddPerfect.ExcessSupport
import OddPerfect.EscapeRowUnique

/-!
# Restrained odd perfect numbers: counting against the exponent of 3

Setting of `restrained_not_dvd_of_lt`: `N` is an odd perfect number with special prime `q`,
`r ≠ q` is a further prime, and every prime factor other than `q` and `r` has exponent exactly
2. The landed results give `r = 3`, `q ≡ 1 (mod 12)` and `E = v_3(N)` even.

Call the prime factors other than `q` and `3` the ordinary primes; each has exponent 2, so they
all lie in `squarePrimes N q` and `ω(N) ≤ #squarePrimes + 2`.

* `restrained_card_squarePrimes_le`: `#squarePrimes ≤ 2 * #O1 + 1`, where `O1` is the set of
  prime factors of exponent 2 that are 1 modulo 3. The counting lemma `card_squarePrimes_le`
  bounds `#squarePrimes` by the number of escape rows plus the total exponent of the prime
  factors `t ≠ q, 3` with `t ≡ 1 (mod 3)`; in this family each such `t` has exponent 2, and
  there is at most one escape row (`card_escapeRows_le_one_all`).
* `restrained_omega_le`: `ω(N) ≤ 2 * v_3(N) + 3`, since `#O1 ≤ v_3(N)`
  (`card_sq_mod_three_eq_one_le`).
* `restrained_nineteen_thousand_le_three`: `19024 ≤ v_3(N)`, from `ω(N) ≥ 38049` and the
  parity of `v_3(N)`.
* `restrained_Omega_ge_of_nineteen_thousand`: `Ω(N) ≥ 95119`, from
  `2 ω(N) + v_3(N) ≤ Ω(N) + 3`.

Relation to the literature. The relation between the exponent of 3 and `ω(N)` is a counting
argument of the type of a lemma of Ochem and Zelinsky, "On odd perfect numbers with exactly one
even exponent greater than 2" (arXiv 2607.19746, section on the notable prime 3), who state that
the exponent of 3 is at least `ω(N)/2 − 2`, using a theorem of Bugeaud and Mihailescu and a lemma
of Ochem and Rao. Here the library's unconditional single escape row theorem takes the place of
both and gives `ω(N) ≤ 2E + 3`. The same paper states a much larger lower bound for the exponent
of 3, obtained by a long computation, which is not proved here. The theorems of
this file are conditional family results checked by the kernel; no novelty is claimed. The odd
perfect number conjecture is open and nothing here decides it.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.omega ArithmeticFunction.Omega

namespace OddPerfect

open RestrainedSeven

/-- **Restrained family: the square primes against the square primes that are 1 modulo 3.**
`#squarePrimes N q ≤ 2 * #{p ∣ N : v_p(N) = 2, p ≡ 1 (mod 3)} + 1`: every square prime that is
not an escape row sends weight to an ordinary prime `t ≡ 1 (mod 3)`, which has exponent 2 and so
receives weight at most 2, and there is at most one escape row. Proved inside the restrained
family only: in general the receivers may have exponent larger than 2.
Conditional family result; no novelty is claimed. -/
theorem restrained_card_squarePrimes_le {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    (squarePrimes N q).card ≤
      2 * {p ∈ N.primeFactors | N.factorization p = 2 ∧ p % 3 = 1}.card + 1 := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have hgen := card_squarePrimes_le (q := q) h
  have hesc := card_escapeRows_le_one_all h hq hodd
  set R := N.primeFactors.filter (fun t => t ≠ q ∧ t ≠ 3 ∧ t % 3 = 1) with hR
  have hsum : ∑ t ∈ R, N.factorization t = R.card * 2 := by
    refine Finset.sum_const_nat fun t ht => ?_
    obtain ⟨htN, htq, ht3, -⟩ := Finset.mem_filter.mp ht
    exact F.sq t htN htq ht3
  have hsub : R ⊆ {p ∈ N.primeFactors | N.factorization p = 2 ∧ p % 3 = 1} := by
    intro t ht
    obtain ⟨htN, htq, ht3, h1⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨htN, F.sq t htN htq ht3, h1⟩
  have hle := Finset.card_le_card hsub
  omega

/-- **Restrained family: `ω(N) ≤ 2 * v_3(N) + 3`.** The prime factors are `q`, `3` and the
square primes, and `#squarePrimes ≤ 2 * #O1 + 1 ≤ 2 * v_3(N) + 1`. This is counting of the type
of a lemma of Ochem and Zelinsky (arXiv 2607.19746), who state that the exponent of 3 is at least
`ω(N)/2 − 2` by a theorem of Bugeaud and Mihailescu and a lemma of Ochem and Rao; here the
unconditional single escape row theorem `card_escapeRows_le_one_all` takes the place of both.
Conditional family result; no novelty is claimed. -/
theorem restrained_omega_le {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    ω N ≤ 2 * N.factorization 3 + 3 := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have hc := restrained_card_squarePrimes_le h hq hodd hr hrq hsq
  have hE := card_sq_mod_three_eq_one_le h
  have hsub : N.primeFactors ⊆ insert q (insert 3 (squarePrimes N q)) := by
    intro p hp
    by_cases hpq : p = q
    · rw [hpq]
      exact Finset.mem_insert_self _ _
    by_cases hp3 : p = 3
    · rw [hp3]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
    exact Finset.mem_filter.mpr ⟨hp, hpq, F.sq p hp hpq hp3⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le q (insert 3 (squarePrimes N q))
  have h3 := Finset.card_insert_le 3 (squarePrimes N q)
  rw [cardDistinctFactors_eq_card_primeFactors]
  omega

/-- **Restrained family: `19024 ≤ v_3(N)`.** From `38049 ≤ ω(N) ≤ 2 * v_3(N) + 3` we get
`v_3(N) ≥ 19023`, and `v_3(N)` is even. Ochem and Zelinsky (arXiv 2607.19746) state a much
larger bound for this exponent, obtained by a long computation; it is not proved here.
Conditional family result checked by the kernel; no novelty is claimed. -/
theorem restrained_nineteen_thousand_le_three {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    19024 ≤ N.factorization 3 := by
  have h1 := restrained_omega_ge h hq hodd hr hrq hsq
  have h2 := restrained_omega_le h hq hodd hr hrq hsq
  obtain ⟨-, -, ⟨k, hk⟩, -⟩ := restrained_exception_eq_three h hq hodd hr hrq hsq
  omega

/-- **Restrained family: `Ω(N) ≥ 95119`.** From `ω(N) ≥ 38049`, `v_3(N) ≥ 19024` and
`2 ω(N) + v_3(N) ≤ Ω(N) + 3`.
Conditional family result; no novelty is claimed. -/
theorem restrained_Omega_ge_of_nineteen_thousand {N q r : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    95119 ≤ Ω N := by
  have h1 := restrained_omega_ge h hq hodd hr hrq hsq
  have h2 := restrained_nineteen_thousand_le_three h hq hodd hr hrq hsq
  have h3 := two_mul_card_add_factorization_three_le h
  omega

end OddPerfect

#print axioms OddPerfect.restrained_card_squarePrimes_le
#print axioms OddPerfect.restrained_omega_le
#print axioms OddPerfect.restrained_nineteen_thousand_le_three
#print axioms OddPerfect.restrained_Omega_ge_of_nineteen_thousand
