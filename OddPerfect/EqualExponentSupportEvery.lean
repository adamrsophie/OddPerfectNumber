import OddPerfect.EqualExponentSupportModFourData
import OddPerfect.EqualExponentBelow137

/-!
# Equal exponents: six prime factors of the Euler index for every special exponent

Setting: `N = q ^ a * m ^ 2` is an odd perfect number with special prime `q`, `q ∤ m`, `l` is
an odd prime and every prime factor of `N` other than `q` has exponent `l - 1`. Write
`J = eulerIndex q a m`.

Results:

* `six_le_card_primeFactors_eulerIndex_of_index_mem`: for `l` in 137, 149, 157, 173, 181, 193,
  197, 233, 241, 269, 281, 293, 313, 317 the Euler index has at least six prime factors, for
  every special exponent `a`.
* `six_le_card_primeFactors_eulerIndex_of_index_mod_four`: the same for every odd prime
  `l ≤ 197` with `l % 4 = 1`.

Proof idea: if `ω(J) ≤ 5`, the certificate for `l` from
`OddPerfect.EqualExponentSupportModFourData`, accepted by `EqSupport.supportCheckFour` with
target `7`, gives a contradiction by `EqSupport.supportCheckFour_sound`. Its sources are `3`
modulo `4`, so they differ from the special prime with no bound on `q` or on `a`. Below `137`
the family is impossible (`not_all_exponents_eq_pred_of_lt_137`).

Scope. The certificates come from a search outside Lean; only the kernel checks are trusted.
The list of fourteen primes is the set for which that search found such a certificate; this is
a limit of the search and not a statement about other primes. These are restricted results for
the family where all ordinary exponents equal `l - 1`; the family is not excluded. The special
exponent and the number of prime factors of the Euler index are not bounded, and `l` is bounded
only through that number. The odd perfect number conjecture remains open.

Restricted result; no published source was checked; novelty not verified.
-/

namespace OddPerfect

open EqSupport

/-- For these fourteen index primes the Euler index has at least six prime factors, for every
special exponent. Restricted result for the family where all ordinary exponents equal `l - 1`;
the list is the reach of a search outside Lean. Restricted result; no published source was
checked; novelty not verified. -/
theorem six_le_card_primeFactors_eulerIndex_of_index_mem {N q a m l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m)
    (hl : l ∈ [137, 149, 157, 173, 181, 193, 197, 233, 241, 269, 281, 293, 313, 317])
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    6 ≤ (eulerIndex q a m).primeFactors.card := by
  by_contra hlt
  have hk : (eulerIndex q a m).primeFactors.card ≤ 5 := by omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact supportCheckFour_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk fourCheck137
  · exact supportCheckFour_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk fourCheck149
  · exact supportCheckFour_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk fourCheck157
  · exact supportCheckFour_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk fourCheck173
  · exact supportCheckFour_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk fourCheck181
  · exact supportCheckFour_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk fourCheck193
  · exact supportCheckFour_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk fourCheck197
  · exact supportCheckFour_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk fourCheck233
  · exact supportCheckFour_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk fourCheck241
  · exact supportCheckFour_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk fourCheck269
  · exact supportCheckFour_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk fourCheck281
  · exact supportCheckFour_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk fourCheck293
  · exact supportCheckFour_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk fourCheck313
  · exact supportCheckFour_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk fourCheck317

/-- Every odd prime `l ≤ 197` with `l % 4 = 1`: below 137 the family is impossible, and the
seven primes 137, 149, 157, 173, 181, 193, 197 have certificates. So the Euler index has at
least six prime factors, for every special exponent. Restricted result for the family where all
ordinary exponents equal `l - 1`. Restricted result; no published source was checked; novelty
not verified. -/
theorem six_le_card_primeFactors_eulerIndex_of_index_mod_four {N q a m l : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m)
    (hl : l.Prime) (hl4 : l % 4 = 1) (hl197 : l ≤ 197)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    6 ≤ (eulerIndex q a m).primeFactors.card := by
  obtain ⟨-, hqa, hao, -⟩ := euler_frame h hq hN hqm
  have hodd : Odd (N.factorization q) := hqa ▸ hao
  have hl2 : l ≠ 2 := by omega
  rcases Nat.lt_or_ge l 137 with h137 | h137
  · exact (not_all_exponents_eq_pred_of_lt_137 h hq hodd hl hl2 h137 hexp).elim
  · have hmem : l ∈ [137, 149, 157, 173, 181, 193, 197, 233, 241, 269, 281, 293, 313, 317] := by
      interval_cases l <;> first
        | decide
        | (exfalso; omega)
        | (exfalso; norm_num at hl)
    exact six_le_card_primeFactors_eulerIndex_of_index_mem h hq hN hqm hmem hexp

end OddPerfect

#print axioms OddPerfect.six_le_card_primeFactors_eulerIndex_of_index_mem
#print axioms OddPerfect.six_le_card_primeFactors_eulerIndex_of_index_mod_four
