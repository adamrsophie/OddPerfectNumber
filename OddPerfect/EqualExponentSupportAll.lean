import OddPerfect.EqualExponentSupportSplitData
import OddPerfect.EqualExponentSupportEvery
import OddPerfect.EqualExponentBelow137

/-!
# Equal exponents: six prime factors of the Euler index for index primes up to 331

Setting: `N = q ^ a * m ^ 2` is an odd perfect number with special prime `q`, `q ∤ m`, `l` is
an odd prime and every prime factor of `N` other than `q` has exponent `l - 1`. Write
`J = eulerIndex q a m`.

Results:

* `six_le_card_primeFactors_eulerIndex_of_split_mem`: for `l` in 139, 151, 163, 167, 191, 199,
  211, 227, 229, 239, 251, 257, 277, 283, 307, 311, 331 the Euler index has at least six prime
  factors.
* `six_le_card_primeFactors_eulerIndex_of_index_le_331`: the same for every odd prime
  `l ≤ 331` other than 179, 223, 263, 271.

Proof idea: if `ω(J) ≤ 5`, the certificate for `l` from
`OddPerfect.EqualExponentSupportSplitData`, accepted by `EqSupport.splitCheck` with target `7`,
gives a contradiction by `EqSupport.splitCheck_sound`. That certificate splits on the special
prime: a main case in which `q` is none of finitely many listed primes, and one case for each
listed prime. For the second theorem: below `137` the family is impossible
(`not_all_exponents_eq_pred_of_lt_137`); from `137` to `331` every prime outside the four
exceptions is in the list of the first theorem or in the list of
`six_le_card_primeFactors_eulerIndex_of_index_mem`.

Scope. The certificates come from a search outside Lean; only the kernel checks are trusted.
The four exception primes are those for which that search found no certificate; this is a limit
of the search and not a statement about these primes. No bound on the special prime or on the
special exponent is assumed. These are restricted results for the family where all ordinary
exponents equal `l - 1`; the family is not excluded. The special exponent and the number of
prime factors of the Euler index are not bounded, and `l` is bounded only through that number.
Nothing is proved here for `l > 331`.
The odd perfect number conjecture remains open.

Restricted result; no published source was checked; novelty not verified.
-/

namespace OddPerfect

open EqSupport

/-- For these seventeen index primes the Euler index has at least six prime factors, for every
special prime and every special exponent. Restricted result for the family where all ordinary
exponents equal `l - 1`; the list is the reach of a search outside Lean. Restricted result; no
published source was checked; novelty not verified. -/
theorem six_le_card_primeFactors_eulerIndex_of_split_mem {N q a m l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m)
    (hl : l ∈ [139, 151, 163, 167, 191, 199, 211, 227, 229, 239, 251, 257, 277, 283, 307, 311,
      331])
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    6 ≤ (eulerIndex q a m).primeFactors.card := by
  by_contra hlt
  have hk : (eulerIndex q a m).primeFactors.card ≤ 5 := by omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact splitCheck_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk splitCheck139
  · exact splitCheck_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk splitCheck151
  · exact splitCheck_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk splitCheck163
  · exact splitCheck_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk splitCheck167
  · exact splitCheck_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk splitCheck191
  · exact splitCheck_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk splitCheck199
  · exact splitCheck_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk splitCheck211
  · exact splitCheck_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk splitCheck227
  · exact splitCheck_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk splitCheck229
  · exact splitCheck_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk splitCheck239
  · exact splitCheck_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk splitCheck251
  · exact splitCheck_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk splitCheck257
  · exact splitCheck_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk splitCheck277
  · exact splitCheck_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk splitCheck283
  · exact splitCheck_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk splitCheck307
  · exact splitCheck_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk splitCheck311
  · exact splitCheck_sound h hq hN hqm (by norm_num) (by norm_num) hexp hk splitCheck331

/-- Every odd prime `l ≤ 331` other than 179, 223, 263, 271: below 137 the family is
impossible, and every other prime from 137 to 331 has a certificate. So the Euler index has at
least six prime factors, for every special prime and every special exponent. The four exceptions
are a limit of the search outside Lean, not a statement about these primes. Restricted result
for the family where all ordinary exponents equal `l - 1`. Restricted result; no published
source was checked; novelty not verified. -/
theorem six_le_card_primeFactors_eulerIndex_of_index_le_331 {N q a m l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (hl : l.Prime) (hl2 : l ≠ 2)
    (hl331 : l ≤ 331)
    (hne : l ≠ 179 ∧ l ≠ 223 ∧ l ≠ 263 ∧ l ≠ 271)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    6 ≤ (eulerIndex q a m).primeFactors.card := by
  obtain ⟨-, hqa, hao, -⟩ := euler_frame h hq hN hqm
  have hodd : Odd (N.factorization q) := hqa ▸ hao
  rcases Nat.lt_or_ge l 137 with h137 | h137
  · exact (not_all_exponents_eq_pred_of_lt_137 h hq hodd hl hl2 h137 hexp).elim
  · have hmem : l ∈ [139, 151, 163, 167, 191, 199, 211, 227, 229, 239, 251, 257, 277, 283, 307,
        311, 331]
        ∨ l ∈ [137, 149, 157, 173, 181, 193, 197, 233, 241, 269, 281, 293, 313, 317] := by
      interval_cases l <;> first
        | decide
        | (exfalso; omega)
        | (exfalso; norm_num at hl)
    rcases hmem with hm | hm
    · exact six_le_card_primeFactors_eulerIndex_of_split_mem h hq hN hqm hm hexp
    · exact six_le_card_primeFactors_eulerIndex_of_index_mem h hq hN hqm hm hexp

end OddPerfect

#print axioms OddPerfect.six_le_card_primeFactors_eulerIndex_of_split_mem
#print axioms OddPerfect.six_le_card_primeFactors_eulerIndex_of_index_le_331
