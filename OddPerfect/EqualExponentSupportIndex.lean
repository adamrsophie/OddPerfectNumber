import OddPerfect.EqualExponentEulerIndex
import OddPerfect.EqualExponentSpecialLower
import OddPerfect.EqualExponentSupportData

/-!
# Equal exponents: six prime factors in the Euler index for special exponent at most 49

Let `N = q ^ a * m ^ 2` be an odd perfect number with special prime `q`, `q ∤ m`, and suppose
every ordinary exponent equals `l - 1` for an odd prime `l`. Write `J = eulerIndex q a m`.

* `six_le_card_primeFactors_eulerIndex_or_of_special_le_forty_nine`: for `a ≤ 49`, `J` has at
  least six prime factors, or `l` is `179` or `197`.
* `six_le_card_primeFactors_eulerIndex_of_special_le_twenty_nine`: for `a ≤ 29`, `J` has at
  least six prime factors.

Proof. The family is impossible for `l < 131`. If `J` has at most five prime factors, the row
capacity (`equal_exponents_row_capacity` with `T = 6`, `r = 4` and weight `2`, resp. `3`) gives
`l ≤ 201`, resp. `l ≤ 175`; the special prime exceeds `10 ^ 6`
(`special_gt_of_small_eulerIndex`), and the support certificate of
`OddPerfect.EqualExponentSupportData` for `l` gives a contradiction. The certificates come
from a search outside Lean; only the kernel check is trusted.

These are restricted results for the family where all ordinary exponents equal `l - 1`. The
family is not excluded; the special exponent and the number of prime factors of `J` are not
bounded here, and `l` is bounded only through that number. Restricted result; no published
source was checked; novelty not verified.
-/

namespace OddPerfect

/-- Closed value of `capDeficit 3 6 4`. -/
theorem capDeficit_three_six_four : capDeficit 3 6 4 = 267 := by decide +kernel

/-- Closed value of `capDeficit 2 6 4`. -/
theorem capDeficit_two_six_four : capDeficit 2 6 4 = 308 := by decide +kernel

/-- `v_l(n) = 0` for `0 < n < l`. -/
private lemma support_padicValNat_eq_zero_of_lt {l n : ℕ} (hl : l.Prime) (hn0 : 0 < n)
    (hn : n < l) : padicValNat l n = 0 := by
  have hnd : ¬ l ∣ n := fun hd => absurd (Nat.le_of_dvd hn0 hd) (by omega)
  have : Fact l.Prime := ⟨hl⟩
  rw [Nat.padicValNat_def]
  exact multiplicity_eq_zero_of_not_dvd hnd

/-- For special exponent `a ≤ 49` and equal ordinary exponents `l - 1` (`l` an odd prime), the
Euler index has at least six prime factors, or `l = 179` or `l = 197`. The two exceptions are
left open. Restricted result: the family is not excluded. Restricted result; no published
source was checked; novelty not verified. -/
theorem six_le_card_primeFactors_eulerIndex_or_of_special_le_forty_nine {N q a m l : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (ha : a ≤ 49)
    (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    6 ≤ (eulerIndex q a m).primeFactors.card ∨ l = 179 ∨ l = 197 := by
  obtain ⟨-, hqa, hao, -⟩ := EqSupport.euler_frame h hq hN hqm
  rcases Nat.lt_or_ge l 131 with hlt | hge
  · exact (not_all_exponents_eq_pred_of_lt_131 h hq (hqa ▸ hao) hl hl2 hlt hexp).elim
  by_cases hk : 6 ≤ (eulerIndex q a m).primeFactors.card
  · exact Or.inl hk
  right
  have hk5 : (eulerIndex q a m).primeFactors.card ≤ 5 := by omega
  have hb := equal_exponents_row_capacity (w := 2) (T := 6) (r := 4) h hq hN hqm hl hl2 hexp
    (by norm_num) (by omega)
  rw [capDeficit_two_six_four,
    support_padicValNat_eq_zero_of_lt (n := a + 1) hl (by omega) (by omega)] at hb
  have hl201 : l ≤ 201 := by omega
  have hla : ¬ l ∣ a + 1 := fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega)
  have hBq : 10 ^ 6 < q := special_gt_of_small_eulerIndex (A := 49) (B := 10 ^ 6) h hq hN hqm
    hl hl2 hexp hla (by omega) ha (EqSupport.geom_lt_of_le hge)
  rcases EqSupport.support_cases_of_prime hl hge hl201 with hc | hc
  · exact (EqSupport.false_of_support_cases h hq hN hqm hl hl2 hexp hk5 hBq hc).elim
  · exact hc

/-- For special exponent `a ≤ 29` and equal ordinary exponents `l - 1` (`l` an odd prime), the
Euler index has at least six prime factors. Restricted result: the number of prime factors
stays unbounded and the family is not excluded. Restricted result; no published source was
checked; novelty not verified. -/
theorem six_le_card_primeFactors_eulerIndex_of_special_le_twenty_nine {N q a m l : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (ha : a ≤ 29)
    (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    6 ≤ (eulerIndex q a m).primeFactors.card := by
  rcases six_le_card_primeFactors_eulerIndex_or_of_special_le_forty_nine h hq hN hqm
    (by omega) hl hl2 hexp with hk | hc
  · exact hk
  by_contra hk
  have hl175 : 175 < l := by omega
  have hb := equal_exponents_row_capacity (w := 3) (T := 6) (r := 4) h hq hN hqm hl hl2 hexp
    (by norm_num) (by omega)
  rw [capDeficit_three_six_four,
    support_padicValNat_eq_zero_of_lt (n := a + 1) hl (by omega) (by omega)] at hb
  omega

end OddPerfect

#print axioms OddPerfect.capDeficit_three_six_four
#print axioms OddPerfect.capDeficit_two_six_four
#print axioms OddPerfect.six_le_card_primeFactors_eulerIndex_or_of_special_le_forty_nine
#print axioms OddPerfect.six_le_card_primeFactors_eulerIndex_of_special_le_twenty_nine
