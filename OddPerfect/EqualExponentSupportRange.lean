import OddPerfect.EqualExponentBelow137
import OddPerfect.EqualExponentSupportWide
import OddPerfect.EqualExponentSpecialLowerPow
import OddPerfect.EqualExponentSupportTable

/-!
# Equal exponents: support certificates over a range of special exponents

Let `N = q ^ a * m ^ 2` be an odd perfect number with special prime `q`, `q ∤ m`, and suppose
every ordinary exponent equals `l - 1` for an odd prime `l`. Write `J = eulerIndex q a m`.

* `ten_pow_ten_lt_special_of_small_eulerIndex`: for `a ≤ 4000` and `ω(J) ≤ 5`, `10 ^ 10 < q`.
* `ten_pow_eight_hundred_lt_special_of_special_le_forty_nine`: for `a ≤ 49` and `ω(J) ≤ 5`,
  `10 ^ 800 < q`.
* `capDeficit_one_six_four`: the closed value `capDeficit 1 6 4 = 456`.
* `six_le_card_primeFactors_eulerIndex_of_special_le_four_thousand`: for `a ≤ 4000` and `l` at
  most `331` outside `179, 223, 263, 271`, `J` has at least six prime factors.
* `six_le_card_primeFactors_eulerIndex_or_of_special_le_221`: for
  `a ≤ 221`, `J` has at least six prime factors, or `l` is one of `179, 223, 263, 271`.
* `six_le_card_primeFactors_eulerIndex_or_of_special_le_sixty_nine`: for `a ≤ 69`, `J` has at
  least six prime factors, or `l = 179`.

Proof. The family is impossible for `l < 137`. For `l ≥ 137`, `v_l(a + 1) ≤ 1` when
`a ≤ 4000`, and `v_l(a + 1) = 0` when `a ≤ 49`; the bound of `special_gt_of_small_eulerIndex_pow`
then gives the size of the special prime, since a geometric sum is below the next power of its
base. With the special prime above `10 ^ 10`, the support certificates of
`OddPerfect.EqualExponentSupportData`, `OddPerfect.EqualExponentSupportWide` and
`OddPerfect.EqualExponentSupportTable` exclude an Euler index with at most five prime factors
for every prime `l` with `137 ≤ l ≤ 331` outside the four exceptions. For `a ≤ 221`, `a` is odd
and `a + 1 < 2 l`, so `v_l(a + 1) = 0`, and the row capacity (`equal_exponents_row_capacity`
with `T = 6`, `r = 4`, weight `1`) gives `l ≤ 331`. For `a ≤ 69` the weight `2` gives
`l ≤ 221`.

The certificates come from a search outside Lean; only the kernel checks are trusted. The
primes `179`, `223`, `263` and `271` stay explicit exceptions: a search outside Lean found no
certificate for them, which is a limit of the search and not a statement about these primes.

These are restricted results for the family where all ordinary exponents equal `l - 1`. The
family is not excluded; the special exponent and the number of prime factors of `J` are not
bounded here, and `l` is bounded only through that number. Restricted result; no published
source was checked; novelty not verified.
-/

namespace OddPerfect

namespace EqSupportRange

/-- `v_l(n) = 0` for `0 < n < l`. -/
private lemma padicValNat_eq_zero_of_lt {l n : ℕ} (hl : l.Prime) (hn0 : 0 < n)
    (hn : n < l) : padicValNat l n = 0 := by
  have hnd : ¬ l ∣ n := fun hd => absurd (Nat.le_of_dvd hn0 hd) (by omega)
  have : Fact l.Prime := ⟨hl⟩
  rw [Nat.padicValNat_def]
  exact multiplicity_eq_zero_of_not_dvd hnd

/-- `v_l(a + 1) = 0` for odd `a` with `a + 1 < 2 l`, `l` an odd prime. -/
private lemma padicValNat_eq_zero_of_odd {l a : ℕ} (hl : l.Prime) (hl2 : l ≠ 2)
    (hao : Odd a) (ha : a + 1 < 2 * l) : padicValNat l (a + 1) = 0 := by
  have hnd : ¬ l ∣ a + 1 := by
    rintro ⟨k, hk⟩
    have hk1 : k = 1 := by
      rcases Nat.lt_or_ge k 2 with h2 | h2
      · interval_cases k <;> omega
      · have := Nat.mul_le_mul_left l h2
        omega
    subst hk1
    obtain ⟨j, hj⟩ := hao
    obtain ⟨i, hi⟩ := hl.odd_of_ne_two hl2
    omega
  have : Fact l.Prime := ⟨hl⟩
  rw [Nat.padicValNat_def]
  exact multiplicity_eq_zero_of_not_dvd hnd

/-- `v_l(n) ≤ 1` for `0 < n ≤ 4001` and a prime `l ≥ 137`. -/
private lemma padicValNat_le_one {l n : ℕ} (hl : l.Prime) (h137 : 137 ≤ l) (hn0 : n ≠ 0)
    (hn : n ≤ 4001) : padicValNat l n ≤ 1 := by
  have : Fact l.Prime := ⟨hl⟩
  by_contra hc
  push Not at hc
  rw [Nat.padicValNat_def] at hc
  have hd : l ^ 2 ∣ n := (multiplicity_dvd_iff_le hn0).mpr (by omega)
  have h1 : l ^ 2 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hd
  have h2 : 137 ^ 2 ≤ l ^ 2 := Nat.pow_le_pow_left h137 2
  have h3 := h2.trans h1
  norm_num at h3
  omega

/-- `2 ≤ 10 ^ n` for `n ≠ 0`. -/
private lemma two_le_ten_pow {n : ℕ} (hn : n ≠ 0) : 2 ≤ 10 ^ n :=
  (by norm_num : 2 ≤ 10).trans (Nat.le_self_pow hn 10)

/-- `275 ^ (136 t) ≤ (2 l + 1) ^ ((l - 1) t)` for `l ≥ 137`. -/
private lemma pow_le_of_ge {l t : ℕ} (hl : 137 ≤ l) :
    (275 : ℕ) ^ (136 * t) ≤ (2 * l + 1) ^ ((l - 1) * t) :=
  calc (275 : ℕ) ^ (136 * t) ≤ (2 * l + 1) ^ (136 * t) := Nat.pow_le_pow_left (by omega) _
    _ ≤ (2 * l + 1) ^ ((l - 1) * t) :=
      Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (by omega))

/-- The geometric sum bound for `a ≤ 4000`, source bound `10 ^ 10` and `t = 129`. -/
private lemma geom_four_thousand {l : ℕ} (hl : 137 ≤ l) :
    ∑ j ∈ Finset.range (4000 + 1), (10 ^ 10 : ℕ) ^ j < (2 * l + 1) ^ ((l - 1) * 129) := by
  have h1 : ∑ j ∈ Finset.range (4000 + 1), (10 ^ 10 : ℕ) ^ j < (10 ^ 10) ^ (4000 + 1) :=
    Nat.geomSum_lt (two_le_ten_pow (n := 10) (by norm_num)) (fun k hk => Finset.mem_range.mp hk)
  have h2 : (10 ^ 10 : ℕ) ^ (4000 + 1) < 275 ^ (136 * 129) := by decide +kernel
  have h3 : (275 : ℕ) ^ (136 * 129) ≤ (2 * l + 1) ^ ((l - 1) * 129) :=
    pow_le_of_ge (t := 129) hl
  exact h1.trans (h2.trans_le h3)

/-- The geometric sum bound for `a ≤ 49`, source bound `10 ^ 800` and `t = 130`. -/
private lemma geom_forty_nine {l : ℕ} (hl : 137 ≤ l) :
    ∑ j ∈ Finset.range (49 + 1), (10 ^ 800 : ℕ) ^ j < (2 * l + 1) ^ ((l - 1) * 130) := by
  have h1 : ∑ j ∈ Finset.range (49 + 1), (10 ^ 800 : ℕ) ^ j < (10 ^ 800) ^ (49 + 1) :=
    Nat.geomSum_lt (two_le_ten_pow (n := 800) (by norm_num)) (fun k hk => Finset.mem_range.mp hk)
  have h2 : (10 ^ 800 : ℕ) ^ (49 + 1) < 275 ^ (136 * 130) := by decide +kernel
  have h3 : (275 : ℕ) ^ (136 * 130) ≤ (2 * l + 1) ^ ((l - 1) * 130) :=
    pow_le_of_ge (t := 130) hl
  exact h1.trans (h2.trans_le h3)

/-- The primes `l` with `137 ≤ l ≤ 331`, sorted by the certificate that covers them. -/
private lemma range_cases_of_prime {l : ℕ} (hl : l.Prime) (h1 : 137 ≤ l) (h2 : l ≤ 331) :
    (l = 131 ∨ l = 137 ∨ l = 139 ∨ l = 149 ∨ l = 151 ∨ l = 157 ∨ l = 163 ∨ l = 167 ∨ l = 173 ∨
      l = 181 ∨ l = 191 ∨ l = 193 ∨ l = 199) ∨ l = 197 ∨
    (l = 211 ∨ l = 227 ∨ l = 229 ∨ l = 233 ∨ l = 239 ∨ l = 241 ∨ l = 251 ∨ l = 257 ∨ l = 269 ∨
      l = 277 ∨ l = 281 ∨ l = 283 ∨ l = 293 ∨ l = 307 ∨ l = 311 ∨ l = 313 ∨ l = 317 ∨ l = 331) ∨
    (l = 179 ∨ l = 223 ∨ l = 263 ∨ l = 271) := by
  interval_cases l <;> first | decide | exact absurd hl (by norm_num)

/-- The certificates of `OddPerfect.EqualExponentSupportTable`: with the special prime above
`10 ^ 10`, an Euler index with at most five prime factors is impossible for the eighteen primes
`l` of the table. -/
private lemma false_of_table_cases {N q a m l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hJ : (eulerIndex q a m).primeFactors.card ≤ 5) (hB : 10 ^ 10 < q)
    (hcase : l = 211 ∨ l = 227 ∨ l = 229 ∨ l = 233 ∨ l = 239 ∨ l = 241 ∨ l = 251 ∨ l = 257 ∨
      l = 269 ∨ l = 277 ∨ l = 281 ∨ l = 283 ∨ l = 293 ∨ l = 307 ∨ l = 311 ∨ l = 313 ∨ l = 317 ∨
      l = 331) : False := by
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact EqSupport.supportCheck_sound (k := 5) h hq hN hqm hl hl2 hexp hJ hB
      EqSupport.check211
  · exact EqSupport.supportCheck_sound (k := 5) h hq hN hqm hl hl2 hexp hJ hB
      EqSupport.check227
  · exact EqSupport.supportCheck_sound (k := 5) h hq hN hqm hl hl2 hexp hJ hB
      EqSupport.check229
  · exact EqSupport.supportCheck_sound (k := 5) h hq hN hqm hl hl2 hexp hJ hB
      EqSupport.check233
  · exact EqSupport.supportCheck_sound (k := 5) h hq hN hqm hl hl2 hexp hJ hB
      EqSupport.check239
  · exact EqSupport.supportCheck_sound (k := 5) h hq hN hqm hl hl2 hexp hJ hB
      EqSupport.check241
  · exact EqSupport.supportCheck_sound (k := 5) h hq hN hqm hl hl2 hexp hJ hB
      EqSupport.check251
  · exact EqSupport.supportCheck_sound (k := 5) h hq hN hqm hl hl2 hexp hJ hB
      EqSupport.check257
  · exact EqSupport.supportCheck_sound (k := 5) h hq hN hqm hl hl2 hexp hJ hB
      EqSupport.check269
  · exact EqSupport.supportCheck_sound (k := 5) h hq hN hqm hl hl2 hexp hJ hB
      EqSupport.check277
  · exact EqSupport.supportCheck_sound (k := 5) h hq hN hqm hl hl2 hexp hJ hB
      EqSupport.check281
  · exact EqSupport.supportCheck_sound (k := 5) h hq hN hqm hl hl2 hexp hJ hB
      EqSupport.check283
  · exact EqSupport.supportCheck_sound (k := 5) h hq hN hqm hl hl2 hexp hJ hB
      EqSupport.check293
  · exact EqSupport.supportCheck_sound (k := 5) h hq hN hqm hl hl2 hexp hJ hB
      EqSupport.check307
  · exact EqSupport.supportCheck_sound (k := 5) h hq hN hqm hl hl2 hexp hJ hB
      EqSupport.check311
  · exact EqSupport.supportCheck_sound (k := 5) h hq hN hqm hl hl2 hexp hJ hB
      EqSupport.check313
  · exact EqSupport.supportCheck_sound (k := 5) h hq hN hqm hl hl2 hexp hJ hB
      EqSupport.check317
  · exact EqSupport.supportCheck_sound (k := 5) h hq hN hqm hl hl2 hexp hJ hB
      EqSupport.check331

end EqSupportRange

open EqSupportRange

/-- Closed value of `capDeficit 1 6 4`. -/
theorem capDeficit_one_six_four : capDeficit 1 6 4 = 456 := by decide +kernel

/-- For special exponent `a ≤ 4000` and equal ordinary exponents `l - 1` (`l` an odd prime), an
Euler index with at most five prime factors forces the special prime above `10 ^ 10`.
Restricted result for the family where all ordinary exponents equal `l - 1`; nothing is
excluded. Restricted result; no published source was checked; novelty not verified. -/
theorem ten_pow_ten_lt_special_of_small_eulerIndex {N q a m l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (ha : a ≤ 4000) (hl : l.Prime)
    (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hJ : (eulerIndex q a m).primeFactors.card ≤ 5) : 10 ^ 10 < q := by
  obtain ⟨-, hqa, hao, -⟩ := EqSupport.euler_frame h hq hN hqm
  rcases Nat.lt_or_ge l 137 with hlt | hge
  · exact (not_all_exponents_eq_pred_of_lt_137 h hq (hqa ▸ hao) hl hl2 hlt hexp).elim
  have hv : padicValNat l (a + 1) ≤ 1 := padicValNat_le_one hl hge (by omega) (by omega)
  exact special_gt_of_small_eulerIndex_pow (A := 4000) (B := 10 ^ 10) (t := 129) h hq hN hqm hl
    hl2 hexp (by omega) ha (geom_four_thousand hge)

/-- For special exponent `a ≤ 49` and equal ordinary exponents `l - 1` (`l` an odd prime), an
Euler index with at most five prime factors forces the special prime above `10 ^ 800`.
Restricted result for the family where all ordinary exponents equal `l - 1`; nothing is
excluded. Restricted result; no published source was checked; novelty not verified. -/
theorem ten_pow_eight_hundred_lt_special_of_special_le_forty_nine {N q a m l : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (ha : a ≤ 49)
    (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hJ : (eulerIndex q a m).primeFactors.card ≤ 5) : 10 ^ 800 < q := by
  obtain ⟨-, hqa, hao, -⟩ := EqSupport.euler_frame h hq hN hqm
  rcases Nat.lt_or_ge l 137 with hlt | hge
  · exact (not_all_exponents_eq_pred_of_lt_137 h hq (hqa ▸ hao) hl hl2 hlt hexp).elim
  have hv : padicValNat l (a + 1) = 0 :=
    padicValNat_eq_zero_of_lt hl (by omega) (by omega)
  exact special_gt_of_small_eulerIndex_pow (A := 49) (B := 10 ^ 800) (t := 130) h hq hN hqm hl
    hl2 hexp (by omega) ha (geom_forty_nine hge)

/-- For special exponent `a ≤ 4000` and equal ordinary exponents `l - 1`, where `l` is an odd
prime with `l ≤ 331` other than `179`, `223`, `263` and `271`, the Euler index has at least
six prime factors. The four primes stay explicit exceptions: a search outside Lean found
no certificate for them, which is a limit of the search and not a statement about them.
Restricted result: the family is not excluded. Restricted result; no published source was
checked; novelty not verified. -/
theorem six_le_card_primeFactors_eulerIndex_of_special_le_four_thousand {N q a m l : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (ha : a ≤ 4000)
    (hl : l.Prime) (hl2 : l ≠ 2) (hl331 : l ≤ 331)
    (hne : l ≠ 179 ∧ l ≠ 223 ∧ l ≠ 263 ∧ l ≠ 271)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    6 ≤ (eulerIndex q a m).primeFactors.card := by
  obtain ⟨-, hqa, hao, -⟩ := EqSupport.euler_frame h hq hN hqm
  rcases Nat.lt_or_ge l 137 with hlt | hge
  · exact (not_all_exponents_eq_pred_of_lt_137 h hq (hqa ▸ hao) hl hl2 hlt hexp).elim
  by_contra hk
  have hk5 : (eulerIndex q a m).primeFactors.card ≤ 5 := by omega
  have hq10 : 10 ^ 10 < q :=
    ten_pow_ten_lt_special_of_small_eulerIndex h hq hN hqm ha hl hl2 hexp hk5
  rcases range_cases_of_prime hl hge hl331 with hc | hc | hc | hc
  · exact EqSupport.false_of_support_cases h hq hN hqm hl hl2 hexp hk5
      (lt_trans (by norm_num) hq10) hc
  · subst hc
    exact EqSupport.supportCheck_sound (k := 5) h hq hN hqm hl hl2 hexp hk5
      (lt_trans (by norm_num) hq10) EqSupport.check197
  · exact false_of_table_cases h hq hN hqm hl hl2 hexp hk5 hq10 hc
  · omega

/-- For special exponent `a ≤ 221` and equal ordinary exponents `l - 1` (`l` an odd prime), the
Euler index has at least six prime factors, or `l` is `179`, `223`, `263` or `271`. The four
exceptions are left open: a search outside Lean found no certificate for them, which is a limit
of the search and not a statement about them. Restricted result: the family is not excluded.
Restricted result; no published source was checked; novelty not verified. -/
theorem six_le_card_primeFactors_eulerIndex_or_of_special_le_221
    {N q a m l : ℕ} (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m)
    (ha : a ≤ 221) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    6 ≤ (eulerIndex q a m).primeFactors.card ∨ l = 179 ∨ l = 223 ∨ l = 263 ∨ l = 271 := by
  obtain ⟨-, hqa, hao, -⟩ := EqSupport.euler_frame h hq hN hqm
  rcases Nat.lt_or_ge l 137 with hlt | hge
  · exact (not_all_exponents_eq_pred_of_lt_137 h hq (hqa ▸ hao) hl hl2 hlt hexp).elim
  by_cases hk : 6 ≤ (eulerIndex q a m).primeFactors.card
  · exact Or.inl hk
  have hk5 : (eulerIndex q a m).primeFactors.card ≤ 5 := by omega
  have hb := equal_exponents_row_capacity (w := 1) (T := 6) (r := 4) h hq hN hqm hl hl2 hexp
    (by norm_num) (by omega)
  rw [capDeficit_one_six_four, padicValNat_eq_zero_of_odd hl hl2 hao (by omega)] at hb
  have hl336 : l ≤ 336 := by omega
  have hl331 : l ≤ 331 := by
    by_contra hc
    have h332 : 332 ≤ l := by omega
    interval_cases l <;> exact absurd hl (by norm_num)
  by_cases hne : l ≠ 179 ∧ l ≠ 223 ∧ l ≠ 263 ∧ l ≠ 271
  · exact Or.inl (six_le_card_primeFactors_eulerIndex_of_special_le_four_thousand h hq hN hqm
      (by omega) hl hl2 hl331 hne hexp)
  · right
    omega

/-- For special exponent `a ≤ 69` and equal ordinary exponents `l - 1` (`l` an odd prime), the
Euler index has at least six prime factors, or `l = 179`. The exception is left open: a search
outside Lean found no certificate for it, which is a limit of the search and not a statement
about `179`. Restricted result: the family is not excluded. Restricted result; no published
source was checked; novelty not verified. -/
theorem six_le_card_primeFactors_eulerIndex_or_of_special_le_sixty_nine {N q a m l : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (ha : a ≤ 69)
    (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    6 ≤ (eulerIndex q a m).primeFactors.card ∨ l = 179 := by
  obtain ⟨-, hqa, hao, -⟩ := EqSupport.euler_frame h hq hN hqm
  rcases Nat.lt_or_ge l 137 with hlt | hge
  · exact (not_all_exponents_eq_pred_of_lt_137 h hq (hqa ▸ hao) hl hl2 hlt hexp).elim
  by_cases hk : 6 ≤ (eulerIndex q a m).primeFactors.card
  · exact Or.inl hk
  have hk5 : (eulerIndex q a m).primeFactors.card ≤ 5 := by omega
  have hb := equal_exponents_row_capacity (w := 2) (T := 6) (r := 4) h hq hN hqm hl hl2 hexp
    (by norm_num) (by omega)
  rw [capDeficit_two_six_four,
    padicValNat_eq_zero_of_lt (n := a + 1) hl (by omega) (by omega)] at hb
  have hl221 : l ≤ 221 := by omega
  by_cases h179 : l = 179
  · exact Or.inr h179
  · exact Or.inl (six_le_card_primeFactors_eulerIndex_of_special_le_four_thousand h hq hN hqm
      (by omega) hl hl2 (by omega) (by omega) hexp)

end OddPerfect

#print axioms OddPerfect.capDeficit_one_six_four
#print axioms OddPerfect.ten_pow_ten_lt_special_of_small_eulerIndex
#print axioms OddPerfect.ten_pow_eight_hundred_lt_special_of_special_le_forty_nine
#print axioms OddPerfect.six_le_card_primeFactors_eulerIndex_of_special_le_four_thousand
#print axioms OddPerfect.six_le_card_primeFactors_eulerIndex_or_of_special_le_221
#print axioms OddPerfect.six_le_card_primeFactors_eulerIndex_or_of_special_le_sixty_nine
