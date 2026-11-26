import OddPerfect.TwoExceptionsGeneralCore

/-!
# Certificate data for the row of length 67

Write `R(x) = ∑ i ∈ Finset.range 67, x ^ i = (x ^ 67 - 1) / (x - 1)` for `x ≥ 2`. This module
supplies the finite hypotheses of `OddPerfect.TwoExcGen.dvd_of_two_exceptions_gen` for `l = 67`,
`B = 1200`, `k = 33`, `m = 13`, `r0 = 269`, each checked by kernel reduction:

* for every odd prime `p < 100` other than `67`, a lower bound for the number of distinct prime
  factors of `R(p)`: at least `3`, except for the primes of `eList` where it is at least `2`;
* the values `R(p)` for the primes of `eList` are pairwise coprime, and all these primes are at
  least `13`;
* no prime below `269` is `1` modulo `67`;
* the two numerical bounds.

The trial factors are prime powers `r ^ e` with `r` prime, `r ≡ 1 (mod 134)` and `r < 4 * 10 ^ 6`,
exactly dividing `R(p)`.

Restricted result; no published source was checked; novelty not verified.
-/

namespace OddPerfect.TwoExc67

open OddPerfect.TwoExcGen

/-- The closed form of the row of length 67. -/
def Rv (p : ℕ) : ℕ := (p ^ 67 - 1) / (p - 1)

theorem geom_eq_Rv {p : ℕ} (hp : 2 ≤ p) : ∑ i ∈ Finset.range 67, p ^ i = Rv p :=
  Nat.geomSum_eq hp 67

/-- The odd primes below `100` other than `67`. -/
def small : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 71, 73, 79, 83, 89, 97]

/-- The primes whose row is only shown to have two distinct prime factors. -/
def eList : List ℕ := [13, 17, 19, 59, 71, 79, 97]

/-- Trial factors of `R(p)`. -/
def rsOf : ℕ → List ℕ
  | 3 => [221101]
  | 5 => [269, 1609, 26399]
  | 7 => [228337]
  | 11 => [15277, 2160349]
  | 17 => [436171]
  | 23 => [269]
  | 29 => [4691, 7237]
  | 31 => [882659]
  | 37 => [269, 446221]
  | 41 => [269, 466723, 862559]
  | 43 => [20771]
  | 47 => [269, 229409]
  | 53 => [269, 83617]
  | 61 => [269]
  | 73 => [97151, 808021]
  | 83 => [72763]
  | 89 => [171253]
  | _ => []

/-- The claimed lower bound. -/
def kOf (p : ℕ) : ℕ := if p ∈ eList then 2 else 3

theorem cert_ok :
    small.all (fun p => decide (kOf p ≤ cardLB (Rv p) (rsOf p))) = true := by
  decide +kernel

theorem Rv_pos {p : ℕ} (hp : 2 ≤ p) : Rv p ≠ 0 := by
  rw [← geom_eq_Rv hp]
  exact (Finset.sum_pos (fun i _ => by positivity) ⟨0, by simp⟩).ne'

theorem small_ge : ∀ p ∈ small, 2 ≤ p := by
  decide +kernel

theorem kOf_le_card {p : ℕ} (hp : p ∈ small) : kOf p ≤ (Rv p).primeFactors.card := by
  have h := List.all_eq_true.mp cert_ok p hp
  rw [decide_eq_true_eq] at h
  exact h.trans (cardLB_le _ _ (Rv_pos (small_ge p hp)))

theorem kOf_facts : ∀ p ∈ small, 2 ≤ kOf p ∧ (3 ≤ kOf p ∨ p ∈ eList) := by
  decide +kernel

theorem eList_ge : ∀ p ∈ eList, 13 ≤ p := by
  decide +kernel

theorem eList_coprime : ∀ a ∈ eList, ∀ b ∈ eList, a ≠ b → Nat.gcd (Rv a) (Rv b) = 1 := by
  decide +kernel

/-- Every odd prime below `100` other than `67` is listed. -/
theorem mem_small {p : ℕ} (hp : p.Prime) (h100 : p < 100) (h2 : p ≠ 2) (hl : p ≠ 67) :
    p ∈ small := by
  have key : ∀ s, 1 < s → p % s = 0 → p = s := fun s hs h =>
    ((hp.eq_one_or_self_of_dvd s (Nat.dvd_of_mod_eq_zero h)).resolve_left (by omega)).symm
  have k2 := key 2 (by norm_num)
  have k3 := key 3 (by norm_num)
  have k5 := key 5 (by norm_num)
  have k7 := key 7 (by norm_num)
  have h1 := hp.two_le
  interval_cases p <;> first | omega | simp [small]

/-- The row facts in the form of the core hypothesis. -/
theorem small_facts : ∀ p, p.Prime → p < 100 → p ≠ 2 → p ≠ 67 →
    2 ≤ (∑ i ∈ Finset.range 67, p ^ i).primeFactors.card ∧
    (3 ≤ (∑ i ∈ Finset.range 67, p ^ i).primeFactors.card ∨ p ∈ eList.toFinset) := by
  intro p hp h100 h2 hl
  have hm := mem_small hp h100 h2 hl
  rw [geom_eq_Rv hp.two_le, List.mem_toFinset]
  have hc := kOf_le_card hm
  have hf := kOf_facts p hm
  refine ⟨by omega, ?_⟩
  rcases hf.2 with h3 | h3
  · left
    omega
  · right
    exact h3

theorem e_ge : ∀ p ∈ eList.toFinset, 13 ≤ p := fun p hp =>
  eList_ge p (List.mem_toFinset.mp hp)

theorem e_coprime : ∀ a ∈ eList.toFinset, ∀ b ∈ eList.toFinset, a ≠ b →
    Nat.gcd (∑ i ∈ Finset.range 67, a ^ i) (∑ i ∈ Finset.range 67, b ^ i) = 1 := by
  intro a ha b hb hab
  rw [List.mem_toFinset] at ha hb
  have h1 := eList_ge a ha
  have h2 := eList_ge b hb
  rw [geom_eq_Rv (by omega), geom_eq_Rv (by omega)]
  exact eList_coprime a ha b hb hab

/-- No prime below `269` is `1` modulo `67`. -/
theorem ge_r0 : ∀ x, x.Prime → x % 67 = 1 → 269 ≤ x := by
  intro x hx h1
  by_contra hlt
  have : x = 1 ∨ x = 68 ∨ x = 135 ∨ x = 202 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> norm_num at hx

theorem big_mem : ∀ p, p.Prime → 100 ≤ p → p ≤ 1200 → p ∈ (bigList 1200).toFinset :=
  fun _ hp h1 h2 => mem_bigList hp h1 h2

theorem big_ge : ∀ p ∈ (bigList 1200).toFinset, 2 ≤ p := fun p hp => by
  have := ge_of_mem_bigList (List.mem_toFinset.mp hp)
  omega

theorem denL_pos : 0 < denL 1200 := by
  decide +kernel

/-- The case a bound, cross multiplied. -/
theorem numeric_two :
    13 * 1199 * 269 ^ 2 * numL 1200 < 2 * 12 * 1067 * 268 ^ 2 * denL 1200 := by
  decide +kernel

theorem numeric_a : ab 13 * ((∏ p ∈ (bigList 1200).toFinset, ab p) *
      (1 / (1 - ((2 * (67 - 1) : ℕ) : ℚ) / ((((1200 : ℕ)) : ℚ) - 1)))) * ab 269 ^ 2 < 2 := by
  rw [prod_bigList denL_pos]
  have e1 : ab 13 = 13 / 12 := by norm_num [ab]
  have e2 : ab 269 = 269 / 268 := by norm_num [ab]
  have e3 : (1 : ℚ) / (1 - ((2 * (67 - 1) : ℕ) : ℚ) / ((((1200 : ℕ)) : ℚ) - 1)) = 1199 / 1067 := by
    norm_num
  rw [e1, e2, e3]
  have hd : (0 : ℚ) < denL 1200 := by exact_mod_cast denL_pos
  have hk : ((13 * 1199 * 269 ^ 2 * numL 1200 : ℕ) : ℚ) <
      ((2 * 12 * 1067 * 268 ^ 2 * denL 1200 : ℕ) : ℚ) := by
    exact_mod_cast numeric_two
  push_cast at hk
  have hq : (numL 1200 : ℚ) / denL 1200 <
      2 * (12 * 1067 * 268 ^ 2) / (13 * 1199 * 269 ^ 2) := by
    rw [div_lt_iff₀ hd]
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by norm_num)]
    linarith
  have e : 13 / 12 * ((numL 1200 : ℚ) / denL 1200 * (1199 / 1067)) * (269 / 268) ^ 2 =
      (13 / 12 * (1199 / 1067) * (269 / 268) ^ 2) * ((numL 1200 : ℚ) / denL 1200) := by
    ring
  rw [e]
  calc (13 / 12 * (1199 / 1067) * (269 / 268) ^ 2) * ((numL 1200 : ℚ) / denL 1200)
      < (13 / 12 * (1199 / 1067) * (269 / 268) ^ 2) *
          (2 * (12 * 1067 * 268 ^ 2) / (13 * 1199 * 269 ^ 2)) :=
        mul_lt_mul_of_pos_left hq (by norm_num)
    _ = 2 := by norm_num

theorem c_lt_one : ((2 * (67 - 1) : ℕ) : ℚ) / ((((1200 : ℕ)) : ℚ) - 1) < 1 := by
  norm_num

theorem c_lt_one' : ((1 : ℕ) : ℚ) / ((((1200 : ℕ)) : ℚ) - 1) < 1 := by
  norm_num

theorem numeric_b :
    100 / 99 * (1 / (1 - ((1 : ℕ) : ℚ) / ((((1200 : ℕ)) : ℚ) - 1))) * (15 / 8) < 2 := by
  norm_num

end OddPerfect.TwoExc67

#print axioms OddPerfect.TwoExc67.small_facts
#print axioms OddPerfect.TwoExc67.e_ge
#print axioms OddPerfect.TwoExc67.e_coprime
#print axioms OddPerfect.TwoExc67.ge_r0
#print axioms OddPerfect.TwoExc67.numeric_a
#print axioms OddPerfect.TwoExc67.numeric_b
