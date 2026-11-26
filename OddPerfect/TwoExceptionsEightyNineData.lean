import OddPerfect.TwoExceptionsGeneralCore

/-!
# Certificate data for the row of length 89

Write `R(x) = ∑ i ∈ Finset.range 89, x ^ i = (x ^ 89 - 1) / (x - 1)` for `x ≥ 2`. This module
supplies the finite hypotheses of `OddPerfect.TwoExcGen.dvd_of_two_exceptions_gen` for `l = 89`,
`B = 1600`, `k = 44`, `m = 11`, `r0 = 179`, each checked by kernel reduction:

* for every odd prime `p < 100` other than `89`, a lower bound for the number of distinct prime
  factors of `R(p)`: at least `3`, except for the primes of `eList` where it is at least `2`;
* the values `R(p)` for the primes of `eList` are pairwise coprime, and all these primes are at
  least `11`;
* no prime below `179` is `1` modulo `89`;
* the two numerical bounds.

The trial factors are prime powers `r ^ e` with `r` prime, `r ≡ 1 (mod 178)` and `r < 4 * 10 ^ 6`,
exactly dividing `R(p)`.

Restricted result; no published source was checked; novelty not verified.
-/

namespace OddPerfect.TwoExc89

open OddPerfect.TwoExcGen

/-- The closed form of the row of length 89. -/
def Rv (p : ℕ) : ℕ := (p ^ 89 - 1) / (p - 1)

theorem geom_eq_Rv {p : ℕ} (hp : 2 ≤ p) : ∑ i ∈ Finset.range 89, p ^ i = Rv p :=
  Nat.geomSum_eq hp 89

/-- The odd primes below `100` other than `89`. -/
def small : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 97]

/-- The primes whose row is only shown to have two distinct prime factors. -/
def eList : List ℕ := [11, 53, 61, 71, 73, 79]

/-- Trial factors of `R(p)`. -/
def rsOf : ℕ → List ℕ
  | 3 => [179]
  | 5 => [179]
  | 7 => [1805633]
  | 13 => [179, 9257]
  | 17 => [179, 7121, 10859]
  | 19 => [179]
  | 23 => [11393, 66751, 70667, 460843]
  | 29 => [179, 1069, 27947]
  | 31 => [179, 1476511]
  | 37 => [11393, 1058389]
  | 41 => [465293]
  | 43 => [179]
  | 47 => [179]
  | 59 => [179]
  | 61 => [179]
  | 67 => [179]
  | 83 => [179]
  | 97 => [47527]
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

theorem eList_ge : ∀ p ∈ eList, 11 ≤ p := by
  decide +kernel

theorem eList_coprime : ∀ a ∈ eList, ∀ b ∈ eList, a ≠ b → Nat.gcd (Rv a) (Rv b) = 1 := by
  decide +kernel

/-- Every odd prime below `100` other than `89` is listed. -/
theorem mem_small {p : ℕ} (hp : p.Prime) (h100 : p < 100) (h2 : p ≠ 2) (hl : p ≠ 89) :
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
theorem small_facts : ∀ p, p.Prime → p < 100 → p ≠ 2 → p ≠ 89 →
    2 ≤ (∑ i ∈ Finset.range 89, p ^ i).primeFactors.card ∧
    (3 ≤ (∑ i ∈ Finset.range 89, p ^ i).primeFactors.card ∨ p ∈ eList.toFinset) := by
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

theorem e_ge : ∀ p ∈ eList.toFinset, 11 ≤ p := fun p hp =>
  eList_ge p (List.mem_toFinset.mp hp)

theorem e_coprime : ∀ a ∈ eList.toFinset, ∀ b ∈ eList.toFinset, a ≠ b →
    Nat.gcd (∑ i ∈ Finset.range 89, a ^ i) (∑ i ∈ Finset.range 89, b ^ i) = 1 := by
  intro a ha b hb hab
  rw [List.mem_toFinset] at ha hb
  have h1 := eList_ge a ha
  have h2 := eList_ge b hb
  rw [geom_eq_Rv (by omega), geom_eq_Rv (by omega)]
  exact eList_coprime a ha b hb hab

/-- No prime below `179` is `1` modulo `89`. -/
theorem ge_r0 : ∀ x, x.Prime → x % 89 = 1 → 179 ≤ x := by
  intro x hx h1
  by_contra hlt
  have : x = 1 ∨ x = 90 := by omega
  rcases this with rfl | rfl <;> norm_num at hx

theorem big_mem : ∀ p, p.Prime → 100 ≤ p → p ≤ 1600 → p ∈ (bigList 1600).toFinset :=
  fun _ hp h1 h2 => mem_bigList hp h1 h2

theorem big_ge : ∀ p ∈ (bigList 1600).toFinset, 2 ≤ p := fun p hp => by
  have := ge_of_mem_bigList (List.mem_toFinset.mp hp)
  omega

theorem denL_pos : 0 < denL 1600 := by
  decide +kernel

/-- The case a bound, cross multiplied. -/
theorem numeric_two :
    11 * 1599 * 179 ^ 2 * numL 1600 < 2 * 10 * 1423 * 178 ^ 2 * denL 1600 := by
  decide +kernel

theorem numeric_a : ab 11 * ((∏ p ∈ (bigList 1600).toFinset, ab p) *
      (1 / (1 - ((2 * (89 - 1) : ℕ) : ℚ) / ((((1600 : ℕ)) : ℚ) - 1)))) * ab 179 ^ 2 < 2 := by
  rw [prod_bigList denL_pos]
  have e1 : ab 11 = 11 / 10 := by norm_num [ab]
  have e2 : ab 179 = 179 / 178 := by norm_num [ab]
  have e3 : (1 : ℚ) / (1 - ((2 * (89 - 1) : ℕ) : ℚ) / ((((1600 : ℕ)) : ℚ) - 1)) = 1599 / 1423 := by
    norm_num
  rw [e1, e2, e3]
  have hd : (0 : ℚ) < denL 1600 := by exact_mod_cast denL_pos
  have hk : ((11 * 1599 * 179 ^ 2 * numL 1600 : ℕ) : ℚ) <
      ((2 * 10 * 1423 * 178 ^ 2 * denL 1600 : ℕ) : ℚ) := by
    exact_mod_cast numeric_two
  push_cast at hk
  have hq : (numL 1600 : ℚ) / denL 1600 <
      2 * (10 * 1423 * 178 ^ 2) / (11 * 1599 * 179 ^ 2) := by
    rw [div_lt_iff₀ hd]
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by norm_num)]
    linarith
  have e : 11 / 10 * ((numL 1600 : ℚ) / denL 1600 * (1599 / 1423)) * (179 / 178) ^ 2 =
      (11 / 10 * (1599 / 1423) * (179 / 178) ^ 2) * ((numL 1600 : ℚ) / denL 1600) := by
    ring
  rw [e]
  calc (11 / 10 * (1599 / 1423) * (179 / 178) ^ 2) * ((numL 1600 : ℚ) / denL 1600)
      < (11 / 10 * (1599 / 1423) * (179 / 178) ^ 2) *
          (2 * (10 * 1423 * 178 ^ 2) / (11 * 1599 * 179 ^ 2)) :=
        mul_lt_mul_of_pos_left hq (by norm_num)
    _ = 2 := by norm_num

theorem c_lt_one : ((2 * (89 - 1) : ℕ) : ℚ) / ((((1600 : ℕ)) : ℚ) - 1) < 1 := by
  norm_num

theorem c_lt_one' : ((1 : ℕ) : ℚ) / ((((1600 : ℕ)) : ℚ) - 1) < 1 := by
  norm_num

theorem numeric_b :
    100 / 99 * (1 / (1 - ((1 : ℕ) : ℚ) / ((((1600 : ℕ)) : ℚ) - 1))) * (15 / 8) < 2 := by
  norm_num

end OddPerfect.TwoExc89

#print axioms OddPerfect.TwoExc89.small_facts
#print axioms OddPerfect.TwoExc89.e_ge
#print axioms OddPerfect.TwoExc89.e_coprime
#print axioms OddPerfect.TwoExc89.ge_r0
#print axioms OddPerfect.TwoExc89.numeric_a
#print axioms OddPerfect.TwoExc89.numeric_b
