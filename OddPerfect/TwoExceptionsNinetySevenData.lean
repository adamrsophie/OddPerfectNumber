import OddPerfect.EqualExponentCount

/-!
# Certificate data for the row of length 97

Write `R(x) = ∑ i ∈ Finset.range 97, x ^ i = (x ^ 97 - 1) / (x - 1)` for `x ≥ 2`. This module
holds the finite facts used by `OddPerfect.TwoExceptionsNinetySevenCore`, each checked by kernel
reduction:

* for every odd prime `p < 100` other than `97`, a lower bound for the number of distinct prime
  factors of `R(p)`: at least `3`, except for seven primes where it is at least `2`;
* the values `R(p)` for those seven primes are pairwise coprime;
* the numbers in `[100, 1600]` without a prime factor up to `37` (they are the primes there)
  and a cross multiplied bound for their product of `p / (p - 1)`.

A lower bound for the number of prime factors walks a list of trial factors `r` with
`gcd(r, n / r) = 1`, and closes the cofactor `C` with the witness test of
`OddPerfect.EqCount.two_le_card_of_witness` (a prime power `C` has
`gcd(2 ^ C - 2 mod C, C) ≠ 1`).
-/

namespace OddPerfect.TwoExc97

open OddPerfect.EqCount (fermatRes two_le_card_of_witness)

/-- The closed form of the row of length 97. -/
def Rv (p : ℕ) : ℕ := (p ^ 97 - 1) / (p - 1)

theorem geom_eq_Rv {p : ℕ} (hp : 2 ≤ p) : ∑ i ∈ Finset.range 97, p ^ i = Rv p :=
  Nat.geomSum_eq hp 97

/-- A lower bound for the number of distinct prime factors of `n`, from trial factors. -/
def cardLB : ℕ → List ℕ → ℕ
  | n, [] =>
    if n ≤ 1 then 0 else if 2 < n && Nat.gcd (fermatRes 2 n) n == 1 then 2 else 1
  | n, r :: rs =>
    if 1 < r && n % r == 0 && Nat.gcd r (n / r) == 1 then cardLB (n / r) rs + 1 else 0

theorem cardLB_le : ∀ (rs : List ℕ) (n : ℕ), n ≠ 0 → cardLB n rs ≤ n.primeFactors.card
  | [], n, hn => by
    unfold cardLB
    split_ifs with h1 h2
    · exact Nat.zero_le _
    · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h2
      exact two_le_card_of_witness (by omega) h2.1 h2.2
    · exact (Nat.nonempty_primeFactors.mpr (by omega)).card_pos
  | r :: rs, n, hn => by
    unfold cardLB
    split_ifs with h
    · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      have hdvd : r ∣ n := Nat.dvd_of_mod_eq_zero h2
      have hn' : n = r * (n / r) := (Nat.mul_div_cancel' hdvd).symm
      have hq0 : n / r ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hn'
        exact hn hn'
      have hcop : Nat.Coprime r (n / r) := h3
      have ih := cardLB_le rs (n / r) hq0
      have hr1 : 1 ≤ r.primeFactors.card :=
        (Nat.nonempty_primeFactors.mpr h1).card_pos
      rw [hn', Nat.Coprime.primeFactors_mul hcop,
        Finset.card_union_of_disjoint hcop.disjoint_primeFactors, ← hn']
      omega
    · exact Nat.zero_le _

/-- The odd primes below `100` other than `97`. -/
def small23 : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89]

/-- The seven primes whose row is only shown to have two distinct prime factors. -/
def seven : List ℕ := [19, 29, 37, 47, 59, 71, 89]

/-- Trial factors of `R(p)`: prime factors below `2,000,000`, each occurring once. -/
def rsOf : ℕ → List ℕ
  | 3 => [76631]
  | 5 => [389, 264811]
  | 7 => [389, 971]
  | 11 => [389]
  | 13 => [389, 971]
  | 17 => [389]
  | 23 => [37831, 437083]
  | 31 => [4657, 14551, 51217]
  | 41 => [5821]
  | 43 => [4657]
  | 53 => [971]
  | 61 => [1747, 1631153]
  | 67 => [389, 437471]
  | 73 => [389]
  | 79 => [389, 186629]
  | 83 => [3299]
  | _ => []

/-- The claimed lower bound. -/
def kOf (p : ℕ) : ℕ := if p ∈ seven then 2 else 3

theorem cert_ok :
    small23.all (fun p => decide (kOf p ≤ cardLB (Rv p) (rsOf p))) = true := by
  decide +kernel

theorem Rv_pos {p : ℕ} (hp : 2 ≤ p) : Rv p ≠ 0 := by
  rw [← geom_eq_Rv hp]
  exact (Finset.sum_pos (fun i _ => by positivity) ⟨0, by simp⟩).ne'

theorem kOf_le_card {p : ℕ} (hp : p ∈ small23) : kOf p ≤ (Rv p).primeFactors.card := by
  have h := List.all_eq_true.mp cert_ok p hp
  rw [decide_eq_true_eq] at h
  have h2 : 2 ≤ p := by
    simp only [small23, List.mem_cons] at hp
    simp at hp
    omega
  exact h.trans (cardLB_le _ _ (Rv_pos h2))

theorem kOf_facts : ∀ p ∈ small23, 2 ≤ kOf p ∧ (3 ≤ kOf p ∨ p ∈ seven) := by
  decide +kernel

theorem seven_ge : ∀ p ∈ seven, 19 ≤ p := by
  decide +kernel

theorem seven_coprime : ∀ a ∈ seven, ∀ b ∈ seven, a ≠ b → Nat.gcd (Rv a) (Rv b) = 1 := by
  decide +kernel

/-- Every odd prime below `100` other than `97` is listed. -/
theorem mem_small23 {p : ℕ} (hp : p.Prime) (h100 : p < 100) (h2 : p ≠ 2) (h97 : p ≠ 97) :
    p ∈ small23 := by
  have key : ∀ s, 1 < s → p % s = 0 → p = s := fun s hs h =>
    ((hp.eq_one_or_self_of_dvd s (Nat.dvd_of_mod_eq_zero h)).resolve_left (by omega)).symm
  have k2 := key 2 (by norm_num)
  have k3 := key 3 (by norm_num)
  have k5 := key 5 (by norm_num)
  have k7 := key 7 (by norm_num)
  have h1 := hp.two_le
  interval_cases p <;> first | omega | simp [small23]

/-- The small primes used to sieve `[100, 1600]`. -/
def smallPs : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

/-- No prime factor up to `37`. -/
def good (n : ℕ) : Bool := smallPs.all (fun s => n % s != 0)

/-- The numbers in `[100, 1600]` without a prime factor up to `37`. -/
def bigPrimes : List ℕ := (List.range' 100 1501).filter good

theorem bigPrimes_nodup : bigPrimes.Nodup := List.Nodup.filter good List.nodup_range'

theorem mem_bigPrimes_iff {n : ℕ} : n ∈ bigPrimes → 100 ≤ n := by
  intro h
  simp only [bigPrimes, List.mem_filter, List.mem_range'_1] at h
  exact h.1.1

theorem mem_bigPrimes {p : ℕ} (hp : p.Prime) (h1 : 100 ≤ p) (h2 : p ≤ 1600) :
    p ∈ bigPrimes := by
  simp only [bigPrimes, List.mem_filter, List.mem_range'_1, good, List.all_eq_true,
    bne_iff_ne, ne_eq]
  refine ⟨⟨h1, by omega⟩, fun s hs h => ?_⟩
  have hs' : 2 ≤ s ∧ s ≤ 37 := by
    simp only [smallPs, List.mem_cons] at hs
    simp at hs
    omega
  have := hp.eq_one_or_self_of_dvd s (Nat.dvd_of_mod_eq_zero h)
  omega

/-- The product of the listed numbers. -/
def numL : ℕ := bigPrimes.prod

/-- The product of the listed numbers minus one. -/
def denL : ℕ := (bigPrimes.map (· - 1)).prod

/-- The bound `(389/388)^2 (19/18) ∏ p/(p-1) (1599/1407) < 2`, cross multiplied. -/
theorem numeric_two : 389 ^ 2 * 19 * 1599 * numL < 2 * 388 ^ 2 * 18 * 1407 * denL := by
  decide +kernel

end OddPerfect.TwoExc97

#print axioms OddPerfect.TwoExc97.cardLB_le
#print axioms OddPerfect.TwoExc97.kOf_le_card
#print axioms OddPerfect.TwoExc97.kOf_facts
#print axioms OddPerfect.TwoExc97.seven_coprime
#print axioms OddPerfect.TwoExc97.mem_small23
#print axioms OddPerfect.TwoExc97.mem_bigPrimes
#print axioms OddPerfect.TwoExc97.numeric_two
