import OddPerfect.RestrainedFourteen
import OddPerfect.RestrainedFifteen
import OddPerfect.RestrainedEighteen

/-!
# Restrained odd perfect numbers: the light row count

Setting of `restrained_omega_ge_wheel`: `N` is an odd perfect number with special prime `q` and
odd exponent `a = v_q(N)`, `r ≠ q` is a further prime (forced to be 3), and every other prime
factor has exponent 2. Write `E = v_3(N)`, `R = ordPrimes N q` for the prime factors other than
3 and `q`, and `A`, `B` for the numbers of members of `R` that are 1, respectively 2, modulo 3.

Split `R` into three parts (namespace `OddPerfect.RestrainedNineteen`):
* `qFreeRows N q` (`L`): the members `s` with `rowCount N q s ≤ 1` and `q ∤ s ^ 2 + s + 1`;
* `qRows N q` (`Z`): the members `s` with `rowCount N q s ≤ 1` and `q ∣ s ^ 2 + s + 1`;
* `heavyRows N q` (`H`): the members `s` with `rowCount N q s ≥ 2`.

Counts.
* `#L ≤ A`: a row of `L` is `t` or `3 t` with `t` a member of `R` that is 1 modulo 3
  (`restrained_light_row_shape`), and `s ↦ t` is injective: within a residue class since
  `x ^ 2 + x + 1` is strictly increasing, across the classes by `phi3_ne_three_mul_phi3`.
* `#L + 2 #H ≤ 2 A`: the rows of `R` feed each receiver at most 2 (`capacity`), and only the
  receivers that are 1 modulo 3 receive anything.
* `#Z ≤ a`: each row of `Z` sends at least one factor `q`, and the rows send at most `v_q(N)`.
* `A ≤ E`, from `restrained_three_eq`.

Hence `2 (A + B) ≤ 3 A + 2 a ≤ 3 E + 2 a`. With `ω(N) = A + B + 2` and
`Ω(N) = 2 (A + B) + E + a` this gives `2 ω(N) ≤ 3 E + 2 a + 4`, `8 ω(N) ≤ 3 Ω(N) + 15`,
`Ω(N) ≥ 1538575`, and `E ≥ 384644` when `a = 1`.

These are lower bounds in a restricted family only; the family is not excluded. Ochem and
Zelinsky (2026 preprint, arXiv 2607.19746) state the far larger bound
`v_3(N) ≥ 23,000,000,000` in this family, obtained by a long computation; it is not proved here.
Novelty was not verified. The odd perfect number conjecture is open and nothing here decides it.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.omega ArithmeticFunction.Omega

namespace OddPerfect

namespace RestrainedNineteen

open RestrainedSeven RestrainedFourteen

/-- **Step 1.** `x ^ 2 + x + 1 ≠ 3 (w ^ 2 + w + 1)` for a prime `w > 3`. Equality forces
`x = 3 u + 1` and `3 u (u + 1) = w (w + 1)`; then `w` divides `u` or `u + 1`, so `w ≤ u + 1`,
which leaves only `u ≤ 1`, and neither `u = 0` nor `u = 1` fits. -/
theorem phi3_ne_three_mul_phi3 {x w : ℕ} (hw : w.Prime) (hw3 : 3 < w) :
    x ^ 2 + x + 1 ≠ 3 * (w ^ 2 + w + 1) := by
  intro h
  have hx : x % 3 = 1 := (three_dvd_phi3_iff x).mp ⟨_, h⟩
  obtain ⟨u, rfl⟩ : ∃ u, x = 3 * u + 1 := ⟨x / 3, by omega⟩
  have hu : 3 * (u * (u + 1)) = w * (w + 1) := by nlinarith [h]
  have h20 : 4 * 5 ≤ w * (w + 1) := Nat.mul_le_mul (by omega) (by omega)
  have hd : w ∣ 3 * (u * (u + 1)) := hu ▸ dvd_mul_right w (w + 1)
  have hwle : w ≤ u + 1 := by
    rcases (Nat.Prime.dvd_mul hw).mp hd with h3 | h3
    · have := Nat.le_of_dvd (by norm_num) h3
      omega
    rcases (Nat.Prime.dvd_mul hw).mp h3 with h4 | h4
    · rcases Nat.eq_zero_or_pos u with h0 | h0
      · subst h0
        nlinarith
      · have := Nat.le_of_dvd h0 h4
        omega
    · exact Nat.le_of_dvd (by omega) h4
  have hup : w * (w + 1) ≤ (u + 1) * (u + 2) := Nat.mul_le_mul hwle (by omega)
  have hu1 : u ≤ 1 := by nlinarith
  interval_cases u <;> nlinarith

/-- `x ^ 2 + x + 1` is injective on `ℕ`. -/
theorem phi3_inj {a b : ℕ} (h : phi3 a = phi3 b) : a = b := by
  unfold phi3 at h
  rcases lt_trichotomy a b with hab | hab | hab
  · have := Nat.mul_self_lt_mul_self hab
    nlinarith
  · exact hab
  · have := Nat.mul_self_lt_mul_self hab
    nlinarith

/-- The set `L`: the members `s` of `R` with `rowCount N q s ≤ 1` and `q ∤ phi3 s`. -/
def qFreeRows (N q : ℕ) : Finset ℕ := (lightRows N q).filter (fun s => ¬ q ∣ phi3 s)

/-- The set `Z`: the members `s` of `R` with `rowCount N q s ≤ 1` and `q ∣ phi3 s`. -/
def qRows (N q : ℕ) : Finset ℕ := (lightRows N q).filter (fun s => q ∣ phi3 s)

/-- The set `H`: the members `s` of `R` with `rowCount N q s ≥ 2`. -/
def heavyRows (N q : ℕ) : Finset ℕ := (ordPrimes N q).filter (fun s => ¬ rowCount N q s ≤ 1)

/-- The factor `3 ^ ε` of a light row: 3 when `s ≡ 1 (mod 3)` and 1 otherwise. -/
def rowUnit (s : ℕ) : ℕ := if s % 3 = 1 then 3 else 1

/-- The shape of a row of `L`: `phi3 s = 3 ^ ε t` with `t ∈ O1`. -/
theorem free_shape {N q r s : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hs : s ∈ qFreeRows N q) : ∃ t ∈ ordOne N q, phi3 s = rowUnit s * t := by
  obtain ⟨hsL, hqs⟩ := Finset.mem_filter.mp hs
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  obtain ⟨hsp, -, hs3, -, -⟩ := RestrainedFourteen.mem_ord F (Finset.mem_filter.mp hsL).1
  obtain ⟨h2, h1⟩ := restrained_light_row_shape h hq hodd hr hrq hsq hsL hqs
  rcases mod_three_of_prime hsp hs3 with h31 | h32
  · obtain ⟨t, ht, he⟩ := h1 h31
    refine ⟨t, ht, ?_⟩
    rw [rowUnit, if_pos h31]
    exact he
  · obtain ⟨t, ht, he⟩ := h2 h32
    refine ⟨t, ht, ?_⟩
    rw [rowUnit, if_neg (by omega), one_mul]
    exact he

/-- The target of a row of `L`: `phi3 s / 3 ^ ε`. -/
theorem free_target {N q r s : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hs : s ∈ qFreeRows N q) :
    phi3 s / rowUnit s ∈ ordOne N q ∧ phi3 s = rowUnit s * (phi3 s / rowUnit s) := by
  obtain ⟨t, ht, he⟩ := free_shape h hq hodd hr hrq hsq hs
  have hpos : 0 < rowUnit s := by unfold rowUnit; split_ifs <;> norm_num
  have hdiv : phi3 s / rowUnit s = t := by rw [he, Nat.mul_div_cancel_left _ hpos]
  rw [hdiv]
  exact ⟨ht, he⟩

/-- **Step 2.** `#L ≤ #O1`: the target map is injective on `L`. -/
theorem card_free_le {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    (qFreeRows N q).card ≤ (ordOne N q).card := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  refine Finset.card_le_card_of_injOn (fun s => phi3 s / rowUnit s) (fun s hs => ?_) ?_
  · exact Finset.mem_coe.mpr (free_target h hq hodd hr hrq hsq (Finset.mem_coe.mp hs)).1
  intro s₁ hs₁ s₂ hs₂ heq
  have hs₁' := Finset.mem_coe.mp hs₁
  have hs₂' := Finset.mem_coe.mp hs₂
  have he₁ := (free_target h hq hodd hr hrq hsq hs₁').2
  have he₂ := (free_target h hq hodd hr hrq hsq hs₂').2
  simp only at heq
  have hR : ∀ s ∈ qFreeRows N q, s.Prime ∧ s % 3 ≠ 0 ∧ 3 < s := by
    intro s hs
    have hsR := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1
    obtain ⟨hsp, hsN, hs3, -, -⟩ := RestrainedFourteen.mem_ord F hsR
    have hB := restrained_le_of_ne_three h hq hodd hr hrq hsq hsN hs3
    have := mod_three_of_prime hsp hs3
    exact ⟨hsp, by omega, by omega⟩
  obtain ⟨hp₁, hm₁, hb₁⟩ := hR s₁ hs₁'
  obtain ⟨hp₂, hm₂, hb₂⟩ := hR s₂ hs₂'
  rw [← heq] at he₂
  set t := phi3 s₁ / rowUnit s₁
  unfold rowUnit at he₁ he₂
  by_cases c₁ : s₁ % 3 = 1 <;> by_cases c₂ : s₂ % 3 = 1 <;>
    simp only [c₁, c₂, ↓reduceIte, one_mul] at he₁ he₂
  · exact phi3_inj (he₁.trans he₂.symm)
  · exact (phi3_ne_three_mul_phi3 (x := s₁) hp₂ hb₂
      (show phi3 s₁ = 3 * phi3 s₂ by rw [he₁, he₂])).elim
  · exact (phi3_ne_three_mul_phi3 (x := s₂) hp₁ hb₁
      (show phi3 s₂ = 3 * phi3 s₁ by rw [he₁, he₂])).elim
  · exact phi3_inj (he₁.trans he₂.symm)

/-- A row of `L` holds at least one ordinary prime. -/
theorem one_le_rowCount_free {N q r s : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hs : s ∈ qFreeRows N q) : 1 ≤ rowCount N q s := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  obtain ⟨t, ht, he⟩ := free_shape h hq hodd hr hrq hsq hs
  have htR := (Finset.mem_filter.mp ht).1
  have htp := (RestrainedFourteen.mem_ord F htR).1
  have hn : phi3 s ≠ 0 := by unfold phi3; omega
  have hd : t ∣ phi3 s := by rw [he]; exact dvd_mul_left t _
  have h1 := htp.factorization_pos_of_dvd hn hd
  have h2 := Finset.single_le_sum (f := fun t => (phi3 s).factorization t)
    (fun t _ => Nat.zero_le _) htR
  unfold rowCount
  omega

/-- The double count: `∑ s ∈ R, rowCount N q s ≤ 2 #O1`. -/
theorem sum_rowCount_le {N q : ℕ} (F : Fam N q) :
    ∑ s ∈ ordPrimes N q, rowCount N q s ≤ 2 * (ordOne N q).card := by
  unfold rowCount
  rw [Finset.sum_comm]
  calc ∑ t ∈ ordPrimes N q, ∑ s ∈ ordPrimes N q, (phi3 s).factorization t
      ≤ ∑ t ∈ ordPrimes N q, (if t % 3 = 1 then 2 else 0) := by
        refine Finset.sum_le_sum fun t ht => ?_
        split_ifs with h1
        · exact RestrainedFourteen.capacity F ht
        · refine le_of_eq (Finset.sum_eq_zero fun s _ => ?_)
          obtain ⟨htp, -, ht3, -, -⟩ := RestrainedFourteen.mem_ord F ht
          by_contra hne
          exact h1 (prime_dvd_phi3_mod_three htp ht3 (Nat.dvd_of_factorization_pos hne))
    _ = 2 * (ordOne N q).card := by
        show _ = 2 * ((ordPrimes N q).filter (fun p => p % 3 = 1)).card
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **Step 3, the capacity count.** `#L + 2 #H ≤ 2 #O1`. -/
theorem free_add_two_heavy_le {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    (qFreeRows N q).card + 2 * (heavyRows N q).card ≤ 2 * (ordOne N q).card := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have hdisj : Disjoint (qFreeRows N q) (heavyRows N q) := by
    refine Finset.disjoint_left.mpr fun s hsL hsH => ?_
    have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hsL).1).2
    have h2 := (Finset.mem_filter.mp hsH).2
    exact h2 h1
  have hsub : qFreeRows N q ∪ heavyRows N q ⊆ ordPrimes N q := by
    intro s hs
    rcases Finset.mem_union.mp hs with hs | hs
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1
    · exact (Finset.mem_filter.mp hs).1
  have hU : ∑ s ∈ qFreeRows N q ∪ heavyRows N q, rowCount N q s ≤
      ∑ s ∈ ordPrimes N q, rowCount N q s :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_union hdisj] at hU
  have hL : (qFreeRows N q).card ≤ ∑ s ∈ qFreeRows N q, rowCount N q s := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun s hs => one_le_rowCount_free h hq hodd hr hrq hsq hs
  have hH : 2 * (heavyRows N q).card ≤ ∑ s ∈ heavyRows N q, rowCount N q s := by
    have h2 : ∑ s ∈ heavyRows N q, 2 ≤ ∑ s ∈ heavyRows N q, rowCount N q s :=
      Finset.sum_le_sum fun s hs => by
        have := (Finset.mem_filter.mp hs).2
        omega
    rw [Finset.sum_const, smul_eq_mul] at h2
    omega
  have hT := sum_rowCount_le F
  omega

/-- **Step 3, the rows divisible by `q`.** `#Z ≤ v_q(N)`. -/
theorem card_qRows_le {N q : ℕ} (F : Fam N q) : (qRows N q).card ≤ N.factorization q := by
  have hq2 : q ≠ 2 := by have := F.mod12; omega
  have hsub : qRows N q ⊆ N.primeFactors := fun s hs =>
    (RestrainedFourteen.mem_ord F (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1).2.1
  calc (qRows N q).card = ∑ s ∈ qRows N q, 1 := Finset.card_eq_sum_ones _
    _ ≤ ∑ s ∈ qRows N q, sigmaWeight N s q := Finset.sum_le_sum fun s hs => by
        obtain ⟨hsL, hd⟩ := Finset.mem_filter.mp hs
        rw [RestrainedFourteen.weight_eq F (Finset.mem_filter.mp hsL).1]
        have hn : phi3 s ≠ 0 := by unfold phi3; omega
        exact Nat.succ_le_of_lt (F.prime.factorization_pos_of_dvd hn hd)
    _ ≤ N.factorization q := sum_sigmaWeight_le_factorization F.perf F.prime hq2 hsub

/-- The set `R` is `N.primeFactors` with 3 and `q` removed. -/
theorem ordPrimes_eq (N q : ℕ) : ordPrimes N q = (N.primeFactors.erase 3).erase q := by
  ext p
  simp only [ordPrimes, Finset.mem_filter, Finset.mem_erase]
  tauto

/-- The counts in one place: `ω(N) = #R + 2`, `Ω(N) = 2 #R + E + a` and
`2 #R ≤ 3 E + 2 a`. -/
theorem counts {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    ω N = (ordPrimes N q).card + 2 ∧
      Ω N = 2 * (ordPrimes N q).card + N.factorization 3 + N.factorization q ∧
      2 * (ordPrimes N q).card ≤ 3 * N.factorization 3 + 2 * N.factorization q := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have hq3 : q ≠ 3 := by have := F.mod12; omega
  have hqN : q ∈ N.primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hq, ?_, h.ne_zero⟩
    obtain ⟨k, hk⟩ := hodd
    exact Nat.dvd_of_factorization_pos (by omega)
  have h3N : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_three, restrained_three_dvd h hq hodd hr hrq hsq, h.ne_zero⟩
  have hqm : q ∈ N.primeFactors.erase 3 := Finset.mem_erase.mpr ⟨hq3, hqN⟩
  -- the prime count
  have hω : ω N = (ordPrimes N q).card + 2 := by
    have e1 := Finset.card_erase_of_mem hqm
    have e2 := Finset.card_erase_of_mem h3N
    have p1 := Finset.card_pos.mpr ⟨q, hqm⟩
    have p2 := Finset.card_pos.mpr ⟨3, h3N⟩
    rw [cardDistinctFactors_eq_card_primeFactors, ordPrimes_eq]
    omega
  -- the total exponent
  have hΩ : Ω N = 2 * (ordPrimes N q).card + N.factorization 3 + N.factorization q := by
    have hR2 : ∑ p ∈ ordPrimes N q, N.factorization p = (ordPrimes N q).card * 2 :=
      Finset.sum_const_nat fun p hp => (RestrainedFourteen.mem_ord F hp).2.2.2.2
    rw [cardFactors_eq_sum_primeFactors, ← Finset.add_sum_erase _ _ h3N,
      ← Finset.add_sum_erase _ _ hqm, ← ordPrimes_eq, hR2]
    omega
  -- the partition of `R`
  have hP1 : (lightRows N q).card + (heavyRows N q).card = (ordPrimes N q).card :=
    Finset.card_filter_add_card_filter_not (s := ordPrimes N q) (fun s => rowCount N q s ≤ 1)
  have hP2 : (qRows N q).card + (qFreeRows N q).card = (lightRows N q).card :=
    Finset.card_filter_add_card_filter_not (s := lightRows N q) (fun s => q ∣ phi3 s)
  have hL := card_free_le h hq hodd hr hrq hsq
  have hLH := free_add_two_heavy_le h hq hodd hr hrq hsq
  have hZ := card_qRows_le F
  -- `#O1 ≤ E`
  have hO : ordOne N q = {p ∈ N.primeFactors | p ≠ 3 ∧ p ≠ q ∧ p % 3 = 1} := by
    ext p
    simp only [ordOne, ordPrimes, Finset.mem_filter, and_assoc]
  have hE := restrained_three_eq h hq hodd hr hrq hsq
  rw [← hO] at hE
  exact ⟨hω, hΩ, by omega⟩

end RestrainedNineteen

open RestrainedSeven RestrainedNineteen

/-- **Restrained family: `2 ω(N) ≤ 3 v_3(N) + 2 v_q(N) + 4`.** The prime factors other than 3
and `q` split into the light rows free of `q` (at most `#O1` of them, by an injective target
map), the light rows divisible by `q` (at most `v_q(N)`), and the heavy rows (at most
`#O1 − #L / 2`, by the capacity 2 of each receiver), and `#O1 ≤ v_3(N)`. A bound in a
restricted family only; the family is not excluded. Novelty was not verified. -/
theorem restrained_two_mul_omega_le {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    2 * ω N ≤ 3 * N.factorization 3 + 2 * N.factorization q + 4 := by
  obtain ⟨h1, -, h3⟩ := counts h hq hodd hr hrq hsq
  omega

/-- **Restrained family: `8 n ≤ 3 Ω(N) + 15` for every lower bound `n ≤ ω(N)`.** From
`restrained_two_mul_omega_le`, `Ω(N) = 2 ω(N) + v_3(N) + v_q(N) − 4` and `v_q(N) ≥ 1`; a later
lower bound for `ω(N)` can be plugged in. A bound in a restricted family only; the family is not
excluded. Novelty was not verified. -/
theorem restrained_eight_mul_le_of_le_omega {N q r n : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) (hn : n ≤ ω N) :
    8 * n ≤ 3 * Ω N + 15 := by
  obtain ⟨h1, h2, h3⟩ := counts h hq hodd hr hrq hsq
  obtain ⟨k, hk⟩ := hodd
  omega

/-- **Restrained family: `8 ω(N) ≤ 3 Ω(N) + 15`.** The case `n = ω(N)` of
`restrained_eight_mul_le_of_le_omega`. A bound in a restricted family only; the family is not
excluded. Novelty was not verified. -/
theorem restrained_eight_mul_omega_le {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    8 * ω N ≤ 3 * Ω N + 15 :=
  restrained_eight_mul_le_of_le_omega h hq hodd hr hrq hsq le_rfl

/-- **Restrained family: `Ω(N) ≥ 1538575`.** From `8 ω(N) ≤ 3 Ω(N) + 15` and `ω(N) ≥ 576967`
(`restrained_omega_ge_wheel`), and since `Ω(N) = 2 ω(N) + v_3(N) + v_q(N) − 4` is odd
(`v_3(N)` even, `v_q(N)` odd). A lower bound only; the family is not excluded. Ochem and
Zelinsky (2026 preprint) state a far larger bound for `v_3(N)` in this family; it is not
proved here. Novelty was not verified. -/
theorem restrained_bigOmega_ge {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    1538575 ≤ Ω N := by
  have hw := restrained_omega_ge_wheel h hq hodd hr hrq hsq
  have h8 := restrained_eight_mul_le_of_le_omega h hq hodd hr hrq hsq hw
  obtain ⟨-, h2, -⟩ := counts h hq hodd hr hrq hsq
  obtain ⟨-, -, ⟨e, he⟩, -⟩ := restrained_exception_eq_three h hq hodd hr hrq hsq
  obtain ⟨k, hk⟩ := hodd
  omega

/-- **Restrained family with `v_q(N) = 1`: `v_3(N) ≥ 384644`.** From
`2 ω(N) ≤ 3 v_3(N) + 6`, `ω(N) ≥ 576967` and the evenness of `v_3(N)`. A lower bound only;
the family is not excluded. Ochem and Zelinsky (2026 preprint, arXiv 2607.19746) state the
far larger bound `v_3(N) ≥ 23,000,000,000` in this family; it is not proved here. Novelty was
not verified. -/
theorem restrained_three_ge_of_exponent_one {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (ha : N.factorization q = 1) : 384644 ≤ N.factorization 3 := by
  have hw := restrained_omega_ge_wheel h hq hodd hr hrq hsq
  have h2 := restrained_two_mul_omega_le h hq hodd hr hrq hsq
  obtain ⟨-, -, ⟨e, he⟩, -⟩ := restrained_exception_eq_three h hq hodd hr hrq hsq
  omega

end OddPerfect

#print axioms OddPerfect.RestrainedNineteen.phi3_ne_three_mul_phi3
#print axioms OddPerfect.RestrainedNineteen.phi3_inj
#print axioms OddPerfect.RestrainedNineteen.free_shape
#print axioms OddPerfect.RestrainedNineteen.free_target
#print axioms OddPerfect.RestrainedNineteen.card_free_le
#print axioms OddPerfect.RestrainedNineteen.one_le_rowCount_free
#print axioms OddPerfect.RestrainedNineteen.sum_rowCount_le
#print axioms OddPerfect.RestrainedNineteen.free_add_two_heavy_le
#print axioms OddPerfect.RestrainedNineteen.card_qRows_le
#print axioms OddPerfect.RestrainedNineteen.ordPrimes_eq
#print axioms OddPerfect.RestrainedNineteen.counts
#print axioms OddPerfect.restrained_two_mul_omega_le
#print axioms OddPerfect.restrained_eight_mul_le_of_le_omega
#print axioms OddPerfect.restrained_eight_mul_omega_le
#print axioms OddPerfect.restrained_bigOmega_ge
#print axioms OddPerfect.restrained_three_ge_of_exponent_one
