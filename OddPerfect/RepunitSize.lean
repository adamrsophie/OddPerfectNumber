import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# A size bound for prime repunit rows with a common value

Let `p` be the value of the repunit `1 + r + ... + r ^ (ℓ r - 1)` for every base `r` of a finite
nonempty set `I` of odd primes, where every length `ℓ r` is an odd prime. The theorem
`repunit_rows_size` shows `2 * (∏ r ∈ I, ℓ r) * (∑ r ∈ I, (r - 1)) < p`.

This is an elementary size bound. It decides nothing about odd perfect numbers by itself, and its
novelty was not verified.

## Certificates

Both certificates are checked by `decide +kernel` on a merge walk: for two bases `r < s` the
walk runs through the increasing sequences `rep r 2, rep r 3, ...` and `rep s 2, rep s 3, ...`
at the same time and fails on a common value below the bound.

* Certificate A: for distinct odd primes `r, s < 512` and lengths at least two, no value below
  `2 ^ 18` is shared.
* Certificate B: for distinct odd primes `r, s ≤ 64` and lengths at least two, no value below
  `2 ^ 1536` is shared.

## Regimes

* One row: `2 * ℓ * (r - 1) < rep r ℓ` directly.
* Two or more rows: certificate A gives `2 ^ 18 ≤ p`. Let `n = Nat.log 2 p`. A base above `64`
  has length at most `n / 6 + 1`; any base has length at most `n + 1`. The lengths of the bases
  above `64` are distinct odd primes, so their product is at most the product of the odd primes
  up to `n / 6 + 1`. With `K = 2 * (∏ ℓ) * #I` one shows `K ^ 2 ≤ 2 ^ n`; then each base is at
  most `Nat.sqrt p` and the claim follows.
  * Regime 2 (`p < 2 ^ 1536`): by certificate B at most one base is at most `64`. For
    `n < 144` a finite table decides the inequality; for larger `n` a crude estimate does.
  * Regime 3 (`2 ^ 1536 ≤ p`): at most `17` bases are at most `64`, each with length at most
    `n + 1`, and a crude estimate suffices.
-/

namespace OddPerfect

namespace RepunitSize

/-- The repunit `1 + r + ... + r ^ (ℓ - 1)`. -/
private def rep (r ℓ : ℕ) : ℕ := ∑ i ∈ Finset.range ℓ, r ^ i

private theorem rep_succ (r ℓ : ℕ) : rep r (ℓ + 1) = rep r ℓ * r + 1 := by
  unfold rep
  rw [Finset.sum_range_succ', Finset.sum_mul]
  simp [pow_succ]

private theorem rep_two (r : ℕ) : rep r 2 = r + 1 := by
  simp only [rep, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

private theorem rep_three (r : ℕ) : rep r 3 = 1 + r + r ^ 2 := by
  simp only [rep, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

private theorem rep_lt_succ {r : ℕ} (hr : 1 ≤ r) (ℓ : ℕ) : rep r ℓ < rep r (ℓ + 1) := by
  rw [rep_succ]
  nlinarith

private theorem rep_le_rep {r i j : ℕ} (hr : 1 ≤ r) (h : i ≤ j) : rep r i ≤ rep r j :=
  (strictMono_nat_of_lt_succ (rep_lt_succ hr)).monotone h

private theorem rep_lt_rep_base {r s ℓ : ℕ} (h : r < s) (hℓ : 2 ≤ ℓ) : rep r ℓ < rep s ℓ := by
  unfold rep
  apply Finset.sum_lt_sum (fun i _ => Nat.pow_le_pow_left h.le i)
  exact ⟨1, Finset.mem_range.mpr (by omega), by simpa using h⟩

private theorem pow_le_rep (r : ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : r ^ (ℓ - 1) ≤ rep r ℓ := by
  unfold rep
  exact Finset.single_le_sum (f := fun i => r ^ i) (fun i _ => Nat.zero_le _)
    (Finset.mem_range.mpr (by omega))

private theorem sq_lt_rep (r : ℕ) {ℓ : ℕ} (hℓ : 3 ≤ ℓ) : r ^ 2 < rep r ℓ := by
  have hsub : ({0, 2} : Finset ℕ) ⊆ Finset.range ℓ := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rw [Finset.mem_range]
    omega
  have h := Finset.sum_le_sum_of_subset (f := fun i => r ^ i) hsub
  rw [Finset.sum_pair (by norm_num)] at h
  unfold rep
  simp only [pow_zero] at h
  omega

/-! ### The merge walk -/

/-- Merge walk over the repunits of the bases `r` and `s`: `a` and `b` are the current values,
`f` is fuel. It returns `true` when one value reaches `B` before a common value appears. -/
private def mergeChk (r s B : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | f + 1, a, b =>
    if Nat.ble B a || Nat.ble B b then true
    else if Nat.beq a b then false
    else if Nat.blt a b then mergeChk r s B f (a * r + 1) b
    else mergeChk r s B f a (b * s + 1)

private theorem mergeChk_sound {r s B : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) :
    ∀ f i j, mergeChk r s B f (rep r i) (rep s j) = true →
      ∀ ℓ m, i ≤ ℓ → j ≤ m → rep r ℓ = rep s m → B ≤ rep r ℓ := by
  intro f
  induction f with
  | zero => intro i j h; simp [mergeChk] at h
  | succ f ih =>
    intro i j h ℓ m hi hj he
    simp only [mergeChk] at h
    by_cases h1 : (Nat.ble B (rep r i) || Nat.ble B (rep s j)) = true
    · simp only [Bool.or_eq_true, Nat.ble_eq] at h1
      rcases h1 with h1 | h1
      · exact h1.trans (rep_le_rep hr hi)
      · rw [he]
        exact h1.trans (rep_le_rep hs hj)
    rw [if_neg h1] at h
    by_cases h2 : Nat.beq (rep r i) (rep s j) = true
    · rw [if_pos h2] at h
      exact absurd h (by simp)
    rw [if_neg h2] at h
    rw [Nat.beq_eq] at h2
    by_cases h3 : Nat.blt (rep r i) (rep s j) = true
    · rw [if_pos h3, ← rep_succ] at h
      rw [Nat.blt_eq] at h3
      rcases Nat.eq_or_lt_of_le hi with rfl | hi'
      · exfalso
        have := rep_le_rep hs hj
        omega
      · exact ih (i + 1) j h ℓ m hi' hj he
    · rw [if_neg h3, ← rep_succ] at h
      rw [Nat.blt_eq] at h3
      rcases Nat.eq_or_lt_of_le hj with rfl | hj'
      · exfalso
        have := rep_le_rep hr hi
        omega
      · exact ih i (j + 1) h ℓ m hi hj' he

/-- Check of all pairs of a list of bases by the merge walk. -/
private def pairsOK (B f : ℕ) : List ℕ → Bool
  | [] => true
  | r :: t => t.all (fun s => mergeChk r s B f (r + 1) (s + 1)) && pairsOK B f t

/-- No common repunit value below `B` for the bases `r` and `s` and lengths at least two. -/
private def NoColl (B r s : ℕ) : Prop :=
  ∀ ℓ m, 2 ≤ ℓ → 2 ≤ m → rep r ℓ = rep s m → B ≤ rep r ℓ

private theorem noColl_symm {B r s : ℕ} (h : NoColl B r s) : NoColl B s r := by
  intro ℓ m hℓ hm he
  rw [he]
  exact h m ℓ hm hℓ he.symm

private theorem noColl_of_mergeChk {B f r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (h : mergeChk r s B f (r + 1) (s + 1) = true) : NoColl B r s := by
  intro ℓ m hℓ hm he
  rw [← rep_two r, ← rep_two s] at h
  exact mergeChk_sound hr hs f 2 2 h ℓ m hℓ hm he

private theorem pairsOK_sound (B f : ℕ) : ∀ L : List ℕ, (∀ r ∈ L, 1 ≤ r) →
    pairsOK B f L = true → ∀ r ∈ L, ∀ s ∈ L, r ≠ s → NoColl B r s
  | [], _, _ => by simp
  | a :: t, hpos, h => by
    simp only [pairsOK, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨ha, ht⟩ := h
    have hpt : ∀ r ∈ t, 1 ≤ r := fun r hr => hpos r (List.mem_cons_of_mem a hr)
    have hpa : 1 ≤ a := hpos a (by simp)
    intro r hr s hs hrs
    rcases List.mem_cons.mp hr with rfl | hr' <;> rcases List.mem_cons.mp hs with rfl | hs'
    · exact absurd rfl hrs
    · exact noColl_of_mergeChk hpa (hpt s hs') (ha s hs')
    · exact noColl_symm (noColl_of_mergeChk hpa (hpt r hr') (ha r hr'))
    · exact pairsOK_sound B f t hpt ht r hr' s hs' hrs

/-- The odd numbers in `[3, n)` with no proper divisor in `ds`. -/
private def sieve (n : ℕ) (ds : List ℕ) : List ℕ :=
  (List.range n).filter
    (fun r => Nat.ble 3 r && r % 2 == 1 && ds.all (fun d => r == d || r % d != 0))

private theorem one_le_of_mem_sieve {n : ℕ} {ds : List ℕ} {r : ℕ} (h : r ∈ sieve n ds) :
    1 ≤ r := by
  simp only [sieve, List.mem_filter, Bool.and_eq_true, Nat.ble_eq] at h
  omega

private theorem mem_sieve {n : ℕ} {ds : List ℕ} (hds : ∀ d ∈ ds, 2 ≤ d) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrn : r < n) : r ∈ sieve n ds := by
  simp only [sieve, List.mem_filter, List.mem_range, Bool.and_eq_true, Nat.ble_eq,
    List.all_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne]
  refine ⟨hrn, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · have := hr.two_le
    omega
  · exact Nat.odd_iff.mp (hr.odd_of_ne_two hr2)
  · intro d hd
    by_cases h : r % d = 0
    · left
      rcases hr.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero h) with h1 | h1
      · have := hds d hd
        omega
      · exact h1.symm
    · right
      exact h

private theorem noColl_cert {B f n : ℕ} {ds : List ℕ} (hds : ∀ d ∈ ds, 2 ≤ d)
    (hc : pairsOK B f (sieve n ds) = true) {r s : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrn : r < n)
    (hs : s.Prime) (hs2 : s ≠ 2) (hsn : s < n) (hrs : r ≠ s) : NoColl B r s :=
  pairsOK_sound B f _ (fun _ h => one_le_of_mem_sieve h) hc r (mem_sieve hds hr hr2 hrn) s
    (mem_sieve hds hs hs2 hsn) hrs

/-- Certificate A. -/
private theorem certA : pairsOK (2 ^ 18) 100 (sieve 512 [3, 5, 7, 11, 13, 17, 19]) = true := by
  decide +kernel

/-- Certificate B. -/
private theorem certB : pairsOK (2 ^ 1536) 4000 (sieve 65 [3, 5, 7]) = true := by
  decide +kernel

private theorem lenB : (sieve 65 [3, 5, 7]).length = 17 := by
  decide +kernel

/-! ### One row -/

private theorem two_mul_le_three_pow : ∀ x, 4 ≤ x → 2 * x ≤ 3 ^ (x - 2) := by
  intro x hx
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih =>
    have : x + 1 - 2 = (x - 2) + 1 := by omega
    rw [this, pow_succ]
    omega

private theorem one_row {r ℓ : ℕ} (hr : 3 ≤ r) (hℓ : 3 ≤ ℓ) : 2 * ℓ * (r - 1) < rep r ℓ := by
  rcases Nat.eq_or_lt_of_le hℓ with rfl | hℓ4
  · rw [rep_three]
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 3 := ⟨r - 3, by omega⟩
    have : m + 3 - 1 = m + 2 := by omega
    rw [this]
    nlinarith
  · have h1 := two_mul_le_three_pow ℓ hℓ4
    have h2 : 3 ^ (ℓ - 2) ≤ r ^ (ℓ - 2) := Nat.pow_le_pow_left hr _
    have h3 : r ^ (ℓ - 1) = r ^ (ℓ - 2) * r := by
      rw [← pow_succ]
      congr 1
      omega
    have h4 := pow_le_rep r (show 1 ≤ ℓ by omega)
    calc 2 * ℓ * (r - 1) < 2 * ℓ * r := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      _ ≤ r ^ (ℓ - 2) * r := Nat.mul_le_mul_right r (h1.trans h2)
      _ = r ^ (ℓ - 1) := h3.symm
      _ ≤ rep r ℓ := h4

/-! ### Odd primes up to a bound -/

/-- The odd primes up to `m`. -/
private def oddPr (m : ℕ) : Finset ℕ := (Finset.range (m + 1)).filter (fun q => q.Prime ∧ q ≠ 2)

private theorem oddPr_prod_le (m : ℕ) : ∏ q ∈ oddPr m, q ≤ 4 ^ m := by
  refine le_trans (Nat.le_of_dvd (primorial_pos m) ?_) (primorial_le_four_pow m)
  unfold primorial oddPr
  exact Finset.prod_dvd_prod_of_subset _ _ _ (fun q hq => by
    simp only [Finset.mem_filter] at hq ⊢
    exact ⟨hq.1, hq.2.1⟩)

private theorem oddPr_card_le (m : ℕ) : (oddPr m).card ≤ m + 1 :=
  (Finset.card_filter_le _ _).trans (Finset.card_range _).le

private theorem table : ∀ n ∈ Finset.Ico 18 144,
    (2 * ((n + 1) * ∏ q ∈ oddPr (n / 6 + 1), q) * (1 + (oddPr (n / 6 + 1)).card)) ^ 2 ≤
      2 ^ n := by
  decide +kernel

/-! ### Crude estimates -/

private theorem crude_two (n : ℕ) (hn : 144 ≤ n) :
    (2 * ((n + 1) * 4 ^ (n / 6 + 1)) * (1 + (n / 6 + 2))) ^ 2 ≤ 2 ^ n := by
  set t := n / 6 with ht
  set q := t / 8 with hq
  have hq2 : q + 1 ≤ 2 ^ q := Nat.lt_two_pow_self
  have h1 : n + 1 ≤ 2 ^ (q + 6) := by
    rw [pow_add]
    omega
  have h2 : 1 + (t + 2) ≤ 2 ^ (q + 4) := by
    rw [pow_add]
    omega
  have h3 : (4 : ℕ) ^ (t + 1) = 2 ^ (2 * t + 2) := by
    rw [show 2 * t + 2 = 2 * (t + 1) by ring, pow_mul]
    norm_num
  have hK : 2 * ((n + 1) * 4 ^ (t + 1)) * (1 + (t + 2)) ≤ 2 ^ (2 * q + 13 + 2 * t) := by
    rw [h3]
    calc 2 * ((n + 1) * 2 ^ (2 * t + 2)) * (1 + (t + 2))
        ≤ 2 * (2 ^ (q + 6) * 2 ^ (2 * t + 2)) * 2 ^ (q + 4) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ h1)) h2
      _ = 2 ^ (2 * q + 13 + 2 * t) := by ring
  calc (2 * ((n + 1) * 4 ^ (t + 1)) * (1 + (t + 2))) ^ 2
      ≤ (2 ^ (2 * q + 13 + 2 * t)) ^ 2 := Nat.pow_le_pow_left hK 2
    _ = 2 ^ ((2 * q + 13 + 2 * t) * 2) := (pow_mul 2 _ 2).symm
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)

private theorem crude_three (n : ℕ) (hn : 1536 ≤ n) :
    (2 * ((n + 1) ^ 17 * 4 ^ (n / 6 + 1)) * (17 + (n / 6 + 2))) ^ 2 ≤ 2 ^ n := by
  set t := n / 6 with ht
  set q := t / 64 with hq
  have hq2 : q + 1 ≤ 2 ^ q := Nat.lt_two_pow_self
  have h1 : n + 1 ≤ 2 ^ (q + 9) := by
    rw [pow_add]
    omega
  have h1' : (n + 1) ^ 17 ≤ 2 ^ ((q + 9) * 17) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left h1 17
  have h2 : 17 + (t + 2) ≤ 2 ^ (q + 9) := by
    rw [pow_add]
    omega
  have h3 : (4 : ℕ) ^ (t + 1) = 2 ^ (2 * t + 2) := by
    rw [show 2 * t + 2 = 2 * (t + 1) by ring, pow_mul]
    norm_num
  have hK : 2 * ((n + 1) ^ 17 * 4 ^ (t + 1)) * (17 + (t + 2)) ≤
      2 ^ (18 * q + 165 + 2 * t) := by
    rw [h3]
    calc 2 * ((n + 1) ^ 17 * 2 ^ (2 * t + 2)) * (17 + (t + 2))
        ≤ 2 * (2 ^ ((q + 9) * 17) * 2 ^ (2 * t + 2)) * 2 ^ (q + 9) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ h1')) h2
      _ = 2 ^ (18 * q + 165 + 2 * t) := by ring
  calc (2 * ((n + 1) ^ 17 * 4 ^ (t + 1)) * (17 + (t + 2))) ^ 2
      ≤ (2 ^ (18 * q + 165 + 2 * t)) ^ 2 := Nat.pow_le_pow_left hK 2
    _ = 2 ^ ((18 * q + 165 + 2 * t) * 2) := (pow_mul 2 _ 2).symm
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ### The last step -/

private theorem finish {I : Finset ℕ} {ℓ : ℕ → ℕ} {p : ℕ} (hne : I.Nonempty)
    (hsq : ∀ r ∈ I, r ^ 2 < p) (hD : 0 < ∏ r ∈ I, ℓ r)
    (hK : (2 * (∏ r ∈ I, ℓ r) * I.card) ^ 2 ≤ p) :
    2 * (∏ r ∈ I, ℓ r) * (∑ r ∈ I, (r - 1)) < p := by
  set D := ∏ r ∈ I, ℓ r
  set s := Nat.sqrt p
  obtain ⟨r0, hr0⟩ := hne
  have hs1 : 1 ≤ s := Nat.le_sqrt'.mpr (by have := hsq r0 hr0; omega)
  have hrs : ∀ r ∈ I, r - 1 < s := by
    intro r hr
    have := Nat.le_sqrt'.mpr (hsq r hr).le
    omega
  have hsum : ∑ r ∈ I, (r - 1) < I.card * s := by
    calc ∑ r ∈ I, (r - 1) < ∑ _r ∈ I, s := Finset.sum_lt_sum_of_nonempty ⟨r0, hr0⟩ hrs
      _ = I.card * s := by rw [Finset.sum_const, smul_eq_mul]
  have hKs : 2 * D * I.card ≤ s := Nat.le_sqrt'.mpr hK
  calc 2 * D * ∑ r ∈ I, (r - 1) < 2 * D * (I.card * s) :=
        Nat.mul_lt_mul_of_pos_left hsum (by omega)
    _ = (2 * D * I.card) * s := by ring
    _ ≤ s * s := Nat.mul_le_mul_right s hKs
    _ ≤ p := Nat.sqrt_le p

end RepunitSize

open RepunitSize in
/-- If `p` is the value of the repunit `1 + r + ... + r ^ (ℓ r - 1)` for each base `r` of a finite
nonempty set `I` of odd primes, with odd prime lengths `ℓ r`, then twice the product of the
lengths times the sum of the `r - 1` is below `p`. -/
theorem repunit_rows_size (p : ℕ) (I : Finset ℕ) (ℓ : ℕ → ℕ) (hne : I.Nonempty)
    (h : ∀ r ∈ I, r.Prime ∧ r ≠ 2 ∧ (ℓ r).Prime ∧ ℓ r ≠ 2 ∧
      ∑ i ∈ Finset.range (ℓ r), r ^ i = p) :
    2 * (∏ r ∈ I, ℓ r) * (∑ r ∈ I, (r - 1)) < p := by
  have hrep : ∀ r ∈ I, rep r (ℓ r) = p := fun r hr => (h r hr).2.2.2.2
  have hr3 : ∀ r ∈ I, 3 ≤ r := fun r hr => by
    have := (h r hr).1.two_le
    have := (h r hr).2.1
    omega
  have hl3 : ∀ r ∈ I, 3 ≤ ℓ r := fun r hr => by
    have := (h r hr).2.2.1.two_le
    have := (h r hr).2.2.2.1
    omega
  have hsq : ∀ r ∈ I, r ^ 2 < p := fun r hr => hrep r hr ▸ sq_lt_rep r (hl3 r hr)
  have hDpos : 0 < ∏ r ∈ I, ℓ r := Finset.prod_pos (fun r hr => by have := hl3 r hr; omega)
  have hinj : Set.InjOn ℓ I := by
    intro r hr s hs he
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · have := rep_lt_rep_base (ℓ := ℓ r) hlt (by have := hl3 r hr; omega)
      rw [hrep r hr, he, hrep s hs] at this
      exact lt_irrefl _ this
    · have := rep_lt_rep_base (ℓ := ℓ s) hlt (by have := hl3 s hs; omega)
      rw [hrep s hs, ← he, hrep r hr] at this
      exact lt_irrefl _ this
  rcases Nat.lt_or_ge 1 I.card with hk | hk
  swap
  · obtain ⟨r, rfl⟩ : ∃ r, I = {r} := Finset.card_eq_one.mp (by have := hne.card_pos; omega)
    simp only [Finset.prod_singleton, Finset.sum_singleton]
    have hr : r ∈ ({r} : Finset ℕ) := Finset.mem_singleton_self r
    rw [← hrep r hr]
    exact one_row (hr3 r hr) (hl3 r hr)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hk
  have hp18 : 2 ^ 18 ≤ p := by
    by_contra hlt
    replace hlt := not_le.mp hlt
    have hlt' : ∀ r ∈ I, r < 512 := fun r hr => by
      have : r ^ 2 < 512 ^ 2 := (hsq r hr).trans (hlt.trans_eq (by norm_num))
      exact (Nat.pow_lt_pow_iff_left (by norm_num)).mp this
    have := noColl_cert (by decide) certA (h a ha).1 (h a ha).2.1 (hlt' a ha) (h b hb).1
      (h b hb).2.1 (hlt' b hb) hab (ℓ a) (ℓ b) (by have := hl3 a ha; omega)
      (by have := hl3 b hb; omega) (by rw [hrep a ha, hrep b hb])
    rw [hrep a ha] at this
    exact absurd this (not_le.mpr hlt)
  have hp0 : p ≠ 0 := by
    have : 0 < 2 ^ 18 := by positivity
    omega
  set n := Nat.log 2 p with hn
  have hn1 : 2 ^ n ≤ p := Nat.pow_log_le_self 2 hp0
  have hn2 : p < 2 ^ (n + 1) := Nat.lt_pow_succ_log_self (by norm_num) p
  have hn18 : 18 ≤ n := Nat.le_log_of_pow_le (by norm_num) hp18
  have hlen : ∀ r ∈ I, ℓ r ≤ n + 1 := by
    intro r hr
    have h1 : 2 ^ (ℓ r - 1) ≤ r ^ (ℓ r - 1) :=
      Nat.pow_le_pow_left (by have := hr3 r hr; omega) _
    have h2 := pow_le_rep r (show 1 ≤ ℓ r by have := hl3 r hr; omega)
    rw [hrep r hr] at h2
    have : 2 ^ (ℓ r - 1) < 2 ^ (n + 1) := lt_of_le_of_lt (h1.trans h2) hn2
    have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    omega
  have hlenL : ∀ r ∈ I, 64 < r → ℓ r ≤ n / 6 + 1 := by
    intro r hr h64
    have h1 : 64 ^ (ℓ r - 1) ≤ r ^ (ℓ r - 1) := Nat.pow_le_pow_left h64.le _
    have h2 := pow_le_rep r (show 1 ≤ ℓ r by have := hl3 r hr; omega)
    rw [hrep r hr] at h2
    have h3 : (64 : ℕ) ^ (ℓ r - 1) = 2 ^ (6 * (ℓ r - 1)) := by
      rw [pow_mul]
      norm_num
    have : 2 ^ (6 * (ℓ r - 1)) < 2 ^ (n + 1) := by
      rw [← h3]
      exact lt_of_le_of_lt (h1.trans h2) hn2
    have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    omega
  set Is := I.filter (fun r => r ≤ 64) with hIs
  set Il := I.filter (fun r => ¬ r ≤ 64) with hIl
  have hD : ∏ r ∈ I, ℓ r = (∏ r ∈ Is, ℓ r) * ∏ r ∈ Il, ℓ r :=
    (Finset.prod_filter_mul_prod_filter_not I _ ℓ).symm
  have hk' : I.card = Is.card + Il.card := (Finset.card_filter_add_card_filter_not _).symm
  have hT : Il.image ℓ ⊆ oddPr (n / 6 + 1) := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
    rw [Finset.mem_filter] at hr
    simp only [oddPr, Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := hlenL r hr.1 (by omega); omega, (h r hr.1).2.2.1, (h r hr.1).2.2.2.1⟩
  have hinjL : Set.InjOn ℓ Il :=
    hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
  have hDl : ∏ r ∈ Il, ℓ r ≤ ∏ q ∈ oddPr (n / 6 + 1), q := by
    rw [show ∏ r ∈ Il, ℓ r = ∏ q ∈ Il.image ℓ, q from
      (Finset.prod_image (f := fun x => x) hinjL).symm]
    exact Nat.le_of_dvd (Finset.prod_pos (fun q hq => (Finset.mem_filter.mp hq).2.1.pos))
      (Finset.prod_dvd_prod_of_subset _ _ _ hT)
  have hkl : Il.card ≤ (oddPr (n / 6 + 1)).card := by
    rw [← Finset.card_image_of_injOn hinjL]
    exact Finset.card_le_card hT
  have hDs : ∏ r ∈ Is, ℓ r ≤ (n + 1) ^ Is.card :=
    Finset.prod_le_pow_card _ _ _ (fun r hr => hlen r (Finset.mem_filter.mp hr).1)
  refine finish ⟨a, ha⟩ hsq hDpos ?_
  rw [hD, hk']
  refine le_trans ?_ hn1
  by_cases hB : p < 2 ^ 1536
  · have hks : Is.card ≤ 1 := Finset.card_le_one.mpr (by
      intro x hx y hy
      by_contra hxy
      have hx' := Finset.mem_filter.mp hx
      have hy' := Finset.mem_filter.mp hy
      have := noColl_cert (by decide) certB (h x hx'.1).1 (h x hx'.1).2.1 (by omega)
        (h y hy'.1).1 (h y hy'.1).2.1 (by omega) hxy (ℓ x) (ℓ y)
        (by have := hl3 x hx'.1; omega) (by have := hl3 y hy'.1; omega)
        (by rw [hrep x hx'.1, hrep y hy'.1])
      rw [hrep x hx'.1] at this
      exact absurd this (not_le.mpr hB))
    have hDs1 : ∏ r ∈ Is, ℓ r ≤ n + 1 :=
      (hDs.trans (Nat.pow_le_pow_right (by omega) hks)).trans_eq (pow_one _)
    rcases Nat.lt_or_ge n 144 with hn144 | hn144
    · refine le_trans (Nat.pow_le_pow_left ?_ 2) (table n (Finset.mem_Ico.mpr ⟨hn18, hn144⟩))
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.mul_le_mul hDs1 hDl))
        (Nat.add_le_add hks hkl)
    · refine le_trans (Nat.pow_le_pow_left ?_ 2) (crude_two n hn144)
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.mul_le_mul hDs1
        (hDl.trans (oddPr_prod_le _)))) (Nat.add_le_add hks
        (by have := oddPr_card_le (n / 6 + 1); omega))
  · have hn1536 : 1536 ≤ n := by
      have key : ∀ x y : ℕ, 2 ^ x ≤ y → x ≤ Nat.log 2 y :=
        fun x y hxy => Nat.le_log_of_pow_le one_lt_two hxy
      exact key 1536 p (Nat.le_of_not_lt hB)
    have hks : Is.card ≤ 17 := by
      rw [← lenB]
      refine le_trans (Finset.card_le_card ?_) (List.toFinset_card_le _)
      intro r hr
      have hr' := Finset.mem_filter.mp hr
      rw [List.mem_toFinset]
      exact mem_sieve (by decide) (h r hr'.1).1 (h r hr'.1).2.1 (by omega)
    have hDs17 : ∏ r ∈ Is, ℓ r ≤ (n + 1) ^ 17 := hDs.trans (Nat.pow_le_pow_right (by omega) hks)
    refine le_trans (Nat.pow_le_pow_left ?_ 2) (crude_three n hn1536)
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.mul_le_mul hDs17
      (hDl.trans (oddPr_prod_le _)))) (Nat.add_le_add hks
      (by have := oddPr_card_le (n / 6 + 1); omega))

end OddPerfect

#print axioms OddPerfect.repunit_rows_size
