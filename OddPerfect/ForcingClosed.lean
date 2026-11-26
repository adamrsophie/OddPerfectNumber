import OddPerfect.Euler
import OddPerfect.Abundancy
import OddPerfect.Zsigmondy
import OddPerfect.Pratt

/-!
# Forcing closed configurations (conjecture C1)

A forcing closed configuration keeps, of an odd perfect number, only four pieces of data:
primality of the nodes, forcing (every odd prime factor of a component divisor sum is a node),
Euler parity, and size (the product of component abundancies is at most two). The exact
valuation ledger is dropped.

* `ForcingClosed S e`: the configuration with support `S` and exponents `e`. It is decidable.
* `forcingClosed_of_oddPerfect`: an odd perfect number gives one, with product exactly two.
* `C1`: the statement that no forcing closed configuration exists. A `Prop`, never assumed.
* `oddPerfectConjecture_of_C1`: C1 implies the odd perfect number conjecture.
* `ForcingClosed.exists_mem_mod_eq_one`, `ForcingClosed.exponent_lt_max`: every exponent `e ≥ 2`
  of a node yields a node `r ≡ 1 (mod e + 1)`; so every exponent is below the largest node, and
  a fixed support carries only finitely many configurations.
* `ForcingClosed.reduce`: WLOG the special exponent is `1` and each ordinary exponent is `l - 1`
  with `l` an odd prime (rows of the reduced configuration divide the old rows).
* `ForcingClosed.three_mem`: closure and parity alone force `3 ∈ S` when every ordinary
  exponent `e` has `3 ∣ e + 1`.
* `ForcingClosed.exists_not_three_dvd_succ`: closure, parity and size forbid all ordinary
  exponents having `3 ∣ e + 1` (Steuerwald and McDaniel for configurations, no ledger), via
  the finite tree `ForcingClosed.false_of_sq`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- A forcing closed configuration with support `S` and exponents `e`:
1. every node is an odd prime with positive exponent;
2. Euler parity: one node `q ≡ 1 (mod 4)` has exponent `≡ 1 (mod 4)`, all other exponents
   are even;
3. forcing closure: every odd prime factor of `σ(s ^ e s)`, for `s ∈ S`, lies in `S`;
4. size: `∏_{s ∈ S} σ(s ^ e s) / s ^ e s ≤ 2`. -/
def ForcingClosed (S : Finset ℕ) (e : ℕ → ℕ) : Prop :=
  (∀ s ∈ S, s.Prime ∧ s ≠ 2 ∧ 0 < e s) ∧
  (∃ q ∈ S, q % 4 = 1 ∧ e q % 4 = 1 ∧ ∀ s ∈ S, s ≠ q → e s % 2 = 0) ∧
  (∀ s ∈ S, ∀ r ∈ (σ 1 (s ^ e s)).primeFactors, r ≠ 2 → r ∈ S) ∧
  ∏ s ∈ S, abundancy (s ^ e s) ≤ 2

instance (S : Finset ℕ) (e : ℕ → ℕ) : Decidable (ForcingClosed S e) := by
  unfold ForcingClosed; infer_instance

/-- Conjecture C1: no forcing closed configuration exists. A statement only; it is never
assumed in this project and may be false. -/
def C1 : Prop := ∀ (S : Finset ℕ) (e : ℕ → ℕ), ¬ ForcingClosed S e

/-- An odd perfect number gives a forcing closed configuration (its prime factors with their
exact exponents), and the product of the component abundancies is exactly two. -/
theorem forcingClosed_of_oddPerfect {N : ℕ} (h : OddPerfect N) :
    ForcingClosed N.primeFactors N.factorization ∧
      ∏ s ∈ N.primeFactors, abundancy (s ^ N.factorization s) = 2 := by
  have hprod : ∏ s ∈ N.primeFactors, abundancy (s ^ N.factorization s) = 2 := by
    rw [← abundancy_eq_prod_primeFactors h.ne_zero]
    exact (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
  refine ⟨⟨fun s hs => ?_, ?_, fun s hs r hr hr2 => ?_, hprod.le⟩, hprod⟩
  · have hsp := Nat.prime_of_mem_primeFactors hs
    have hsN := Nat.dvd_of_mem_primeFactors hs
    refine ⟨hsp, ?_, hsp.factorization_pos_of_dvd h.ne_zero hsN⟩
    rintro rfl
    exact h.not_two_dvd hsN
  · obtain ⟨q, hq, hqN, hq4, he4, hev⟩ := exists_special_prime h
    refine ⟨q, Nat.mem_primeFactors.mpr ⟨hq, hqN, h.ne_zero⟩, hq4, he4, fun s hs hsq => ?_⟩
    exact Nat.even_iff.mp (hev s (Nat.prime_of_mem_primeFactors hs) hsq)
  · have hrp := Nat.prime_of_mem_primeFactors hr
    have hrN := OPNStarter.force_prime h.perfect (Nat.prime_of_mem_primeFactors hs) rfl hrp hr2
      (Nat.dvd_of_mem_primeFactors hr)
    exact Nat.mem_primeFactors.mpr ⟨hrp, hrN, h.ne_zero⟩

/-- C1 implies the odd perfect number conjecture. -/
theorem oddPerfectConjecture_of_C1 (hC : C1) : OddPerfectConjecture :=
  fun _ h => hC _ _ (forcingClosed_of_oddPerfect h).1

namespace ForcingClosed

variable {S : Finset ℕ} {e : ℕ → ℕ}

/-- Closure in usable form: an odd prime dividing a row lies in the support. -/
theorem mem_of_dvd (hF : ForcingClosed S e) {s r : ℕ} (hs : s ∈ S) (hr : r.Prime)
    (hr2 : r ≠ 2) (hd : r ∣ σ 1 (s ^ e s)) : r ∈ S := by
  have hsp := (hF.1 s hs).1
  refine hF.2.2.1 s hs r (Nat.mem_primeFactors.mpr ⟨hr, hd, ?_⟩) hr2
  exact (sigma_pos 1 _ (pow_ne_zero _ hsp.ne_zero)).ne'

/-- Primitive divisors: if a node `s` has exponent `e s ≥ 2`, some node `r` has
`r ≡ 1 (mod e s + 1)`, with `s` of order exactly `e s + 1` modulo `r`. -/
theorem exists_mem_mod_eq_one (hF : ForcingClosed S e) {s : ℕ} (hs : s ∈ S)
    (he : 2 ≤ e s) :
    ∃ r ∈ S, orderOf (s : ZMod r) = e s + 1 ∧ r % (e s + 1) = 1 := by
  obtain ⟨hsp, hs2, -⟩ := hF.1 s hs
  obtain ⟨r, hr, hdiv, ho, hmod⟩ :=
    exists_prime_dvd_sigma_orderOf_eq (d := e s + 1) hsp (by have := hsp.two_le; omega)
      (by omega) dvd_rfl
  have hr2 : r ≠ 2 := by
    rintro rfl
    rw [Nat.mod_eq_of_lt (by omega : 2 < e s + 1)] at hmod
    omega
  exact ⟨r, hF.mem_of_dvd hs hr hr2 hdiv, ho, hmod⟩

/-- Every exponent of a forcing closed configuration is smaller than some node:
`e s + 2 ≤ r` for some `r ∈ S`. (For `e s = 1` take `r = s ≥ 3`.) -/
theorem exists_mem_exponent_add_two_le (hF : ForcingClosed S e) {s : ℕ} (hs : s ∈ S) :
    ∃ r ∈ S, e s + 2 ≤ r := by
  by_cases he : 2 ≤ e s
  · obtain ⟨r, hr, -, hmod⟩ := hF.exists_mem_mod_eq_one hs he
    refine ⟨r, hr, ?_⟩
    by_contra hlt
    rcases Nat.lt_or_ge r (e s + 1) with h1 | h1
    · rw [Nat.mod_eq_of_lt h1] at hmod
      have := (hF.1 r hr).1.two_le
      omega
    · have : r = e s + 1 := by omega
      rw [this, Nat.mod_self] at hmod
      omega
  · obtain ⟨hsp, hs2, hpos⟩ := hF.1 s hs
    have := hsp.two_le
    exact ⟨s, hs, by omega⟩

/-- Finiteness for a fixed support: every exponent is below the largest node. -/
theorem exponent_lt_max (hF : ForcingClosed S e) {s : ℕ} (hs : s ∈ S) :
    e s + 2 ≤ S.max' ⟨s, hs⟩ := by
  obtain ⟨r, hr, hle⟩ := hF.exists_mem_exponent_add_two_le hs
  exact hle.trans (S.le_max' r hr)

/-- Row divisibility: if `a + 1 ∣ b + 1` then `σ(p ^ a) ∣ σ(p ^ b)`. -/
theorem sigma_prime_pow_dvd_of_dvd {p a b : ℕ} (hp : p.Prime) (h : a + 1 ∣ b + 1) :
    σ 1 (p ^ a) ∣ σ 1 (p ^ b) := by
  have h1 := Nat.pow_sub_one_dvd_pow_sub_one p h
  rw [← sigma_prime_pow_mul_pred hp a, ← sigma_prime_pow_mul_pred hp b] at h1
  exact Nat.dvd_of_mul_dvd_mul_right (by have := hp.two_le; omega) h1

/-- Shrinking exponents along row divisibility preserves forcing closure: if every new
exponent `e' s` is positive, keeps the parity pattern, and has `e' s + 1 ∣ e s + 1`, the new
configuration is again forcing closed (rows divide old rows; abundancies drop). -/
theorem of_dvd (hF : ForcingClosed S e) {e' : ℕ → ℕ} (q : ℕ) (hq : q ∈ S) (hq4 : q % 4 = 1)
    (he'q : e' q % 4 = 1) (hev : ∀ s ∈ S, s ≠ q → e' s % 2 = 0)
    (hpos : ∀ s ∈ S, 0 < e' s) (hdvd : ∀ s ∈ S, e' s + 1 ∣ e s + 1) :
    ForcingClosed S e' := by
  have hle : ∀ s ∈ S, e' s ≤ e s := fun s hs =>
    Nat.le_of_lt_succ (Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.succ_pos _) (hdvd s hs)) |>
      fun h => by omega)
  refine ⟨fun s hs => ⟨(hF.1 s hs).1, (hF.1 s hs).2.1, hpos s hs⟩, ⟨q, hq, hq4, he'q, hev⟩,
    fun s hs r hr hr2 => ?_, ?_⟩
  · have hsp := (hF.1 s hs).1
    exact hF.mem_of_dvd hs (Nat.prime_of_mem_primeFactors hr) hr2
      ((Nat.dvd_of_mem_primeFactors hr).trans (sigma_prime_pow_dvd_of_dvd hsp (hdvd s hs)))
  · refine le_trans (Finset.prod_le_prod₀ (fun s _ => ?_) fun s hs =>
      abundancy_prime_pow_mono (hF.1 s hs).1 (hle s hs)) hF.2.2.2
    unfold abundancy
    positivity

/-- The reduced exponents: `1` at the special node `q`, and `l - 1` at every other node,
where `l` is the least prime factor of `e s + 1`. -/
def reduceExp (q : ℕ) (e : ℕ → ℕ) (s : ℕ) : ℕ := if s = q then 1 else (e s + 1).minFac - 1

/-- Reduction: every forcing closed configuration has a reduced one on the same support, with
special exponent `1` and every ordinary exponent of the form `l - 1`, `l` an odd prime.
It also returns the special node `q` of the original configuration with its parity data.
So C1 is equivalent to C1 for reduced configurations. -/
theorem reduce (hF : ForcingClosed S e) :
    ∃ q ∈ S, q % 4 = 1 ∧ e q % 4 = 1 ∧ (∀ s ∈ S, s ≠ q → e s % 2 = 0) ∧
      ForcingClosed S (reduceExp q e) ∧ reduceExp q e q = 1 ∧
      ∀ s ∈ S, s ≠ q → (reduceExp q e s + 1).Prime ∧ reduceExp q e s + 1 ≠ 2 := by
  obtain ⟨q, hq, hq4, he4, hev⟩ := hF.2.1
  -- facts about an ordinary node
  have hord : ∀ s ∈ S, s ≠ q → (e s + 1).minFac.Prime ∧ (e s + 1).minFac ≠ 2 ∧
      (e s + 1).minFac ∣ e s + 1 := by
    intro s hs hsq
    have he0 := (hF.1 s hs).2.2
    have hes := hev s hs hsq
    have hne1 : e s + 1 ≠ 1 := by omega
    refine ⟨Nat.minFac_prime hne1, fun h2 => ?_, Nat.minFac_dvd _⟩
    have := Nat.minFac_dvd (e s + 1)
    rw [h2] at this
    omega
  have hred : ∀ s ∈ S, s ≠ q → reduceExp q e s + 1 = (e s + 1).minFac := by
    intro s hs hsq
    have := (hord s hs hsq).1.two_le
    simp only [reduceExp, if_neg hsq]
    omega
  refine ⟨q, hq, hq4, he4, hev, hF.of_dvd q hq hq4 (by simp [reduceExp]) (fun s hs hsq => ?_)
    (fun s hs => ?_) (fun s hs => ?_), by simp [reduceExp], fun s hs hsq => ?_⟩
  · obtain ⟨hl, hl2, -⟩ := hord s hs hsq
    have h := hred s hs hsq
    have hodd := hl.eq_one_or_self_of_dvd 2
    rcases hl.eq_two_or_odd with h' | h'
    · exact absurd h' hl2
    · omega
  · by_cases hsq : s = q
    · subst hsq; simp [reduceExp]
    · have := hred s hs hsq
      have := (hord s hs hsq).1.two_le
      have := (hord s hs hsq).2.1
      omega
  · by_cases hsq : s = q
    · subst hsq
      simp only [reduceExp]
      exact even_iff_two_dvd.mp (by rw [Nat.even_add_one, Nat.not_even_iff_odd, Nat.odd_iff]; omega)
    · rw [hred s hs hsq]; exact (hord s hs hsq).2.2
  · rw [hred s hs hsq]; exact ⟨(hord s hs hsq).1, (hord s hs hsq).2.1⟩

/-- `σ(s ^ 2) = s ^ 2 + s + 1`. -/
private lemma sigma_sq {s : ℕ} (hs : s.Prime) : σ 1 (s ^ 2) = s ^ 2 + s + 1 := by
  rw [sigma_one_apply_prime_pow hs]
  simp [Finset.sum_range_succ]
  ring

/-- Closure and parity alone (no size): if every ordinary exponent `e s` has `3 ∣ e s + 1`
(for example all ordinary exponents equal `2`), then `3` is a node. Proof: otherwise every
ordinary node is `≢ 1 (mod 3)`, so every prime factor of `s ^ 2 + s + 1` is the special node `q`;
an odd prime `s ∣ q + 1` then gives `s ^ 2 + s + 1 = q`, so `s ∣ 2`. -/
theorem three_mem (hF : ForcingClosed S e) (h3 : ∀ s ∈ S, e s % 2 = 0 → 3 ∣ e s + 1) :
    3 ∈ S := by
  by_contra h3S
  obtain ⟨q, hq, hq4, he4, hev⟩ := hF.2.1
  obtain ⟨hqp, -, -⟩ := hF.1 q hq
  -- rows of length three are available at every ordinary node
  have hrow : ∀ s ∈ S, s ≠ q → ∀ r, r.Prime → r ∣ s ^ 2 + s + 1 → r ∈ S := by
    intro s hs hsq r hr hd
    have hsp := (hF.1 s hs).1
    have hd' : r ∣ σ 1 (s ^ e s) :=
      (sigma_sq hsp ▸ hd).trans (sigma_prime_pow_dvd_of_dvd hsp (h3 s hs (hev s hs hsq)))
    refine hF.mem_of_dvd hs hr ?_ hd'
    rintro rfl
    have : 2 ∣ s ^ 2 + s + 1 := hd
    have : 2 ∣ s * (s + 1) := Nat.even_mul_succ_self s |>.two_dvd
    have : s ^ 2 + s + 1 = s * (s + 1) + 1 := by ring
    omega
  -- an ordinary node is not `1 (mod 3)`
  have hmod : ∀ s ∈ S, s ≠ q → s % 3 ≠ 1 := by
    intro s hs hsq h1
    refine h3S (hrow s hs hsq 3 Nat.prime_three ?_)
    have : (s ^ 2 + s + 1) % 3 = 0 := by
      rw [Nat.add_mod, Nat.add_mod (s ^ 2), Nat.pow_mod, h1]
    omega
  -- every prime factor of an ordinary row of length three is `q`
  have honly : ∀ s ∈ S, s ≠ q → ∀ r, r.Prime → r ∣ s ^ 2 + s + 1 → r = q := by
    intro s hs hsq r hr hd
    have hrS := hrow s hs hsq r hr hd
    have hsp := (hF.1 s hs).1
    rcases prime_dvd_sigma_prime_pow_of_prime_length (l := 3) hsp hr Nat.prime_three
      (by rw [show 3 - 1 = 2 from rfl, sigma_sq hsp]; exact hd) with h | h
    · exact absurd (h ▸ hrS) h3S
    · by_contra hrq
      exact hmod r hrS hrq h
  -- an odd prime factor `s` of `q + 1`
  have hq5 : 5 ≤ q := by
    have := hqp.two_le
    rcases (by omega : q = 1 ∨ q = 5 ∨ 5 ≤ q) with h | h | h
    · omega
    · omega
    · exact h
  obtain ⟨m, hm⟩ : ∃ m, q + 1 = 2 * m := ⟨(q + 1) / 2, by omega⟩
  have hm1 : m ≠ 1 := by omega
  set s := m.minFac with hs_def
  have hsp : s.Prime := Nat.minFac_prime hm1
  have hsm : s ∣ m := Nat.minFac_dvd m
  have hmodd : m % 2 = 1 := by omega
  have hs2 : s ≠ 2 := by
    intro h; rw [h] at hsm; omega
  have hsq1 : s ∣ σ 1 (q ^ e q) := by
    have : σ 1 (q ^ 1) = q + 1 := by
      rw [sigma_one_apply_prime_pow hqp]; simp [Finset.sum_range_succ]; ring
    refine (this ▸ hm ▸ Dvd.dvd.mul_left hsm 2).trans (sigma_prime_pow_dvd_of_dvd hqp ?_)
    exact Nat.dvd_of_mod_eq_zero (by omega)
  have hsS := hF.mem_of_dvd hq hsp hs2 hsq1
  have hslt : s < q := by
    have := Nat.le_of_dvd (by omega) hsm
    omega
  have hsq : s ≠ q := hslt.ne
  -- `s ^ 2 + s + 1 = q`
  set n := s ^ 2 + s + 1 with hn
  have hqn : q ∣ n := by
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by
      have := hsp.two_le; rw [hn]; nlinarith)
    exact honly s hsS hsq r hr hrd ▸ hrd
  obtain ⟨k, hk⟩ := hqn
  have hnlt : n < q * q := by
    have : s + 1 ≤ q := hslt
    rw [hn]; nlinarith
  have hk1 : k = 1 := by
    have hklt : k < q := by
      by_contra hc
      have := Nat.mul_le_mul_left q (Nat.le_of_not_lt hc)
      omega
    by_contra hk1
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hk1
    have hrn : r ∣ n := hk ▸ Dvd.dvd.mul_left hrd q
    have := honly s hsS hsq r hr hrn
    have hk0 : k ≠ 0 := by rintro rfl; rw [hn] at hk; simp at hk
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hrd
    omega
  rw [hk1, mul_one] at hk
  -- `s ∣ q + 1 = s ^ 2 + s + 2`, so `s ∣ 2`
  have hsd : s ∣ q + 1 := hm ▸ Dvd.dvd.mul_left hsm 2
  rw [← hk, hn, show s ^ 2 + s + 1 + 1 = s * (s + 1) + 2 by ring] at hsd
  have h2 := (Nat.dvd_add_right (Dvd.intro _ rfl)).mp hsd
  have := Nat.le_of_dvd (by norm_num) h2
  have := hsp.two_le
  omega

/-- The abundancy of `p ^ k` as an explicit rational. -/
def geomQ (p k : ℕ) : ℚ := (∑ i ∈ Finset.range (k + 1), (p : ℚ) ^ i) / (p : ℚ) ^ k

theorem abundancy_eq_geomQ {p k : ℕ} (hp : p.Prime) : abundancy (p ^ k) = geomQ p k := by
  unfold abundancy geomQ
  rw [sigma_one_apply_prime_pow hp]
  push_cast
  rfl

/-- Size along a duplicate free list of nodes. -/
theorem prod_list_le (hF : ForcingClosed S e) {L : List ℕ} (hnd : L.Nodup)
    (hL : ∀ p ∈ L, p ∈ S) : (L.map fun p => geomQ p (e p)).prod ≤ 2 := by
  have hsub : L.toFinset ⊆ S := fun p hp => hL p (List.mem_toFinset.mp hp)
  have h1 : (L.map fun p => geomQ p (e p)).prod = ∏ p ∈ L.toFinset, abundancy (p ^ e p) := by
    rw [List.prod_toFinset _ hnd]
    congr 1
    exact List.map_congr_left fun p hp => (abundancy_eq_geomQ (hF.1 p (hL p hp)).1).symm
  rw [h1]
  have h1le : ∀ p ∈ S, 1 ≤ abundancy (p ^ e p) := fun p hp => by
    have h := abundancy_prime_pow_mono (hF.1 p hp).1 (Nat.zero_le (e p))
    simpa [abundancy] using h
  refine le_trans (Finset.prod_le_prod_of_subset_of_one_le₀ hsub
    (fun p hp => zero_le_one.trans (h1le p (hsub hp))) fun p hp _ => h1le p hp) hF.2.2.2

private lemma sigma_prime_one {q : ℕ} (hq : q.Prime) : σ 1 (q ^ 1) = q + 1 := by
  rw [sigma_one_apply_prime_pow hq]; simp [Finset.sum_range_succ]; ring

private lemma pr_3169 : Nat.Prime 3169 :=
  Pratt.prime_of_checkPrime (c := [(3169, 7, [2, 2, 2, 2, 2, 3, 3, 11])]) (by decide +kernel)
private lemma pr_5419 : Nat.Prime 5419 :=
  Pratt.prime_of_checkPrime (c := [(5419, 3, [2, 3, 3, 7, 43])]) (by decide +kernel)
private lemma pr_1674289 : Nat.Prime 1674289 :=
  Pratt.prime_of_checkPrime (c := [(1674289, 26, [2, 2, 2, 2, 3, 3, 7, 11, 151])])
    (by decide +kernel)
private lemma pr_3348577 : Nat.Prime 3348577 :=
  Pratt.prime_of_checkPrime (c := [(3348577, 13, [2, 2, 2, 2, 2, 3, 3, 7, 11, 151])])
    (by decide +kernel)
private lemma pr_934415109937 : Nat.Prime 934415109937 :=
  Pratt.prime_of_checkPrime (c := [(12979, 2, [2, 3, 3, 7, 103]),
    (934415109937, 15, [2, 2, 2, 2, 3, 3, 7, 11, 43, 151, 12979])]) (by decide +kernel)
private lemma pr_3737657091169 : Nat.Prime 3737657091169 :=
  Pratt.prime_of_checkPrime (c := [(4519, 3, [2, 3, 3, 251]),
    (3737657091169, 37, [2, 2, 2, 2, 2, 3, 3, 7, 11, 13, 19, 151, 4519])]) (by decide +kernel)

/-- Closure and size alone, for a reduced configuration with all ordinary exponents `2`
and `3` a node: a finite tree branching on which node is special; every leaf has a list of
forced nodes whose abundancies multiply to more than two. -/
theorem false_of_sq (hF : ForcingClosed S e) {q : ℕ} (hq : q ∈ S) (hq4 : q % 4 = 1)
    (heq : e q = 1) (h2 : ∀ s ∈ S, s ≠ q → e s = 2) (h3 : 3 ∈ S) : False := by
  have m2 : ∀ s r : ℕ, s ∈ S → s ≠ q → r.Prime → r ≠ 2 → r ∣ s ^ 2 + s + 1 → r ∈ S := by
    intro s r hs hsq hr hr2 hd
    refine hF.mem_of_dvd hs hr hr2 ?_
    rw [h2 s hs hsq, sigma_sq (hF.1 s hs).1]; exact hd
  have m1 : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ q + 1 → r ∈ S := by
    intro r hr hr2 hd
    refine hF.mem_of_dvd hq hr hr2 ?_
    rw [heq, sigma_prime_one (hF.1 q hq).1]; exact hd
  have n3 : ∀ s : ℕ, s % 4 = 3 → s ≠ q := by rintro s hs rfl; omega
  -- size at a leaf containing the special node
  have leafq : ∀ L : List ℕ, (q :: L).Nodup → (∀ p ∈ L, p ∈ S) →
      geomQ q 1 * (L.map fun p => geomQ p 2).prod ≤ 2 := by
    intro L hnd hL
    have h := hF.prod_list_le hnd (by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hq
      · exact hL p hp)
    rw [List.map_cons, List.prod_cons, heq] at h
    have hm : (L.map fun p => geomQ p (e p)) = L.map fun p => geomQ p 2 :=
      List.map_congr_left fun p hp => by
        rw [h2 p (hL p hp) (fun hpq => (List.nodup_cons.mp hnd).1 (hpq ▸ hp))]
    rwa [hm] at h
  -- size at a leaf of ordinary nodes
  have leaf0 : ∀ L : List ℕ, L.Nodup → (∀ p ∈ L, p ∈ S) → (∀ p ∈ L, p ≠ q) →
      (L.map fun p => geomQ p 2).prod ≤ 2 := by
    intro L hnd hL hne
    have h := hF.prod_list_le hnd hL
    have hm : (L.map fun p => geomQ p (e p)) = L.map fun p => geomQ p 2 :=
      List.map_congr_left fun p hp => by rw [h2 p (hL p hp) (hne p hp)]
    rwa [hm] at h
  have h13 := m2 3 13 h3 (n3 3 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
  by_cases c13 : 13 = q
  · subst c13
    have h7 := m1 7 (by norm_num) (by norm_num) (by norm_num)
    have h19 := m2 7 19 h7 (n3 7 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    have h127 := m2 19 127 h19 (n3 19 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    have h5419 := m2 127 5419 h127 (n3 127 (by norm_num)) pr_5419 (by norm_num) (by norm_num)
    have h31 := m2 5419 31 h5419 (n3 5419 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    have h313 := m2 5419 313 h5419 (n3 5419 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num)
    have h331 := m2 31 331 h31 (n3 31 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    have := leafq [3, 7, 19, 31, 127, 313, 331, 5419] (by decide) (by simp [*])
    norm_num [geomQ, Finset.sum_range_succ] at this
  have h61 := m2 13 61 h13 c13 (by norm_num) (by norm_num) (by norm_num)
  by_cases c61 : 61 = q
  · subst c61
    have h31 := m1 31 (by norm_num) (by norm_num) (by norm_num)
    have h331 := m2 31 331 h31 (n3 31 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    have h7 := m2 331 7 h331 (n3 331 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    have h19 := m2 7 19 h7 (n3 7 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    have := leafq [3, 7, 13, 19, 31, 331] (by decide) (by simp [*])
    norm_num [geomQ, Finset.sum_range_succ] at this
  have h97 := m2 61 97 h61 c61 (by norm_num) (by norm_num) (by norm_num)
  by_cases c97 : 97 = q
  · subst c97
    have h7 := m1 7 (by norm_num) (by norm_num) (by norm_num)
    have h19 := m2 7 19 h7 (n3 7 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    have h127 := m2 19 127 h19 (n3 19 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    have h5419 := m2 127 5419 h127 (n3 127 (by norm_num)) pr_5419 (by norm_num) (by norm_num)
    have h31 := m2 5419 31 h5419 (n3 5419 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    have h331 := m2 31 331 h31 (n3 31 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    have := leafq [3, 7, 13, 19, 31, 61, 127, 331] (by decide) (by simp [*])
    norm_num [geomQ, Finset.sum_range_succ] at this
  have h3169 := m2 97 3169 h97 c97 pr_3169 (by norm_num) (by norm_num)
  by_cases c3169 : 3169 = q
  · subst c3169
    have h5 := m1 5 (by norm_num) (by norm_num) (by norm_num)
    have h31 := m2 5 31 h5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have := leafq [3, 5, 13, 31, 61, 97] (by decide) (by simp [*])
    norm_num [geomQ, Finset.sum_range_succ] at this
  have h3348577 := m2 3169 3348577 h3169 c3169 pr_3348577 (by norm_num) (by norm_num)
  by_cases c3348577 : 3348577 = q
  · subst c3348577
    have h1674289 := m1 1674289 pr_1674289 (by norm_num) (by norm_num)
    have hbig := m2 1674289 934415109937 h1674289 (by norm_num) pr_934415109937 (by norm_num)
      (by norm_num)
    have h79 := m2 934415109937 79 hbig (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h127 := m2 934415109937 127 hbig (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    have h7 := m2 79 7 h79 (n3 79 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    have h43 := m2 79 43 h79 (n3 79 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    have h19 := m2 7 19 h7 (n3 7 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    have := leafq [3, 7, 13, 19, 43, 61, 79, 97, 127] (by decide) (by simp [*])
    norm_num [geomQ, Finset.sum_range_succ] at this
  have hbig := m2 3348577 3737657091169 h3348577 c3348577 pr_3737657091169 (by norm_num)
    (by norm_num)
  by_cases cbig : 3737657091169 = q
  · subst cbig
    have h5 := m1 5 (by norm_num) (by norm_num) (by norm_num)
    have h31 := m2 5 31 h5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have := leafq [3, 5, 13, 31, 61, 97] (by decide) (by simp [*])
    norm_num [geomQ, Finset.sum_range_succ] at this
  have h181 := m2 3737657091169 181 hbig cbig (by norm_num) (by norm_num) (by norm_num)
  by_cases c181 : 181 = q
  · subst c181
    have h7 := m1 7 (by norm_num) (by norm_num) (by norm_num)
    have h19 := m2 7 19 h7 (n3 7 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    have h127 := m2 19 127 h19 (n3 19 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    have h5419 := m2 127 5419 h127 (n3 127 (by norm_num)) pr_5419 (by norm_num) (by norm_num)
    have h31 := m2 5419 31 h5419 (n3 5419 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    have h331 := m2 31 331 h31 (n3 31 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    have := leafq [3, 7, 13, 19, 31, 61, 97, 127, 331] (by decide) (by simp [*])
    norm_num [geomQ, Finset.sum_range_succ] at this
  have h79 := m2 181 79 h181 c181 (by norm_num) (by norm_num) (by norm_num)
  have h7 := m2 79 7 h79 (n3 79 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
  have h43 := m2 79 43 h79 (n3 79 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
  have h19 := m2 7 19 h7 (n3 7 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
  have := leaf0 [3, 7, 13, 19, 43, 61, 79, 97, 181] (by decide) (by simp [*]) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first | assumption | exact n3 _ (by norm_num))
  norm_num [geomQ, Finset.sum_range_succ] at this

/-- **McDaniel and Steuerwald for forcing closed configurations.** In every forcing closed
configuration some ordinary exponent `e s` (even) has `3 ∤ e s + 1`. In particular the
ordinary exponents cannot all equal `2` (Steuerwald) and cannot all be `≡ 2 (mod 3)`
(McDaniel). The proof uses only closure, parity and size: no valuation ledger. -/
theorem exists_not_three_dvd_succ (hF : ForcingClosed S e) :
    ∃ s ∈ S, e s % 2 = 0 ∧ ¬ 3 ∣ e s + 1 := by
  by_contra hcon
  have hall : ∀ s ∈ S, e s % 2 = 0 → 3 ∣ e s + 1 := fun s hs hs2 => by
    by_contra h
    exact hcon ⟨s, hs, hs2, h⟩
  obtain ⟨q, hq, hq4, -, hev, hR, hRq, -⟩ := hF.reduce
  have hR2 : ∀ s ∈ S, s ≠ q → reduceExp q e s = 2 := by
    intro s hs hsq
    have h3d := hall s hs (hev s hs hsq)
    have h1 : e s + 1 ≠ 1 := by have := (hF.1 s hs).2.2; omega
    have hp := Nat.minFac_prime h1
    have hle := Nat.minFac_le_of_dvd (by norm_num) h3d
    have hne2 : (e s + 1).minFac ≠ 2 := by
      intro h2'
      have := Nat.minFac_dvd (e s + 1)
      rw [h2'] at this
      have := hev s hs hsq
      omega
    have := hp.two_le
    simp only [reduceExp, if_neg hsq]
    omega
  have h3 := hR.three_mem (fun s hs hs2 => by
    by_cases hsq : s = q
    · subst hsq; rw [hRq] at hs2; omega
    · rw [hR2 s hs hsq])
  exact hR.false_of_sq hq hq4 hRq hR2 h3

end ForcingClosed

/-- Consequence for odd perfect numbers, through forcing closed configurations: some ordinary
exponent `e` has `3 ∤ e + 1`. This recovers Steuerwald and McDaniel. -/
theorem exists_exponent_not_three_dvd_succ {N : ℕ} (h : OddPerfect N) :
    ∃ p ∈ N.primeFactors, N.factorization p % 2 = 0 ∧ ¬ 3 ∣ N.factorization p + 1 :=
  (forcingClosed_of_oddPerfect h).1.exists_not_three_dvd_succ

end OddPerfect

#print axioms OddPerfect.forcingClosed_of_oddPerfect
#print axioms OddPerfect.oddPerfectConjecture_of_C1
#print axioms OddPerfect.ForcingClosed.mem_of_dvd
#print axioms OddPerfect.ForcingClosed.exists_mem_mod_eq_one
#print axioms OddPerfect.ForcingClosed.exists_mem_exponent_add_two_le
#print axioms OddPerfect.ForcingClosed.exponent_lt_max
#print axioms OddPerfect.ForcingClosed.sigma_prime_pow_dvd_of_dvd
#print axioms OddPerfect.ForcingClosed.of_dvd
#print axioms OddPerfect.ForcingClosed.reduce
#print axioms OddPerfect.ForcingClosed.three_mem
#print axioms OddPerfect.ForcingClosed.abundancy_eq_geomQ
#print axioms OddPerfect.ForcingClosed.prod_list_le
#print axioms OddPerfect.ForcingClosed.false_of_sq
#print axioms OddPerfect.ForcingClosed.exists_not_three_dvd_succ
#print axioms OddPerfect.exists_exponent_not_three_dvd_succ
