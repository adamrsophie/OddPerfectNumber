import OddPerfect.Valuation
import OddPerfect.Phi3
import OddPerfect.SpecialPrime
import OddPerfect.ExcessSeven

/-!
# An exponent budget when every exception is 2 modulo 3

Let `N` be an odd perfect number with special prime `q` of exponent `a`. Call a prime factor
`r ≠ q` of `N` an exception when its exponent is not 2 (so it is even and at least 4), let `H`
be the set of exceptions (`budgetExceptions`), `h = #H` and `V = ∑_{r ∈ H} v_r(N)`. Assume
that every exception is 2 modulo 3.

A prime of exponent 2 sends nothing to `H`: every prime factor of `σ(p ^ 2) = p ^ 2 + p + 1`
is 3 or 1 modulo 3. So the exponent of each `r ∈ H` is fed by the rows `p ∈ H ∪ {q}`, `p ≠ r`.
For one row, with `d` the order of `p` modulo `r`, the valuation `v_r(σ(p ^ e))` is 0 when
`d ∤ e + 1`, is `v_r(e + 1)` when `d = 1`, and is `v_r(p ^ d - 1) + v_r(e + 1)` otherwise
(`padicValNat_sigma_prime_pow_row`). Summing over the columns `r ∈ H` and using
`(e + 1) ^ 4 ≤ 5 ^ e` for the exponents `e ≥ 4` of the rows in `H` gives
`5 ^ (3 * V) ≤ 5 ^ (4 * C) * A ^ 4` (`five_pow_three_mul_le_budget`), where `C`
(`budgetC`) collects the terms `v_r(p ^ d - 1)` and `A` (`budgetA`) is the part of `a + 1`
made of primes in `H`.

Under explicit valuation hypotheses (no exception divides `a + 1`, and no
`r ^ 2 ∣ p ^ (r - 1) - 1` for a row `p` and an exception `r ≠ p`) this gives
`3 * T + 3 * h ≤ 2 * h ^ 2` for the total excess `T`, hence `5 ≤ h` by the landed bound
`7 ≤ T` (`five_le_card_budgetExceptions`).

Restricted family result with explicit valuation hypotheses; whether this is in the literature
was not verified. The hypotheses cannot be checked without knowing the primes of `N`, and the
total excess is not bounded in general by this argument. The odd perfect number conjecture is
open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The base term of the row `p` at the column `r` for the exponent `e`: with `d` the order of
`p` modulo `r`, it is `v_r(p ^ d - 1)` when `1 < d` and `d ∣ e + 1`, and 0 otherwise. -/
noncomputable def budgetBase (p r e : ℕ) : ℕ :=
  if 1 < orderOf (p : ZMod r) ∧ orderOf (p : ZMod r) ∣ e + 1 then
    padicValNat r (p ^ orderOf (p : ZMod r) - 1)
  else 0

/-- `r ∣ x - 1` exactly when `x` is 1 in `ZMod r` (for `x ≥ 1`). -/
private theorem dvd_sub_one_iff' {r x : ℕ} (hx : 1 ≤ x) : r ∣ x - 1 ↔ (x : ZMod r) = 1 := by
  rw [← Nat.modEq_iff_dvd' hx, ← ZMod.natCast_eq_natCast_iff, Nat.cast_one, eq_comm]

/-- The order of a prime `p` modulo a different prime `r` divides `r - 1`. -/
private theorem orderOf_dvd_sub_one {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) :
    orderOf (p : ZMod r) ∣ r - 1 := by
  have : Fact r.Prime := ⟨hr⟩
  refine ZMod.orderOf_dvd_card_sub_one fun h0 => hpr ?_
  exact ((Nat.prime_dvd_prime_iff_eq hr hp).mp ((ZMod.natCast_eq_zero_iff _ _).mp h0)).symm

/-- One row. Let `p` and `r` be different primes with `r` odd and `d` the order of `p` modulo
`r`. If `d ∤ e + 1`, then `v_r(σ(p ^ e)) = 0`; if `d = 1`, then `v_r(σ(p ^ e)) = v_r(e + 1)`;
if `1 < d` and `d ∣ e + 1`, then `v_r(σ(p ^ e)) = v_r(p ^ d - 1) + v_r(e + 1)`. -/
theorem padicValNat_sigma_prime_pow_row {p r e : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hr2 : r ≠ 2) (hpr : p ≠ r) :
    (¬ orderOf (p : ZMod r) ∣ e + 1 → padicValNat r (σ 1 (p ^ e)) = 0) ∧
    (orderOf (p : ZMod r) = 1 → padicValNat r (σ 1 (p ^ e)) = padicValNat r (e + 1)) ∧
    (1 < orderOf (p : ZMod r) → orderOf (p : ZMod r) ∣ e + 1 →
      padicValNat r (σ 1 (p ^ e)) =
        padicValNat r (p ^ orderOf (p : ZMod r) - 1) + padicValNat r (e + 1)) := by
  have : Fact r.Prime := ⟨hr⟩
  refine ⟨padicValNat_sigma_prime_pow_of_not_orderOf_dvd hp hr, fun h1 => ?_, fun h1 hd => ?_⟩
  · refine padicValNat_sigma_prime_pow_of_dvd_pred hp hr hr2 ?_
    rw [dvd_sub_one_iff' hp.one_lt.le]
    exact orderOf_eq_one_iff.mp h1
  · rw [padicValNat_sigma_prime_pow_of_orderOf_dvd hp hr hr2 hpr h1 hd]
    congr 1
    set d := orderOf (p : ZMod r) with hdd
    have hdr : d ∣ r - 1 := orderOf_dvd_sub_one hp hr hpr
    have hdle : d ≤ r - 1 := Nat.le_of_dvd (by have := hr.two_le; omega) hdr
    have hrd : ¬ r ∣ d := fun h => by have := Nat.le_of_dvd (by omega) h; omega
    obtain ⟨k, hk⟩ := hd
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk
    rw [hk, Nat.mul_div_cancel_left _ (by omega), padicValNat.mul (by omega) hk0,
      padicValNat.eq_zero_of_not_dvd hrd, zero_add]

/-- One row, combined form: `v_r(σ(p ^ e)) ≤ budgetBase p r e + v_r(e + 1)`. -/
theorem padicValNat_sigma_prime_pow_le_budgetBase {p r e : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hr2 : r ≠ 2) (hpr : p ≠ r) :
    padicValNat r (σ 1 (p ^ e)) ≤ budgetBase p r e + padicValNat r (e + 1) := by
  obtain ⟨h0, h1, h2⟩ := padicValNat_sigma_prime_pow_row (e := e) hp hr hr2 hpr
  unfold budgetBase
  split_ifs with hc
  · rw [h2 hc.1 hc.2]
  · rw [zero_add]
    by_cases hd : orderOf (p : ZMod r) ∣ e + 1
    · have hd1 : orderOf (p : ZMod r) = 1 := by
        have : orderOf (p : ZMod r) ≠ 0 := fun h => by rw [h] at hd; simp at hd
        have : ¬ 1 < orderOf (p : ZMod r) := fun h => hc ⟨h, hd⟩
        omega
      rw [h1 hd1]
    · rw [h0 hd]; exact Nat.zero_le _

/-- The exceptions of `N` with respect to `q`: prime factors `r ≠ q` whose exponent is not 2. -/
def budgetExceptions (N q : ℕ) : Finset ℕ :=
  N.primeFactors.filter fun r => r ≠ q ∧ N.factorization r ≠ 2

/-- The base budget `C = ∑_{r ∈ H} ∑_{p ∈ (H ∪ {q}) \ {r}} budgetBase p r v_p(N)`, with
`H = budgetExceptions N q`. -/
noncomputable def budgetC (N q : ℕ) : ℕ :=
  ∑ r ∈ budgetExceptions N q, ∑ p ∈ (insert q (budgetExceptions N q)).erase r,
    budgetBase p r (N.factorization p)

/-- The part of `v_q(N) + 1` made of exceptions: `A = ∏_{r ∈ H} r ^ v_r(v_q(N) + 1)`. -/
def budgetA (N q : ℕ) : ℕ :=
  ∏ r ∈ budgetExceptions N q, r ^ padicValNat r (N.factorization q + 1)

/-- For `n ≠ 0` and any finset `S`, `∏_{r ∈ S} r ^ v_r(n) ≤ n`. -/
private theorem prod_pow_factorization_le {n : ℕ} (hn : n ≠ 0) (S : Finset ℕ) :
    ∏ r ∈ S, r ^ n.factorization r ≤ n := by
  calc ∏ r ∈ S, r ^ n.factorization r = ∏ r ∈ S ∩ n.primeFactors, r ^ n.factorization r := by
        refine (Finset.prod_subset Finset.inter_subset_left fun x hx hx' => ?_).symm
        have hx'' : x ∉ n.primeFactors := fun h => hx' (Finset.mem_inter.mpr ⟨hx, h⟩)
        rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hx''
        rw [hx'', pow_zero]
    _ ≤ ∏ r ∈ n.primeFactors, r ^ n.factorization r :=
        Finset.prod_le_prod_of_subset_of_one_le' Finset.inter_subset_right fun x hx _ =>
          Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors hx).pos
    _ = n := (Nat.prod_primeFactors_pow_factorization hn).symm

/-- For `n ≠ 0` and a finset `S` of numbers at least 5, `5 ^ (∑_{r ∈ S} v_r(n)) ≤ n`. -/
private theorem five_pow_sum_factorization_le {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ}
    (hS : ∀ r ∈ S, 5 ≤ r) : 5 ^ (∑ r ∈ S, n.factorization r) ≤ n := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact (Finset.prod_le_prod' fun r hr => Nat.pow_le_pow_left (hS r hr) _).trans
    (prod_pow_factorization_le hn S)

/-- `(e + 1) ^ 4 ≤ 5 ^ e` for `e ≥ 4`. -/
private theorem succ_pow_four_le_five_pow {e : ℕ} (he : 4 ≤ e) : (e + 1) ^ 4 ≤ 5 ^ e := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    refine Nat.le_of_mul_le_mul_right ?_ (show 0 < 625 by norm_num)
    calc (n + 1 + 1) ^ 4 * 625 = (5 * (n + 1 + 1)) ^ 4 := by ring
      _ ≤ (6 * (n + 1)) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      _ = (n + 1) ^ 4 * 1296 := by ring
      _ ≤ 5 ^ n * 1296 := Nat.mul_le_mul_right _ ih
      _ ≤ 5 ^ (n + 1) * 625 := by rw [pow_succ]; omega

/-- Basic facts about an exception `r`: it is a prime factor `r ≠ q`, at least 5, and its
exponent is even and at least 4. -/
private theorem budgetExceptions_facts {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hH : ∀ r ∈ budgetExceptions N q, r % 3 = 2)
    (hr : r ∈ budgetExceptions N q) :
    r ∈ N.primeFactors ∧ r.Prime ∧ r ≠ q ∧ 5 ≤ r ∧ Even (N.factorization r) ∧
      4 ≤ N.factorization r := by
  have h3 := hH r hr
  simp only [budgetExceptions, Finset.mem_filter] at hr
  obtain ⟨hrN, hrq, hr2⟩ := hr
  have hrp := Nat.prime_of_mem_primeFactors hrN
  have hne2 : r ≠ 2 := by
    rintro rfl
    obtain ⟨c, hc⟩ := Nat.dvd_of_mem_primeFactors hrN
    have := Nat.odd_iff.mp h.1
    omega
  have hev := even_factorization_of_ne h hq hodd hrp hrq
  have h0 : N.factorization r ≠ 0 := by
    rw [← Finsupp.mem_support_iff, Nat.support_factorization]; exact hrN
  have := hrp.two_le
  refine ⟨hrN, hrp, hrq, by omega, hev, ?_⟩
  obtain ⟨k, hk⟩ := hev
  omega

/-- Main inequality. Let `N` be an odd perfect number with special prime `q`, and suppose that
every exception `r ∈ H = budgetExceptions N q` is 2 modulo 3. With `V = ∑_{r ∈ H} v_r(N)`,
`5 ^ (3 * V) ≤ 5 ^ (4 * C) * A ^ 4` for `C = budgetC N q` and `A = budgetA N q`.
Restricted family result; whether this is in the literature was not verified. -/
theorem five_pow_three_mul_le_budget {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hH : ∀ r ∈ budgetExceptions N q, r % 3 = 2) :
    5 ^ (3 * ∑ r ∈ budgetExceptions N q, N.factorization r) ≤
      5 ^ (4 * budgetC N q) * budgetA N q ^ 4 := by
  set H := budgetExceptions N q with hHdef
  have hF := fun {r : ℕ} (hr : r ∈ H) => budgetExceptions_facts h hq hodd hH hr
  have hqN : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    rintro h0; rw [h0] at hodd; exact Nat.not_odd_zero hodd
  have hqH : q ∉ H := fun hq' => (hF hq').2.2.1 rfl
  have hrow : ∀ p ∈ insert q H, p.Prime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hq
    · exact (hF hp).2.1
  set g : ℕ → ℕ → ℕ := fun p r => (N.factorization p + 1).factorization r with hg
  set b : ℕ → ℕ → ℕ := fun p r => budgetBase p r (N.factorization p) with hb
  -- column identity and one row bound
  have hcol : ∀ r ∈ H, N.factorization r ≤
      (∑ p ∈ (insert q H).erase r, b p r) + ∑ p ∈ insert q H, g p r := by
    intro r hr
    obtain ⟨hrN, hrp, hrq, hr5, -, -⟩ := hF hr
    have hr2 : r ≠ 2 := by omega
    have hr3 : r % 3 = 2 := hH r hr
    have hsum := sigmaWeight_sum_eq h.2 hrp hr2
    have hsub : (insert q H).erase r ⊆ N.primeFactors := by
      intro x hx
      rcases Finset.mem_insert.mp (Finset.mem_of_mem_erase hx) with rfl | hx
      · exact hqN
      · exact (hF hx).1
    have hzero : ∀ x ∈ N.primeFactors, x ∉ (insert q H).erase r → sigmaWeight N x r = 0 := by
      intro x hx hx'
      have hxp := Nat.prime_of_mem_primeFactors hx
      by_cases hxr : x = r
      · subst hxr; exact sigmaWeight_self hxp
      have hxq : x ≠ q := fun e => hx' (Finset.mem_erase.mpr ⟨hxr, by simp [e]⟩)
      have hxH : x ∉ H := fun e => hx' (Finset.mem_erase.mpr ⟨hxr, by simp [e]⟩)
      have hx2 : N.factorization x = 2 := by
        by_contra hne
        exact hxH (Finset.mem_filter.mpr ⟨hx, hxq, hne⟩)
      unfold sigmaWeight
      rw [hx2, sigma_prime_sq hxp]
      refine Nat.factorization_eq_zero_of_not_dvd fun hd => ?_
      have := prime_dvd_phi3_mod_three hrp (by omega) hd
      omega
    rw [← hsum, ← Finset.sum_subset hsub hzero]
    calc ∑ p ∈ (insert q H).erase r, sigmaWeight N p r
        ≤ ∑ p ∈ (insert q H).erase r, (b p r + g p r) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hpr := Finset.ne_of_mem_erase hp
          have hpp := hrow p (Finset.mem_of_mem_erase hp)
          rw [sigmaWeight_eq_padicValNat N p hrp]
          simp only [hb, hg]
          rw [Nat.factorization_def _ hrp]
          exact padicValNat_sigma_prime_pow_le_budgetBase hpp hrp hr2 hpr
      _ = (∑ p ∈ (insert q H).erase r, b p r) + ∑ p ∈ (insert q H).erase r, g p r :=
          Finset.sum_add_distrib
      _ ≤ (∑ p ∈ (insert q H).erase r, b p r) + ∑ p ∈ insert q H, g p r :=
          Nat.add_le_add_left (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)) _
  -- sum over the columns
  set V := ∑ r ∈ H, N.factorization r with hV
  have hVle : V ≤ budgetC N q + (∑ r ∈ H, g q r) + ∑ p ∈ H, ∑ r ∈ H, g p r := by
    calc V ≤ ∑ r ∈ H, ((∑ p ∈ (insert q H).erase r, b p r) + ∑ p ∈ insert q H, g p r) :=
          Finset.sum_le_sum hcol
      _ = budgetC N q + ∑ p ∈ insert q H, ∑ r ∈ H, g p r := by
          rw [Finset.sum_add_distrib, Finset.sum_comm (s := H) (t := insert q H)]
          rfl
      _ = budgetC N q + (∑ r ∈ H, g q r) + ∑ p ∈ H, ∑ r ∈ H, g p r := by
          rw [Finset.sum_insert hqH, add_assoc]
  have hH5 : ∀ r ∈ H, 5 ≤ r := fun r hr => (hF hr).2.2.2.1
  have hA : 5 ^ (∑ r ∈ H, g q r) ≤ budgetA N q := by
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod' fun r hr => ?_
    simp only [hg]
    rw [Nat.factorization_def _ (hF hr).2.1]
    exact Nat.pow_le_pow_left (hH5 r hr) _
  set P := ∏ p ∈ H, (N.factorization p + 1) with hP
  have hrows : 5 ^ (∑ p ∈ H, ∑ r ∈ H, g p r) ≤ P := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod' fun p _ => five_pow_sum_factorization_le (by omega) hH5
  have h5 : 5 ^ V ≤ 5 ^ budgetC N q * budgetA N q * P := by
    calc 5 ^ V ≤ 5 ^ (budgetC N q + (∑ r ∈ H, g q r) + ∑ p ∈ H, ∑ r ∈ H, g p r) :=
          Nat.pow_le_pow_right (by norm_num) hVle
      _ = 5 ^ budgetC N q * 5 ^ (∑ r ∈ H, g q r) * 5 ^ (∑ p ∈ H, ∑ r ∈ H, g p r) := by
          rw [pow_add, pow_add]
      _ ≤ 5 ^ budgetC N q * budgetA N q * P :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hA) hrows
  have h6 : P ^ 4 ≤ 5 ^ V := by
    rw [hP, ← Finset.prod_pow, hV, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod' fun p hp => succ_pow_four_le_five_pow (hF hp).2.2.2.2.2
  have key : 5 ^ (3 * V) * 5 ^ V ≤ 5 ^ (4 * budgetC N q) * budgetA N q ^ 4 * 5 ^ V := by
    calc 5 ^ (3 * V) * 5 ^ V = (5 ^ V) ^ 4 := by rw [← pow_add, ← pow_mul]; ring_nf
      _ ≤ (5 ^ budgetC N q * budgetA N q * P) ^ 4 := Nat.pow_le_pow_left h5 4
      _ = 5 ^ (4 * budgetC N q) * budgetA N q ^ 4 * P ^ 4 := by ring
      _ ≤ 5 ^ (4 * budgetC N q) * budgetA N q ^ 4 * 5 ^ V := Nat.mul_le_mul_left _ h6
  exact Nat.le_of_mul_le_mul_right key (by positivity)

/-- If `¬ r ^ 2 ∣ p ^ (r - 1) - 1` for different primes `p` and `r`, then every base term of
the row `p` at the column `r` is at most 1. -/
theorem budgetBase_le_one {p r e : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    (hW : ¬ r ^ 2 ∣ p ^ (r - 1) - 1) : budgetBase p r e ≤ 1 := by
  unfold budgetBase
  split_ifs with hc
  · by_contra hlt
    obtain ⟨k, hk⟩ := orderOf_dvd_sub_one hp hr hpr
    refine hW (((pow_dvd_pow r (by omega :
      2 ≤ padicValNat r (p ^ orderOf (p : ZMod r) - 1))).trans pow_padicValNat_dvd).trans ?_)
    rw [hk, pow_mul]
    simpa using Nat.sub_dvd_pow_sub_pow (p ^ orderOf (p : ZMod r)) 1 k
  · exact Nat.zero_le _

/-- Corollary. Let `N` be an odd perfect number with special prime `q` of exponent `a`, and
`H = budgetExceptions N q` with `h = #H`. Assume that every `r ∈ H` is 2 modulo 3, that no
`r ∈ H` divides `a + 1`, and that `¬ r ^ 2 ∣ p ^ (r - 1) - 1` for all `p ∈ H ∪ {q}` and
`r ∈ H` with `p ≠ r`. Then the total excess `T = ∑_{p ≠ q} (v_p(N) / 2 - 1)` satisfies
`3 * T + 3 * h ≤ 2 * h ^ 2`. Restricted family result with explicit valuation hypotheses;
whether this is in the literature was not verified. The hypotheses cannot be checked without
knowing the primes of `N`, and the total excess is not bounded in general. -/
theorem three_mul_excess_add_le_budget {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hH : ∀ r ∈ budgetExceptions N q, r % 3 = 2)
    (hA : ∀ r ∈ budgetExceptions N q, ¬ r ∣ N.factorization q + 1)
    (hW : ∀ p ∈ insert q (budgetExceptions N q), ∀ r ∈ budgetExceptions N q, p ≠ r →
      ¬ r ^ 2 ∣ p ^ (r - 1) - 1) :
    3 * ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) +
        3 * (budgetExceptions N q).card ≤ 2 * (budgetExceptions N q).card ^ 2 := by
  have hmain := five_pow_three_mul_le_budget h hq hodd hH
  set H := budgetExceptions N q with hHdef
  have hF := fun {r : ℕ} (hr : r ∈ H) => budgetExceptions_facts h hq hodd hH hr
  have hqH : q ∉ H := fun hq' => (hF hq').2.2.1 rfl
  have hA1 : budgetA N q = 1 := by
    refine Finset.prod_eq_one fun r hr => ?_
    have : Fact r.Prime := ⟨(hF hr).2.1⟩
    rw [padicValNat.eq_zero_of_not_dvd (hA r hr), pow_zero]
  have hC : budgetC N q ≤ H.card * H.card := by
    unfold budgetC
    rw [← hHdef]
    calc ∑ r ∈ H, ∑ p ∈ (insert q H).erase r, budgetBase p r (N.factorization p)
        ≤ ∑ r ∈ H, ∑ p ∈ (insert q H).erase r, 1 := by
          refine Finset.sum_le_sum fun r hr => Finset.sum_le_sum fun p hp => ?_
          have hpH := Finset.mem_of_mem_erase hp
          have hpp : p.Prime := by
            rcases Finset.mem_insert.mp hpH with rfl | hp'
            · exact hq
            · exact (hF hp').2.1
          exact budgetBase_le_one hpp (hF hr).2.1 (Finset.ne_of_mem_erase hp)
            (hW p hpH r hr (Finset.ne_of_mem_erase hp))
      _ = ∑ r ∈ H, H.card := by
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [Finset.sum_const, smul_eq_mul, mul_one,
            Finset.card_erase_of_mem (Finset.mem_insert_of_mem hr),
            Finset.card_insert_of_notMem hqH, Nat.add_sub_cancel]
      _ = H.card * H.card := by rw [Finset.sum_const, smul_eq_mul]
  rw [hA1, one_pow, mul_one] at hmain
  have h3V := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).mp hmain
  have hT : ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) =
      ∑ p ∈ H, (N.factorization p / 2 - 1) := by
    refine (Finset.sum_subset (fun x hx => ?_) fun x hx hx' => ?_).symm
    · obtain ⟨hxN, -, hxq, -⟩ := hF hx
      exact Finset.mem_erase.mpr ⟨hxq, hxN⟩
    · obtain ⟨hxq, hxN⟩ := Finset.mem_erase.mp hx
      have hx2 : N.factorization x = 2 := by
        by_contra hne
        exact hx' (Finset.mem_filter.mpr ⟨hxN, hxq, hne⟩)
      simp [hx2]
  have hVT : ∑ r ∈ H, N.factorization r =
      2 * ∑ p ∈ H, (N.factorization p / 2 - 1) + 2 * H.card := by
    rw [Finset.mul_sum, Finset.card_eq_sum_ones, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    obtain ⟨-, -, -, -, ⟨k, hk⟩, h4⟩ := hF hr
    omega
  rw [hT]
  rw [hVT] at h3V
  nlinarith [h3V, hC]

/-- Corollary with the landed bound `7 ≤ T`: under the hypotheses of
`three_mul_excess_add_le_budget`, there are at least 5 exceptions. Restricted family result
with explicit valuation hypotheses; whether this is in the literature was not verified. The
hypotheses cannot be checked without knowing the primes of `N`. -/
theorem five_le_card_budgetExceptions {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hH : ∀ r ∈ budgetExceptions N q, r % 3 = 2)
    (hA : ∀ r ∈ budgetExceptions N q, ¬ r ∣ N.factorization q + 1)
    (hW : ∀ p ∈ insert q (budgetExceptions N q), ∀ r ∈ budgetExceptions N q, p ≠ r →
      ¬ r ^ 2 ∣ p ^ (r - 1) - 1) :
    5 ≤ (budgetExceptions N q).card := by
  have h1 := three_mul_excess_add_le_budget h hq hodd hH hA hW
  have h7 := seven_le_excess h hq hodd
  generalize (budgetExceptions N q).card = k at h1
  by_contra hk
  interval_cases k <;> omega

end OddPerfect

#print axioms OddPerfect.padicValNat_sigma_prime_pow_row
#print axioms OddPerfect.padicValNat_sigma_prime_pow_le_budgetBase
#print axioms OddPerfect.five_pow_three_mul_le_budget
#print axioms OddPerfect.budgetBase_le_one
#print axioms OddPerfect.three_mul_excess_add_le_budget
#print axioms OddPerfect.five_le_card_budgetExceptions
