import OddPerfect.EqualExponentCount
import OddPerfect.Seed.Example
import OddPerfect.Seed.Starter
import OddPerfect.Cyclotomic
import OddPerfect.CycloRootCount
import OddPerfect.AbundancyTail

/-!
# Two exceptions at a prime `l`: the argument with its finite facts as hypotheses

Let `l` be a prime with `l - 1 = 2 k`, `k ≥ 2`, and write `R(x) = ∑ i ∈ Finset.range l, x ^ i`.
Let `q` and `d` be arbitrary natural numbers and let `N` be an odd perfect number with `l ∤ N`
such that every prime factor `p` of `N` other than `q` and `d` has `l ∣ e_p + 1`. Call `G` the
set of these prime factors. For `p ∈ G` every prime factor of `R(p)` divides `N`, is `1` modulo
`l` and lies outside `G`, so it is `q` or `d`.

* If `q` and `d` are both `1` modulo `l`, both are at least the least prime `r0` that is `1`
  modulo `l`; the elements of `G` below `100` number at most one and are at least `m` (they
  lie in a set `E` of primes whose rows are pairwise coprime; every other odd prime below `100`
  has a row with at least three prime factors); those in `[100, B]` lie in a set `M`; those
  above `B` number at most `2 (l - 1)` in each interval `(B ^ j, B ^ (j + 1)]`.
* Otherwise all rows `R(p)`, `p ∈ G`, are powers of one prime. Then `G` has no element below
  `100` (every such row has at least two prime factors), and above its least element the
  elements grow faster than a power `l - 1`.

In each case a numerical hypothesis bounds the product of `p / (p - 1)` below `2`. The module
also holds the generic tools for the data modules: a lower bound for the number of distinct
prime factors from trial factors, and the list of numbers in `[100, B]` without a prime factor
up to `37`.

Restricted result; no published source was checked; novelty not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect.TwoExcGen

open OddPerfect.EqCount (fermatRes two_le_card_of_witness)

/-- The factor `p / (p - 1)`. -/
def ab (p : ℕ) : ℚ := (p : ℚ) / ((p : ℚ) - 1)

/-! ## The factor `p / (p - 1)` -/

theorem ab_eq {p : ℕ} (hp : 2 ≤ p) : ab p = 1 + 1 / ((p : ℚ) - 1) := by
  have h2 : (2 : ℚ) ≤ p := by exact_mod_cast hp
  have hne : (p : ℚ) - 1 ≠ 0 := by intro h; linarith
  rw [ab, one_add_div hne, sub_add_cancel]

theorem one_le_ab {p : ℕ} (hp : 2 ≤ p) : 1 ≤ ab p := by
  have h2 : (2 : ℚ) ≤ p := by exact_mod_cast hp
  have : 0 < 1 / ((p : ℚ) - 1) := one_div_pos.mpr (by linarith)
  rw [ab_eq hp]
  linarith

theorem ab_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ ab p := le_trans zero_le_one (one_le_ab hp)

theorem ab_anti {a p : ℕ} (ha : 2 ≤ a) (hap : a ≤ p) : ab p ≤ ab a := by
  rw [ab_eq ha, ab_eq (ha.trans hap)]
  have h1 : (2 : ℚ) ≤ a := by exact_mod_cast ha
  have h2 : (a : ℚ) ≤ p := by exact_mod_cast hap
  have := one_div_le_one_div_of_le (show (0 : ℚ) < (a : ℚ) - 1 by linarith)
    (show (a : ℚ) - 1 ≤ (p : ℚ) - 1 by linarith)
  linarith

theorem prod_ab_nonneg {s : Finset ℕ} (hs : ∀ p ∈ s, 2 ≤ p) : 0 ≤ ∏ p ∈ s, ab p :=
  Finset.prod_nonneg fun p hp => ab_nonneg (hs p hp)

theorem prod_ab_mono {s t : Finset ℕ} (hst : s ⊆ t) (ht : ∀ p ∈ t, 2 ≤ p) :
    ∏ p ∈ s, ab p ≤ ∏ p ∈ t, ab p := by
  rw [← Finset.prod_sdiff hst]
  have h1 : 1 ≤ ∏ p ∈ t \ s, ab p :=
    Finset.one_le_prod₀ fun p hp => one_le_ab (ht p (Finset.sdiff_subset hp))
  exact le_mul_of_one_le_left (prod_ab_nonneg fun p hp => ht p (hst hp)) h1

theorem prod_ab_le_pow {s : Finset ℕ} {a k : ℕ} (ha : 2 ≤ a) (hs : ∀ p ∈ s, a ≤ p)
    (hk : s.card ≤ k) : ∏ p ∈ s, ab p ≤ ab a ^ k := by
  calc ∏ p ∈ s, ab p ≤ ∏ _p ∈ s, ab a :=
        Finset.prod_le_prod₀ (fun p hp => ab_nonneg (ha.trans (hs p hp)))
          (fun p hp => ab_anti ha (hs p hp))
    _ = ab a ^ s.card := Finset.prod_const _
    _ ≤ ab a ^ k := pow_le_pow_right₀ (one_le_ab ha) hk

/-- Two distinct odd primes contribute at most `(3/2)(5/4)`. -/
theorem prod_ab_le_pair {s : Finset ℕ} (hs : ∀ p ∈ s, 3 ≤ p ∧ p % 2 = 1) (hk : s.card ≤ 2) :
    ∏ p ∈ s, ab p ≤ 15 / 8 := by
  have ab_3 : ab 3 = 3 / 2 := by norm_num [ab]
  have ab_5 : ab 5 = 5 / 4 := by norm_num [ab]
  rcases Nat.lt_or_ge s.card 2 with h | h
  · have := prod_ab_le_pow (a := 3) (k := 1) (by norm_num) (fun p hp => (hs p hp).1)
      (by omega)
    rw [ab_3, pow_one] at this
    linarith
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp (le_antisymm hk h)
    rw [Finset.prod_pair hxy]
    have hx := hs x (by simp)
    have hy := hs y (by simp)
    have key : ∀ a b : ℕ, 3 ≤ a → a % 2 = 1 → b % 2 = 1 → a < b → ab a * ab b ≤ 15 / 8 := by
      intro a b ha _ hb hab
      have e1 := ab_anti (a := 3) (by norm_num) ha
      have e2 := ab_anti (a := 5) (by norm_num) (show 5 ≤ b by omega)
      rw [ab_3] at e1
      rw [ab_5] at e2
      have hb0 := ab_nonneg (p := b) (by omega)
      calc ab a * ab b ≤ 3 / 2 * (5 / 4) := mul_le_mul e1 e2 hb0 (by norm_num)
        _ = 15 / 8 := by norm_num
    rcases lt_or_gt_of_ne hxy with hlt | hlt
    · exact key x y hx.1 hx.2 hy.2 hlt
    · rw [mul_comm]
      exact key y x hy.1 hy.2 hx.2 hlt

/-- A sum bound for `1 / (p - 1)` gives a product bound for `p / (p - 1)`. -/
theorem prod_ab_le_of_sum {s : Finset ℕ} (hs : ∀ p ∈ s, 2 ≤ p) {c : ℚ}
    (hc : ∑ p ∈ s, (1 : ℚ) / ((p : ℚ) - 1) ≤ c) (hc1 : c < 1) :
    ∏ p ∈ s, ab p ≤ 1 / (1 - c) := by
  have hpos : ∀ p ∈ s, (0 : ℚ) ≤ 1 / ((p : ℚ) - 1) := fun p hp => by
    have : (2 : ℚ) ≤ p := by exact_mod_cast hs p hp
    exact le_of_lt (one_div_pos.mpr (by linarith))
  have hsum : ∑ p ∈ s, (1 : ℚ) / ((p : ℚ) - 1) < 1 := lt_of_le_of_lt hc hc1
  have h := prod_one_add_le_inv_one_sub s (fun p => 1 / ((p : ℚ) - 1)) hpos hsum
  beta_reduce at h
  rw [Finset.prod_congr rfl (fun p hp => ab_eq (hs p hp))]
  exact h.trans (one_div_le_one_div_of_le (by linarith) (by linarith))

/-! ## Tools for the data modules -/

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

/-- The small primes used to sieve `[100, B]`. -/
def smallPs : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

/-- No prime factor up to `37`. -/
def good (n : ℕ) : Bool := smallPs.all (fun s => n % s != 0)

/-- The numbers in `[100, B]` without a prime factor up to `37`. -/
def bigList (B : ℕ) : List ℕ := (List.range' 100 (B - 99)).filter good

theorem bigList_nodup (B : ℕ) : (bigList B).Nodup := List.Nodup.filter good List.nodup_range'

theorem ge_of_mem_bigList {B n : ℕ} (h : n ∈ bigList B) : 100 ≤ n := by
  simp only [bigList, List.mem_filter, List.mem_range'_1] at h
  exact h.1.1

theorem mem_bigList {B p : ℕ} (hp : p.Prime) (h1 : 100 ≤ p) (h2 : p ≤ B) :
    p ∈ (bigList B).toFinset := by
  rw [List.mem_toFinset]
  simp only [bigList, List.mem_filter, List.mem_range'_1, good, List.all_eq_true,
    bne_iff_ne, ne_eq]
  refine ⟨⟨h1, by omega⟩, fun s hs h => ?_⟩
  have hs' : 2 ≤ s ∧ s ≤ 37 := by
    simp only [smallPs, List.mem_cons] at hs
    simp at hs
    omega
  have := hp.eq_one_or_self_of_dvd s (Nat.dvd_of_mod_eq_zero h)
  omega

/-- The product of the listed numbers. -/
def numL (B : ℕ) : ℕ := (bigList B).prod

/-- The product of the listed numbers minus one. -/
def denL (B : ℕ) : ℕ := ((bigList B).map (· - 1)).prod

theorem list_prod_ab (l : List ℕ) (h2 : ∀ p ∈ l, 2 ≤ p) :
    (l.map ab).prod * (((l.map (fun x : ℕ => x - 1)).prod : ℕ) : ℚ) = ((l.prod : ℕ) : ℚ) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := h2 p (by simp)
    have ih' := ih (fun x hx => h2 x (by simp [hx]))
    simp only [List.map_cons, List.prod_cons, Nat.cast_mul]
    have hp1 : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    have hne : (p : ℚ) - 1 ≠ 0 := by
      have : (2 : ℚ) ≤ p := by exact_mod_cast hp
      intro h
      linarith
    have hab : ab p * ((p - 1 : ℕ) : ℚ) = p := by
      rw [hp1, ab, div_mul_cancel₀ _ hne]
    rw [← hab, ← ih']
    ring

theorem prod_bigList {B : ℕ} (hd : 0 < denL B) :
    ∏ p ∈ (bigList B).toFinset, ab p = (numL B : ℚ) / denL B := by
  rw [List.prod_toFinset _ (bigList_nodup B)]
  have h2 : ∀ p ∈ bigList B, 2 ≤ p := fun p hp => by
    have := ge_of_mem_bigList hp
    omega
  have hd' : (denL B : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [eq_div_iff hd']
  exact list_prod_ab (bigList B) h2

/-! ## Number theory -/

theorem R_eq_sigma {l p : ℕ} (hl : 1 ≤ l) (hp : p.Prime) :
    ∑ i ∈ Finset.range l, p ^ i = σ 1 (p ^ (l - 1)) := by
  rw [sigma_one_apply_prime_pow hp, Nat.sub_add_cancel hl]

theorem dvd_R_of_mod {l s : ℕ} (hl : 2 ≤ l) (hs : s % l = 1) :
    l ∣ ∑ i ∈ Finset.range l, s ^ i := by
  apply Nat.dvd_of_mod_eq_zero
  rw [Finset.sum_nat_mod]
  have : ∀ i ∈ Finset.range l, s ^ i % l = 1 := fun i _ => by
    rw [Nat.pow_mod, hs, one_pow]
    exact Nat.mod_eq_of_lt (by omega)
  rw [Finset.sum_congr rfl this]
  simp

theorem R_ge {l : ℕ} (hl : 1 ≤ l) (p : ℕ) : p ^ (l - 1) ≤ ∑ i ∈ Finset.range l, p ^ i :=
  Finset.single_le_sum (f := fun i => p ^ i) (fun i _ => Nat.zero_le _)
    (Finset.mem_range.mpr (by omega))

theorem R_one_lt {l p : ℕ} (hl : 2 ≤ l) (hp : 2 ≤ p) : 1 < ∑ i ∈ Finset.range l, p ^ i :=
  lt_of_lt_of_le (Nat.one_lt_pow (by omega) (by omega)) (R_ge (by omega) p)

theorem odd_of_mem {N p : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors) : p % 2 = 1 := by
  rcases (Nat.prime_of_mem_primeFactors hp).eq_two_or_odd with h2 | h2
  · subst h2
    obtain ⟨k, hk⟩ := Nat.dvd_of_mem_primeFactors hp
    have := Nat.odd_iff.mp h.1
    omega
  · exact h2

/-- Every prime factor of the row of an ordinary prime is a prime factor of `N`, equal to `q`
or `d`, and `1` modulo `l`. -/
theorem key {l N q d : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (h : OddPerfect N) (hlN : ¬ l ∣ N)
    (hcomp : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ d → l ∣ N.factorization p + 1)
    {p : ℕ} (hp : p ∈ N.primeFactors) (hpq : p ≠ q) (hpd : p ≠ d) {s : ℕ} (hs : s.Prime)
    (hsR : s ∣ ∑ i ∈ Finset.range l, p ^ i) :
    s ∈ N.primeFactors ∧ (s = q ∨ s = d) ∧ s % l = 1 := by
  have hpP := Nat.prime_of_mem_primeFactors hp
  have hN := h.ne_zero
  have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl.one_lt.le
  have hdv : σ 1 (p ^ (l - 1)) ∣ σ 1 (p ^ N.factorization p) :=
    OPNExample.sigma_prime_pow_dvd (a := l - 1) hpP (by rw [hl1]; exact hcomp p hp hpq hpd)
  rw [R_eq_sigma hl.one_lt.le hpP] at hsR
  have hsl : s % l = 1 := by
    rcases prime_dvd_sigma_prime_pow_of_prime_length hpP hs hl hsR with h1 | h1
    · subst h1
      exact absurd (OPNStarter.force_prime h.perfect hpP rfl hl hl2 (hsR.trans hdv)) hlN
    · exact h1
  have hs2 : s ≠ 2 := by
    intro h2
    rw [h2] at hsl
    have := hl.two_le
    have : 2 % l = 2 := Nat.mod_eq_of_lt (by omega)
    omega
  have hsN : s ∣ N := OPNStarter.force_prime h.perfect hpP rfl hs hs2 (hsR.trans hdv)
  have hsP : s ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hs, hsN, hN⟩
  refine ⟨hsP, ?_, hsl⟩
  by_contra hne
  have hne' := not_or.mp hne
  have hd2 : σ 1 (s ^ (l - 1)) ∣ σ 1 (s ^ N.factorization s) :=
    OPNExample.sigma_prime_pow_dvd (a := l - 1) hs (by rw [hl1]; exact hcomp s hsP hne'.1 hne'.2)
  have hls : l ∣ σ 1 (s ^ (l - 1)) := by
    rw [← R_eq_sigma hl.one_lt.le hs]
    exact dvd_R_of_mod hl.two_le hsl
  exact hlN (OPNStarter.force_prime h.perfect hs rfl hl hl2 (hls.trans hd2))

/-- A number whose prime factors lie in `{q, d}` is at most `q ^ a * d ^ b`. -/
theorem le_mul_of_pf_subset {n q d : ℕ} (hn : n ≠ 0) (h : n.primeFactors ⊆ {q, d}) :
    n ≤ q ^ n.factorization q * d ^ n.factorization d := by
  have e : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n :=
    Nat.prod_factorization_pow_eq_self hn
  rw [Finset.prod_subset (f := fun p => p ^ n.factorization p) h (fun x _ hx => by
    show x ^ n.factorization x = 1
    have : n.factorization x = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      rw [Nat.mem_primeFactors] at hx
      tauto
    rw [this, pow_zero])] at e
  by_cases hqd : q = d
  · subst hqd
    have hs : ({q, q} : Finset ℕ) = {q} := by simp
    rw [hs, Finset.prod_singleton] at e
    calc n = q ^ n.factorization q := e.symm
      _ ≤ q ^ n.factorization q * q ^ n.factorization q := Nat.le_mul_self _
  · rw [Finset.prod_pair hqd] at e
    exact e.ge

/-- At most `l - 1` elements of a block belong to one receiver. -/
theorem blockCount {l B k : ℕ} (hl : l.Prime) (hk : 2 ≤ k) (hB : 2 ≤ B)
    {S : Finset ℕ} {T r : ℕ} (hT : B ≤ T) (hS : ∀ x ∈ S, T < x ∧ x ≤ T * B) (hrl : r ≠ l) :
    (S.filter (fun x => T ^ k ≤ r ^ (∑ i ∈ Finset.range l, x ^ i).factorization r)).card
      ≤ l - 1 := by
  have hTk : 1 < T ^ k := Nat.one_lt_pow (by omega) (by omega)
  by_cases hr : r.Prime
  · have hr1 := hr.one_lt
    have hk0 : 0 < Nat.clog r (T ^ k) := Nat.clog_pos hr1 hTk
    refine le_trans (Finset.card_le_card ?_)
      (card_filter_pow_dvd_geom_sum_le (a := T) hl hr hrl hk0)
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    obtain ⟨hxS, hxk⟩ := hx
    obtain ⟨h1, h2⟩ := hS x hxS
    have hkle : Nat.clog r (T ^ k) ≤ (∑ i ∈ Finset.range l, x ^ i).factorization r :=
      (Nat.clog_le_iff_le_pow hr1).mpr hxk
    have hpowk : T ^ k ≤ r ^ Nat.clog r (T ^ k) := Nat.le_pow_clog hr1 _
    have hTT : T * B ≤ T + T ^ k := by
      have e1 : T * T ≤ T ^ k := by
        rw [← pow_two]
        exact Nat.pow_le_pow_right (by omega) hk
      have e2 : T * B ≤ T * T := Nat.mul_le_mul_left T hT
      omega
    refine ⟨Finset.mem_Ioc.mpr ⟨h1, by omega⟩, ?_⟩
    exact (Nat.pow_dvd_pow r hkle).trans (Nat.ordProj_dvd _ r)
  · have hE : S.filter (fun x => T ^ k ≤ r ^ (∑ i ∈ Finset.range l, x ^ i).factorization r)
        = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x _ hx
      rw [Nat.factorization_eq_zero_of_not_prime _ hr, pow_zero] at hx
      omega
    rw [hE]
    simp

theorem B_le_pow {B j : ℕ} (hB : 1 ≤ B) (hj : 1 ≤ j) : B ≤ B ^ j :=
  calc B = B ^ 1 := (pow_one _).symm
    _ ≤ B ^ j := Nat.pow_le_pow_right (by omega) hj

/-! ## Two receivers -/

theorem case_a {l B k m r0 : ℕ} {E M : Finset ℕ}
    (hl : l.Prime) (hk : 2 * k = l - 1) (hk2 : 2 ≤ k) (hB : 100 ≤ B)
    (hsmall : ∀ p, p.Prime → p < 100 → p ≠ 2 → p ≠ l →
      2 ≤ (∑ i ∈ Finset.range l, p ^ i).primeFactors.card ∧
      (3 ≤ (∑ i ∈ Finset.range l, p ^ i).primeFactors.card ∨ p ∈ E))
    (hE : ∀ p ∈ E, m ≤ p)
    (hcop : ∀ a ∈ E, ∀ b ∈ E, a ≠ b →
      Nat.gcd (∑ i ∈ Finset.range l, a ^ i) (∑ i ∈ Finset.range l, b ^ i) = 1)
    (hr0 : ∀ x, x.Prime → x % l = 1 → r0 ≤ x) (hr02 : 2 ≤ r0) (hm2 : 2 ≤ m)
    (hM : ∀ p, p.Prime → 100 ≤ p → p ≤ B → p ∈ M) (hM2 : ∀ p ∈ M, 2 ≤ p)
    (hc1 : ((2 * (l - 1) : ℕ) : ℚ) / ((B : ℚ) - 1) < 1)
    {N q d : ℕ} (h : OddPerfect N) (hlN : ¬ l ∣ N) (hq1 : q % l = 1) (hd1 : d % l = 1)
    (hkey : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ d → ∀ s, s.Prime →
      s ∣ ∑ i ∈ Finset.range l, p ^ i → s = q ∨ s = d) :
    ∏ p ∈ N.primeFactors, ab p ≤
      ab m * ((∏ p ∈ M, ab p) * (1 / (1 - ((2 * (l - 1) : ℕ) : ℚ) / ((B : ℚ) - 1)))) *
        ab r0 ^ 2 := by
  have hl2 := hl.two_le
  set P := N.primeFactors with hP
  have hP2 : ∀ p ∈ P, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  set G := P.filter (fun p => p ≠ q ∧ p ≠ d) with hG
  have hGP : G ⊆ P := Finset.filter_subset _ _
  have hGm : ∀ p ∈ G, p ∈ P ∧ p ≠ q ∧ p ≠ d := fun p hp => Finset.mem_filter.mp hp
  -- the rows of elements of `G`
  have hsub : ∀ p ∈ G, (∑ i ∈ Finset.range l, p ^ i).primeFactors ⊆ {q, d} := by
    intro p hp x hx
    obtain ⟨hpP, hpq, hpd⟩ := hGm p hp
    have := hkey p hpP hpq hpd x (Nat.prime_of_mem_primeFactors hx)
      (Nat.dvd_of_mem_primeFactors hx)
    rcases this with rfl | rfl <;> simp
  have hRne : ∀ p ∈ G, (∑ i ∈ Finset.range l, p ^ i) ≠ 0 := fun p hp =>
    (lt_trans zero_lt_one (R_one_lt hl2 (hP2 p (hGP hp)))).ne'
  -- exceptional part
  have hEx : ∏ p ∈ P.filter (fun p => ¬ (p ≠ q ∧ p ≠ d)), ab p ≤ ab r0 ^ 2 := by
    refine prod_ab_le_pow hr02 (fun x hx => ?_) ?_
    · rw [Finset.mem_filter] at hx
      have hxp := Nat.prime_of_mem_primeFactors hx.1
      have : x = q ∨ x = d := by tauto
      rcases this with rfl | rfl
      · exact hr0 x hxp hq1
      · exact hr0 x hxp hd1
    · refine (Finset.card_le_card (t := {q, d}) (fun x hx => ?_)).trans Finset.card_le_two
      rw [Finset.mem_filter] at hx
      have : x = q ∨ x = d := by tauto
      rcases this with rfl | rfl <;> simp
  -- small part
  set Gs := G.filter (fun p => p < 100) with hGs
  have hsev : ∀ p ∈ Gs, p ∈ E ∧ (∑ i ∈ Finset.range l, p ^ i).primeFactors = {q, d} := by
    intro p hp
    obtain ⟨hpG, hlt⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpP, hpq, hpd⟩ := hGm p hpG
    have hprime := Nat.prime_of_mem_primeFactors hpP
    have h2 : p ≠ 2 := by
      have := odd_of_mem h hpP
      omega
    have hl' : p ≠ l := by
      rintro rfl
      exact hlN (Nat.dvd_of_mem_primeFactors hpP)
    obtain ⟨hc2, hc3⟩ := hsmall p hprime hlt h2 hl'
    have hs' := hsub p hpG
    have hcard := (Finset.card_le_card hs').trans Finset.card_le_two
    refine ⟨?_, ?_⟩
    · rcases hc3 with h3 | h3
      · omega
      · exact h3
    · exact Finset.eq_of_subset_of_card_le hs' (Finset.card_le_two.trans hc2)
  have hGsb : ∏ p ∈ Gs, ab p ≤ ab m := by
    have := prod_ab_le_pow (k := 1) hm2 (fun p hp => hE p (hsev p hp).1) (s := Gs) (by
      rw [Finset.card_le_one]
      intro a ha b hb
      by_contra hab
      have g := hcop a (hsev a ha).1 b (hsev b hb).1 hab
      have hqa : q ∈ (∑ i ∈ Finset.range l, a ^ i).primeFactors := by rw [(hsev a ha).2]; simp
      have hqb : q ∈ (∑ i ∈ Finset.range l, b ^ i).primeFactors := by rw [(hsev b hb).2]; simp
      have hdv := Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hqa)
        (Nat.dvd_of_mem_primeFactors hqb)
      rw [g] at hdv
      exact (Nat.prime_of_mem_primeFactors hqa).one_lt.ne' (Nat.dvd_one.mp hdv))
    rwa [pow_one] at this
  -- middle part
  set Gr := G.filter (fun p => ¬ p < 100) with hGr
  set Gm := Gr.filter (fun p => p ≤ B) with hGm'
  set Gb := Gr.filter (fun p => ¬ p ≤ B) with hGb
  have hGrG : Gr ⊆ G := Finset.filter_subset _ _
  have hGmb : ∏ p ∈ Gm, ab p ≤ ∏ p ∈ M, ab p := by
    refine prod_ab_mono (fun p hp => ?_) hM2
    obtain ⟨hpGr, hle⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpG, hlt⟩ := Finset.mem_filter.mp hpGr
    exact hM p (Nat.prime_of_mem_primeFactors (hGm p hpG).1) (by omega) hle
  -- large part
  have hGbb : ∏ p ∈ Gb, ab p ≤ 1 / (1 - ((2 * (l - 1) : ℕ) : ℚ) / ((B : ℚ) - 1)) := by
    have hbig : ∀ p ∈ Gb, B < p := fun p hp => by
      have := (Finset.mem_filter.mp hp).2
      omega
    have hblock : ∀ j, 1 ≤ j →
        (Gb.filter (fun p => B ^ j < p ∧ p ≤ B ^ (j + 1))).card ≤ 2 * (l - 1) := by
      intro j hj
      set T := B ^ j with hTdef
      have hT : B ≤ T := B_le_pow (by omega) hj
      set Blk := Gb.filter (fun p => T < p ∧ p ≤ B ^ (j + 1)) with hBlk
      have hBS : ∀ x ∈ Blk, T < x ∧ x ≤ T * B := by
        intro x hx
        have hx' := (Finset.mem_filter.mp hx).2
        rw [hTdef, ← pow_succ]
        exact hx'
      have hBG : ∀ x ∈ Blk, x ∈ G := fun x hx =>
        hGrG (Finset.filter_subset _ _ (Finset.filter_subset _ _ hx))
      have hcover : Blk ⊆
          Blk.filter (fun x => T ^ k ≤ q ^ (∑ i ∈ Finset.range l, x ^ i).factorization q) ∪
          Blk.filter (fun x => T ^ k ≤ d ^ (∑ i ∈ Finset.range l, x ^ i).factorization d) := by
        intro x hx
        have hxG := hBG x hx
        have hle := le_mul_of_pf_subset (hRne x hxG) (hsub x hxG)
        have hlt : T ^ (l - 1) < ∑ i ∈ Finset.range l, x ^ i :=
          lt_of_lt_of_le (Nat.pow_lt_pow_left (hBS x hx).1 (by omega)) (R_ge (by omega) x)
        by_cases h1 : T ^ k ≤ q ^ (∑ i ∈ Finset.range l, x ^ i).factorization q
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h1⟩)
        by_cases h2 : T ^ k ≤ d ^ (∑ i ∈ Finset.range l, x ^ i).factorization d
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, h2⟩)
        exfalso
        have := Nat.mul_lt_mul'' (not_le.mp h1) (not_le.mp h2)
        have hTT : T ^ k * T ^ k = T ^ (l - 1) := by rw [← pow_add, show k + k = l - 1 by omega]
        omega
      have hql : q ≠ l := by
        rintro rfl
        rw [Nat.mod_self] at hq1
        omega
      have hdl : d ≠ l := by
        rintro rfl
        rw [Nat.mod_self] at hd1
        omega
      calc (Gb.filter (fun p => B ^ j < p ∧ p ≤ B ^ (j + 1))).card = Blk.card := rfl
        _ ≤ _ := Finset.card_le_card hcover
        _ ≤ _ := Finset.card_union_le _ _
        _ ≤ (l - 1) + (l - 1) := Nat.add_le_add
            (blockCount hl hk2 (by omega) hT hBS hql) (blockCount hl hk2 (by omega) hT hBS hdl)
        _ = 2 * (l - 1) := by omega
    have hsum := sum_inv_pred_le_of_interval_card (by omega) hbig hblock
    exact prod_ab_le_of_sum (fun p hp => by have := hbig p hp; omega) hsum hc1
  -- assemble
  have e1 : (∏ p ∈ G, ab p) * (∏ p ∈ P.filter (fun p => ¬ (p ≠ q ∧ p ≠ d)), ab p) =
      ∏ p ∈ P, ab p := Finset.prod_filter_mul_prod_filter_not P _ ab
  have e2 : (∏ p ∈ Gs, ab p) * (∏ p ∈ Gr, ab p) = ∏ p ∈ G, ab p :=
    Finset.prod_filter_mul_prod_filter_not G _ ab
  have e3 : (∏ p ∈ Gm, ab p) * (∏ p ∈ Gb, ab p) = ∏ p ∈ Gr, ab p :=
    Finset.prod_filter_mul_prod_filter_not Gr _ ab
  have n2 : 0 ≤ ∏ p ∈ Gm, ab p :=
    prod_ab_nonneg fun p hp => hP2 p (hGP (hGrG (Finset.filter_subset _ _ hp)))
  have n3 : 0 ≤ ∏ p ∈ Gb, ab p :=
    prod_ab_nonneg fun p hp => hP2 p (hGP (hGrG (Finset.filter_subset _ _ hp)))
  have n4 : 0 ≤ ∏ p ∈ P.filter (fun p => ¬ (p ≠ q ∧ p ≠ d)), ab p :=
    prod_ab_nonneg fun p hp => hP2 p (Finset.filter_subset _ _ hp)
  have nM : 0 ≤ ∏ p ∈ M, ab p := prod_ab_nonneg hM2
  have nL : (0 : ℚ) ≤ 1 / (1 - ((2 * (l - 1) : ℕ) : ℚ) / ((B : ℚ) - 1)) :=
    le_of_lt (one_div_pos.mpr (by linarith))
  rw [← e1, ← e2, ← e3]
  have b3 := mul_le_mul hGmb hGbb n3 nM
  have b2 := mul_le_mul hGsb b3 (mul_nonneg n2 n3) (ab_nonneg hm2)
  exact mul_le_mul b2 hEx n4 (mul_nonneg (ab_nonneg hm2) (mul_nonneg nM nL))

/-! ## One receiver -/

theorem case_b {l B : ℕ} {E : Finset ℕ} (hl : l.Prime) (hl5 : 5 ≤ l) (hB : 100 ≤ B)
    (hB4 : B < 10000)
    (hsmall : ∀ p, p.Prime → p < 100 → p ≠ 2 → p ≠ l →
      2 ≤ (∑ i ∈ Finset.range l, p ^ i).primeFactors.card ∧
      (3 ≤ (∑ i ∈ Finset.range l, p ^ i).primeFactors.card ∨ p ∈ E))
    (hc1 : ((1 : ℕ) : ℚ) / ((B : ℚ) - 1) < 1)
    {N q d : ℕ} (h : OddPerfect N) (hlN : ¬ l ∣ N) (r : ℕ)
    (hr : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ d → ∀ s, s.Prime →
      s ∣ ∑ i ∈ Finset.range l, p ^ i → s = r ∧ s % l = 1) :
    ∏ p ∈ N.primeFactors, ab p ≤
      100 / 99 * (1 / (1 - ((1 : ℕ) : ℚ) / ((B : ℚ) - 1))) * (15 / 8) := by
  have hl2 := hl.two_le
  set P := N.primeFactors with hP
  have hP2 : ∀ p ∈ P, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  set G := P.filter (fun p => p ≠ q ∧ p ≠ d) with hG
  have hGP : G ⊆ P := Finset.filter_subset _ _
  have hGm : ∀ p ∈ G, p ∈ P ∧ p ≠ q ∧ p ≠ d := fun p hp => Finset.mem_filter.mp hp
  have hpow : ∀ p ∈ G, ∑ i ∈ Finset.range l, p ^ i =
      r ^ (∑ i ∈ Finset.range l, p ^ i).primeFactorsList.length := by
    intro p hp
    obtain ⟨hpP, hpq, hpd⟩ := hGm p hp
    exact Nat.eq_prime_pow_of_unique_prime_dvd
      (lt_trans zero_lt_one (R_one_lt hl2 (hP2 p hpP))).ne'
      (fun hs hsR => (hr p hpP hpq hpd _ hs hsR).1)
  have hG100 : ∀ p ∈ G, 100 ≤ p := by
    intro p hp
    obtain ⟨hpP, hpq, hpd⟩ := hGm p hp
    by_contra hlt
    push Not at hlt
    have hprime := Nat.prime_of_mem_primeFactors hpP
    have h2 : p ≠ 2 := by
      have := odd_of_mem h hpP
      omega
    have hl' : p ≠ l := by
      rintro rfl
      exact hlN (Nat.dvd_of_mem_primeFactors hpP)
    have hk2 := (hsmall p hprime hlt h2 hl').1
    have hs' : (∑ i ∈ Finset.range l, p ^ i).primeFactors ⊆ {r} := by
      intro x hx
      have := (hr p hpP hpq hpd x (Nat.prime_of_mem_primeFactors hx)
        (Nat.dvd_of_mem_primeFactors hx)).1
      simp [this]
    have := Finset.card_le_card hs'
    rw [Finset.card_singleton] at this
    omega
  have hGb : ∏ p ∈ G, ab p ≤ 100 / 99 * (1 / (1 - ((1 : ℕ) : ℚ) / ((B : ℚ) - 1))) := by
    have nL : (0 : ℚ) ≤ 1 / (1 - ((1 : ℕ) : ℚ) / ((B : ℚ) - 1)) :=
      le_of_lt (one_div_pos.mpr (by linarith))
    by_cases hne : G.Nonempty
    · set m := G.min' hne with hmdef
      have hm : m ∈ G := Finset.min'_mem G hne
      have hmin : ∀ p ∈ G, m ≤ p := fun p hp => Finset.min'_le G p hp
      obtain ⟨hmP, hmq, hmd⟩ := hGm m hm
      -- the receiver is a prime other than `l`
      have hRm := R_one_lt hl2 (hP2 m hmP)
      have hmf := hr m hmP hmq hmd _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd _)
      have hrP : r.Prime := hmf.1 ▸ Nat.minFac_prime (by omega)
      have hrl : r ≠ l := by
        have := hmf.2
        rw [hmf.1] at this
        intro hrl
        rw [hrl, Nat.mod_self] at this
        omega
      have hgrow : ∀ a ∈ G, ∀ b ∈ G, a < b → a ^ (l - 1) < b := fun a ha b hb hab =>
        pow_lt_of_geom_sum_eq_prime_pow hl hrP hrl (Nat.prime_of_mem_primeFactors (hGm a ha).1)
          (Nat.prime_of_mem_primeFactors (hGm b hb).1) hab (hpow a ha) (hpow b hb)
      rw [← Finset.mul_prod_erase G ab hm]
      have h1 : ab m ≤ 100 / 99 := by
        have := ab_anti (a := 100) (by norm_num) (hG100 m hm)
        have e : ab 100 = 100 / 99 := by norm_num [ab]
        rwa [e] at this
      have hsq : ∀ a, 100 ≤ a → a * a ≤ a ^ (l - 1) := fun a ha => by
        rw [← pow_two]
        exact Nat.pow_le_pow_right (by omega) (by omega)
      have hbig : ∀ p ∈ G.erase m, B < p := by
        intro p hp
        obtain ⟨hpm, hpG⟩ := Finset.mem_erase.mp hp
        have hlt : m < p := lt_of_le_of_ne (hmin p hpG) (Ne.symm hpm)
        have e1 := hgrow m hm p hpG hlt
        have e2 := hsq m (hG100 m hm)
        have e3 : 100 * 100 ≤ m * m := Nat.mul_le_mul (hG100 m hm) (hG100 m hm)
        omega
      have hblock : ∀ j, 1 ≤ j →
          ((G.erase m).filter (fun p => B ^ j < p ∧ p ≤ B ^ (j + 1))).card ≤ 1 := by
        intro j hj
        have hT : B ≤ B ^ j := B_le_pow (by omega) hj
        have side : ∀ a b, a ∈ (G.erase m).filter (fun p => B ^ j < p ∧ p ≤ B ^ (j + 1))
            → b ∈ (G.erase m).filter (fun p => B ^ j < p ∧ p ≤ B ^ (j + 1)) →
            a < b → False := by
          intro a b ha hb hab
          rw [Finset.mem_filter] at ha hb
          have e1 := hgrow a (Finset.mem_of_mem_erase ha.1) b (Finset.mem_of_mem_erase hb.1) hab
          have e2 := hsq a (by omega)
          have e3 : B ^ j * B ≤ a * a :=
            Nat.mul_le_mul (by omega) (by omega)
          have e4 : B ^ (j + 1) = B ^ j * B := pow_succ _ _
          omega
        rw [Finset.card_le_one]
        intro a ha b hb
        by_contra hab
        rcases lt_or_gt_of_ne hab with hlt | hlt
        · exact side a b ha hb hlt
        · exact side b a hb ha hlt
      have hsum := sum_inv_pred_le_of_interval_card (by omega) hbig hblock
      have h2 := prod_ab_le_of_sum (fun p hp => by have := hbig p hp; omega) hsum hc1
      exact mul_le_mul h1 h2
        (prod_ab_nonneg fun p hp => hP2 p (hGP (Finset.mem_of_mem_erase hp))) (by norm_num)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.prod_empty]
      have : (1 : ℚ) ≤ 1 / (1 - ((1 : ℕ) : ℚ) / ((B : ℚ) - 1)) := by
        have hB' : (100 : ℚ) ≤ B := by exact_mod_cast hB
        have h0 : (0 : ℚ) ≤ ((1 : ℕ) : ℚ) / ((B : ℚ) - 1) := by
          rw [Nat.cast_one]
          exact le_of_lt (one_div_pos.mpr (by linarith))
        rw [le_div_iff₀ (by linarith)]
        linarith
      nlinarith
  have hE : ∏ p ∈ P.filter (fun p => ¬ (p ≠ q ∧ p ≠ d)), ab p ≤ 15 / 8 := by
    refine prod_ab_le_pair (fun x hx => ?_) ?_
    · have hxP := (Finset.mem_filter.mp hx).1
      have h1 := odd_of_mem h hxP
      have h2 := hP2 x hxP
      exact ⟨by omega, h1⟩
    · refine (Finset.card_le_card (t := {q, d}) (fun x hx => ?_)).trans Finset.card_le_two
      rw [Finset.mem_filter] at hx
      have : x = q ∨ x = d := by tauto
      rcases this with rfl | rfl <;> simp
  have e1 : (∏ p ∈ G, ab p) * (∏ p ∈ P.filter (fun p => ¬ (p ≠ q ∧ p ≠ d)), ab p) =
      ∏ p ∈ P, ab p := Finset.prod_filter_mul_prod_filter_not P _ ab
  rw [← e1]
  have nL : (0 : ℚ) ≤ 1 / (1 - ((1 : ℕ) : ℚ) / ((B : ℚ) - 1)) :=
    le_of_lt (one_div_pos.mpr (by linarith))
  exact mul_le_mul hGb hE (prod_ab_nonneg fun p hp => hP2 p (Finset.filter_subset _ _ hp))
    (mul_nonneg (by norm_num) nL)

/-! ## The main statement with its finite facts as hypotheses -/

/-- Let `l` be a prime with `l - 1 = 2 k`, `k ≥ 2`, and let `q` and `d` be arbitrary natural
numbers. Given the finite facts about the rows of the odd primes below `100`, the least prime
`r0` that is `1` modulo `l`, a set `M` covering the primes of `[100, B]` and the two numerical
bounds, every odd perfect number `N` all of whose prime factors other than `q` and `d` have an
index divisible by `l` is divisible by `l`. Restricted result; no published source was checked;
novelty not verified. -/
theorem dvd_of_two_exceptions_gen {l B k m r0 : ℕ} {E M : Finset ℕ} {N q d : ℕ}
    (hl : l.Prime) (hk : 2 * k = l - 1) (hk2 : 2 ≤ k) (hB : 100 ≤ B) (hB4 : B < 10000)
    (hsmall : ∀ p, p.Prime → p < 100 → p ≠ 2 → p ≠ l →
      2 ≤ (∑ i ∈ Finset.range l, p ^ i).primeFactors.card ∧
      (3 ≤ (∑ i ∈ Finset.range l, p ^ i).primeFactors.card ∨ p ∈ E))
    (hE : ∀ p ∈ E, m ≤ p)
    (hcop : ∀ a ∈ E, ∀ b ∈ E, a ≠ b →
      Nat.gcd (∑ i ∈ Finset.range l, a ^ i) (∑ i ∈ Finset.range l, b ^ i) = 1)
    (hr0 : ∀ x, x.Prime → x % l = 1 → r0 ≤ x) (hr02 : 2 ≤ r0) (hm2 : 2 ≤ m)
    (hM : ∀ p, p.Prime → 100 ≤ p → p ≤ B → p ∈ M) (hM2 : ∀ p ∈ M, 2 ≤ p)
    (hc1 : ((2 * (l - 1) : ℕ) : ℚ) / ((B : ℚ) - 1) < 1)
    (hnumA : ab m * ((∏ p ∈ M, ab p) *
      (1 / (1 - ((2 * (l - 1) : ℕ) : ℚ) / ((B : ℚ) - 1)))) * ab r0 ^ 2 < 2)
    (hc1' : ((1 : ℕ) : ℚ) / ((B : ℚ) - 1) < 1)
    (hnumB : 100 / 99 * (1 / (1 - ((1 : ℕ) : ℚ) / ((B : ℚ) - 1))) * (15 / 8) < 2)
    (h : OddPerfect N)
    (hcomp : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ d → l ∣ N.factorization p + 1) :
    l ∣ N := by
  by_contra hlN
  have hl2 : l ≠ 2 := by omega
  have H4' : (2 : ℚ) < ∏ p ∈ N.primeFactors, ab p := two_lt_prod_primeFactors_div h
  by_cases hab : q % l = 1 ∧ d % l = 1
  · have := case_a hl hk hk2 hB hsmall hE hcop hr0 hr02 hm2 hM hM2 hc1 h hlN hab.1 hab.2
      (fun p hp hpq hpd s hs hsR => (key hl hl2 h hlN hcomp hp hpq hpd hs hsR).2.1)
    linarith
  · obtain ⟨r, hr⟩ : ∃ r, ∀ p ∈ N.primeFactors, p ≠ q → p ≠ d → ∀ s, s.Prime →
        s ∣ ∑ i ∈ Finset.range l, p ^ i → s = r ∧ s % l = 1 := by
      by_cases hq1 : q % l = 1
      · refine ⟨q, fun p hp hpq hpd s hs hsR => ?_⟩
        obtain ⟨-, hsqd, hsl⟩ := key hl hl2 h hlN hcomp hp hpq hpd hs hsR
        refine ⟨?_, hsl⟩
        rcases hsqd with h1 | h1
        · exact h1
        · subst h1
          exact absurd ⟨hq1, hsl⟩ hab
      · refine ⟨d, fun p hp hpq hpd s hs hsR => ?_⟩
        obtain ⟨-, hsqd, hsl⟩ := key hl hl2 h hlN hcomp hp hpq hpd hs hsR
        refine ⟨?_, hsl⟩
        rcases hsqd with h1 | h1
        · subst h1
          exact absurd hsl hq1
        · exact h1
    have := case_b hl (by omega) hB hB4 hsmall hc1' h hlN r hr
    linarith

end OddPerfect.TwoExcGen

#print axioms OddPerfect.TwoExcGen.cardLB_le
#print axioms OddPerfect.TwoExcGen.mem_bigList
#print axioms OddPerfect.TwoExcGen.prod_bigList
#print axioms OddPerfect.TwoExcGen.key
#print axioms OddPerfect.TwoExcGen.case_a
#print axioms OddPerfect.TwoExcGen.case_b
#print axioms OddPerfect.TwoExcGen.dvd_of_two_exceptions_gen
