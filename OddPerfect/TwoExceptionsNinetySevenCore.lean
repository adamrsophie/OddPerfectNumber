import OddPerfect.TwoExceptionsNinetySevenData
import OddPerfect.Seed.Example
import OddPerfect.Seed.Starter
import OddPerfect.Cyclotomic

/-!
# Two exceptions at the prime 97: the argument with its five inputs as hypotheses

Write `R(x) = ∑ i ∈ Finset.range 97, x ^ i`. Let `q` and `d` be arbitrary natural numbers and
let `N` be an odd perfect number with `97 ∤ N` such that every prime factor `p` of `N` other
than `q` and `d` has `97 ∣ e_p + 1`. Call `G` the set of these prime factors. For `p ∈ G`
every prime factor of `R(p)` divides `N`, is `1` modulo `97` and lies outside `G`, so it is `q`
or `d`.

* If `q` and `d` are both `1` modulo `97`, the prime factors of `N` below `100` number at most
  one and are at least `19` (data module), those in `[100, 1600]` are among the listed
  primes, and those above `1600` number at most `192` in each interval
  `(1600 ^ j, 1600 ^ (j + 1)]`; the product of `p / (p - 1)` stays below `2`.
* Otherwise all rows `R(p)`, `p ∈ G`, are powers of one prime `r`. Then `G` has no element
  below `100`, and above its least element the elements grow faster than a power `96`; the
  product of `p / (p - 1)` is at most `(15/8) (100/99) (1599/1598) < 2`.

Restricted result; no published source was checked; novelty not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect.TwoExc97

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

theorem ab_3 : ab 3 = 3 / 2 := by norm_num [ab]
theorem ab_5 : ab 5 = 5 / 4 := by norm_num [ab]
theorem ab_19 : ab 19 = 19 / 18 := by norm_num [ab]
theorem ab_100 : ab 100 = 100 / 99 := by norm_num [ab]
theorem ab_389 : ab 389 = 389 / 388 := by norm_num [ab]

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
theorem prod_ab_le_of_sum
    (H3 : ∀ (s : Finset ℕ) (x : ℕ → ℚ), (∀ i ∈ s, 0 ≤ x i) → ∑ i ∈ s, x i < 1 →
      ∏ i ∈ s, (1 + x i) ≤ 1 / (1 - ∑ i ∈ s, x i))
    {s : Finset ℕ} (hs : ∀ p ∈ s, 2 ≤ p) {c : ℚ}
    (hc : ∑ p ∈ s, (1 : ℚ) / ((p : ℚ) - 1) ≤ c) (hc1 : c < 1) :
    ∏ p ∈ s, ab p ≤ 1 / (1 - c) := by
  have hpos : ∀ p ∈ s, (0 : ℚ) ≤ 1 / ((p : ℚ) - 1) := fun p hp => by
    have : (2 : ℚ) ≤ p := by exact_mod_cast hs p hp
    exact le_of_lt (one_div_pos.mpr (by linarith))
  have hsum : ∑ p ∈ s, (1 : ℚ) / ((p : ℚ) - 1) < 1 := lt_of_le_of_lt hc hc1
  have h := H3 s (fun p => 1 / ((p : ℚ) - 1)) hpos hsum
  beta_reduce at h
  rw [Finset.prod_congr rfl (fun p hp => ab_eq (hs p hp))]
  exact h.trans (one_div_le_one_div_of_le (by linarith) (by linarith))

/-- The product over the listed primes of `[100, 1600]`. -/
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

theorem denL_pos : 0 < denL := by
  rcases Nat.eq_zero_or_pos denL with h | h
  · have := numeric_two
    rw [h] at this
    simp at this
  · exact h

theorem prod_bigPrimes : ∏ p ∈ bigPrimes.toFinset, ab p = (numL : ℚ) / denL := by
  rw [List.prod_toFinset _ bigPrimes_nodup]
  have h2 : ∀ p ∈ bigPrimes, 2 ≤ p := fun p hp => by
    have := mem_bigPrimes_iff hp
    omega
  have hd : (denL : ℚ) ≠ 0 := by exact_mod_cast denL_pos.ne'
  rw [eq_div_iff hd]
  exact list_prod_ab bigPrimes h2

theorem numeric_a :
    19 / 18 * ((numL : ℚ) / denL * (1599 / 1407)) * (389 / 388) ^ 2 < 2 := by
  have hd : (0 : ℚ) < denL := by exact_mod_cast denL_pos
  have hk : ((389 ^ 2 * 19 * 1599 * numL : ℕ) : ℚ) < ((2 * 388 ^ 2 * 18 * 1407 * denL : ℕ) : ℚ) :=
    by exact_mod_cast numeric_two
  push_cast at hk
  have hq : (numL : ℚ) / denL < 2 * (388 ^ 2 * 18 * 1407) / (389 ^ 2 * 19 * 1599) := by
    rw [div_lt_iff₀ hd]
    linarith
  have e : 19 / 18 * ((numL : ℚ) / denL * (1599 / 1407)) * (389 / 388) ^ 2 =
      (19 / 18 * (1599 / 1407) * (389 / 388) ^ 2) * ((numL : ℚ) / denL) := by ring
  rw [e]
  calc (19 / 18 * (1599 / 1407) * (389 / 388) ^ 2) * ((numL : ℚ) / denL)
      < (19 / 18 * (1599 / 1407) * (389 / 388) ^ 2) *
          (2 * (388 ^ 2 * 18 * 1407) / (389 ^ 2 * 19 * 1599)) :=
        mul_lt_mul_of_pos_left hq (by norm_num)
    _ = 2 := by norm_num

/-! ## Number theory -/

theorem R_eq_sigma {p : ℕ} (hp : p.Prime) : ∑ i ∈ Finset.range 97, p ^ i = σ 1 (p ^ 96) :=
  (sigma_one_apply_prime_pow hp).symm

theorem dvd_R_of_mod {s : ℕ} (hs : s % 97 = 1) : 97 ∣ ∑ i ∈ Finset.range 97, s ^ i := by
  apply Nat.dvd_of_mod_eq_zero
  rw [Finset.sum_nat_mod]
  have : ∀ i ∈ Finset.range 97, s ^ i % 97 = 1 := fun i _ => by
    rw [Nat.pow_mod, hs]
    simp
  rw [Finset.sum_congr rfl this]
  simp

theorem R_ge (p : ℕ) : p ^ 96 ≤ ∑ i ∈ Finset.range 97, p ^ i :=
  Finset.single_le_sum (f := fun i => p ^ i) (fun i _ => Nat.zero_le _)
    (Finset.mem_range.mpr (by norm_num))

theorem R_one_lt {p : ℕ} (hp : 2 ≤ p) : 1 < ∑ i ∈ Finset.range 97, p ^ i := by
  have h1 := R_ge p
  have h2 : 2 ^ 96 ≤ p ^ 96 := Nat.pow_le_pow_left hp 96
  have h3 : 1 < 2 ^ 96 := by norm_num
  omega

theorem odd_of_mem {N p : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors) : p % 2 = 1 := by
  rcases (Nat.prime_of_mem_primeFactors hp).eq_two_or_odd with h2 | h2
  · subst h2
    obtain ⟨k, hk⟩ := Nat.dvd_of_mem_primeFactors hp
    have := Nat.odd_iff.mp h.1
    omega
  · exact h2

theorem ge_389 {x : ℕ} (hx : x.Prime) (h1 : x % 97 = 1) : 389 ≤ x := by
  by_contra hlt
  have : x = 1 ∨ x = 98 ∨ x = 195 ∨ x = 292 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> norm_num at hx

/-- Every prime factor of the row of an ordinary prime is a prime factor of `N`, equal to `q`
or `d`, and `1` modulo `97`. -/
theorem key {N q d : ℕ} (h : OddPerfect N) (h97 : ¬ 97 ∣ N)
    (hcomp : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ d → 97 ∣ N.factorization p + 1)
    {p : ℕ} (hp : p ∈ N.primeFactors) (hpq : p ≠ q) (hpd : p ≠ d) {s : ℕ} (hs : s.Prime)
    (hsR : s ∣ ∑ i ∈ Finset.range 97, p ^ i) :
    s ∈ N.primeFactors ∧ (s = q ∨ s = d) ∧ s % 97 = 1 := by
  have hpP := Nat.prime_of_mem_primeFactors hp
  have hN := h.ne_zero
  have p97 : Nat.Prime 97 := by norm_num
  have hdv : σ 1 (p ^ 96) ∣ σ 1 (p ^ N.factorization p) :=
    OPNExample.sigma_prime_pow_dvd (a := 96) hpP (by exact hcomp p hp hpq hpd)
  rw [R_eq_sigma hpP] at hsR
  have hs97 : s % 97 = 1 := by
    rcases prime_dvd_sigma_prime_pow_of_prime_length hpP hs p97 (by exact hsR) with h1 | h1
    · subst h1
      exact absurd (OPNStarter.force_prime h.perfect hpP rfl p97 (by norm_num)
        (hsR.trans hdv)) h97
    · exact h1
  have hs2 : s ≠ 2 := by
    intro h2
    rw [h2] at hs97
    norm_num at hs97
  have hsN : s ∣ N := OPNStarter.force_prime h.perfect hpP rfl hs hs2 (hsR.trans hdv)
  have hsP : s ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hs, hsN, hN⟩
  refine ⟨hsP, ?_, hs97⟩
  by_contra hne
  have hne' := not_or.mp hne
  have hd2 : σ 1 (s ^ 96) ∣ σ 1 (s ^ N.factorization s) :=
    OPNExample.sigma_prime_pow_dvd (a := 96) hs (by exact hcomp s hsP hne'.1 hne'.2)
  have h97s : 97 ∣ σ 1 (s ^ 96) := by
    rw [← R_eq_sigma hs]
    exact dvd_R_of_mod hs97
  exact h97 (OPNStarter.force_prime h.perfect hs rfl p97 (by norm_num) (h97s.trans hd2))

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

/-- At most `96` elements of a block belong to one receiver. -/
theorem blockCount
    (H1 : ∀ {r k a : ℕ}, r.Prime → r ≠ 97 → 0 < k →
      ((Finset.Ioc a (a + r ^ k)).filter
        (fun x => r ^ k ∣ ∑ i ∈ Finset.range 97, x ^ i)).card ≤ 96)
    {S : Finset ℕ} {T r : ℕ} (hT : 1600 ≤ T) (hS : ∀ x ∈ S, T < x ∧ x ≤ T * 1600)
    (hr97 : r ≠ 97) :
    (S.filter (fun x => T ^ 48 ≤ r ^ (∑ i ∈ Finset.range 97, x ^ i).factorization r)).card
      ≤ 96 := by
  have hT48 : 1 < T ^ 48 := Nat.one_lt_pow (by norm_num) (by omega)
  by_cases hr : r.Prime
  · have hr1 := hr.one_lt
    have hk0 : 0 < Nat.clog r (T ^ 48) := Nat.clog_pos hr1 hT48
    refine le_trans (Finset.card_le_card ?_) (H1 (a := T) hr hr97 hk0)
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    obtain ⟨hxS, hx48⟩ := hx
    obtain ⟨h1, h2⟩ := hS x hxS
    have hkle : Nat.clog r (T ^ 48) ≤ (∑ i ∈ Finset.range 97, x ^ i).factorization r :=
      (Nat.clog_le_iff_le_pow hr1).mpr hx48
    have hpowk : T ^ 48 ≤ r ^ Nat.clog r (T ^ 48) := Nat.le_pow_clog hr1 _
    have hTT : T * 1600 ≤ T + T ^ 48 := by
      have e1 : T * T ≤ T ^ 48 := by
        rw [← pow_two]
        exact Nat.pow_le_pow_right (by omega) (by norm_num)
      have e2 : T * 1600 ≤ T * T := Nat.mul_le_mul_left T hT
      omega
    refine ⟨Finset.mem_Ioc.mpr ⟨h1, by omega⟩, ?_⟩
    exact (Nat.pow_dvd_pow r hkle).trans (Nat.ordProj_dvd _ r)
  · have hE : S.filter (fun x => T ^ 48 ≤ r ^ (∑ i ∈ Finset.range 97, x ^ i).factorization r)
        = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x _ hx
      rw [Nat.factorization_eq_zero_of_not_prime _ hr, pow_zero] at hx
      omega
    rw [hE]
    simp

/-! ## Two receivers -/

theorem case_a
    (H1 : ∀ {r k a : ℕ}, r.Prime → r ≠ 97 → 0 < k →
      ((Finset.Ioc a (a + r ^ k)).filter
        (fun x => r ^ k ∣ ∑ i ∈ Finset.range 97, x ^ i)).card ≤ 96)
    (H3 : ∀ (s : Finset ℕ) (x : ℕ → ℚ), (∀ i ∈ s, 0 ≤ x i) → ∑ i ∈ s, x i < 1 →
      ∏ i ∈ s, (1 + x i) ≤ 1 / (1 - ∑ i ∈ s, x i))
    (H5 : ∀ (s : Finset ℕ) (c : ℕ), (∀ p ∈ s, 1600 < p) →
      (∀ j, 1 ≤ j → (s.filter (fun p => 1600 ^ j < p ∧ p ≤ 1600 ^ (j + 1))).card ≤ c) →
      ∑ p ∈ s, (1 : ℚ) / ((p : ℚ) - 1) ≤ (c : ℚ) / (((1600 : ℕ) : ℚ) - 1))
    {N q d : ℕ} (h : OddPerfect N) (h97 : ¬ 97 ∣ N) (hq1 : q % 97 = 1) (hd1 : d % 97 = 1)
    (hk : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ d → ∀ s, s.Prime →
      s ∣ ∑ i ∈ Finset.range 97, p ^ i → s = q ∨ s = d) :
    ∏ p ∈ N.primeFactors, ab p ≤
      19 / 18 * ((numL : ℚ) / denL * (1599 / 1407)) * (389 / 388) ^ 2 := by
  set P := N.primeFactors with hP
  have hP2 : ∀ p ∈ P, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  set G := P.filter (fun p => p ≠ q ∧ p ≠ d) with hG
  have hGP : G ⊆ P := Finset.filter_subset _ _
  have hGm : ∀ p ∈ G, p ∈ P ∧ p ≠ q ∧ p ≠ d := fun p hp => Finset.mem_filter.mp hp
  -- the rows of elements of `G`
  have hsub : ∀ p ∈ G, (∑ i ∈ Finset.range 97, p ^ i).primeFactors ⊆ {q, d} := by
    intro p hp x hx
    obtain ⟨hpP, hpq, hpd⟩ := hGm p hp
    have := hk p hpP hpq hpd x (Nat.prime_of_mem_primeFactors hx)
      (Nat.dvd_of_mem_primeFactors hx)
    rcases this with rfl | rfl <;> simp
  have hRne : ∀ p ∈ G, (∑ i ∈ Finset.range 97, p ^ i) ≠ 0 := fun p hp =>
    (lt_trans zero_lt_one (R_one_lt (hP2 p (hGP hp)))).ne'
  -- exceptional part
  have hE : ∏ p ∈ P.filter (fun p => ¬ (p ≠ q ∧ p ≠ d)), ab p ≤ (389 / 388) ^ 2 := by
    rw [← ab_389]
    refine prod_ab_le_pow (by norm_num) (fun x hx => ?_) ?_
    · rw [Finset.mem_filter] at hx
      have hxp := Nat.prime_of_mem_primeFactors hx.1
      have : x = q ∨ x = d := by tauto
      rcases this with rfl | rfl
      · exact ge_389 hxp hq1
      · exact ge_389 hxp hd1
    · refine (Finset.card_le_card (t := {q, d}) (fun x hx => ?_)).trans Finset.card_le_two
      rw [Finset.mem_filter] at hx
      have : x = q ∨ x = d := by tauto
      rcases this with rfl | rfl <;> simp
  -- small part
  set Gs := G.filter (fun p => p < 100) with hGs
  have hsev : ∀ p ∈ Gs, p ∈ seven ∧ (Rv p).primeFactors = {q, d} := by
    intro p hp
    obtain ⟨hpG, hlt⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpP, hpq, hpd⟩ := hGm p hpG
    have hprime := Nat.prime_of_mem_primeFactors hpP
    have h2 : p ≠ 2 := by
      have := odd_of_mem h hpP
      omega
    have h97' : p ≠ 97 := by
      rintro rfl
      exact h97 (Nat.dvd_of_mem_primeFactors hpP)
    have hm := mem_small23 hprime hlt h2 h97'
    have hc := kOf_le_card hm
    have hf := kOf_facts p hm
    have hs' : (Rv p).primeFactors ⊆ {q, d} := by
      rw [← geom_eq_Rv hprime.two_le]
      exact hsub p hpG
    have hcard := (Finset.card_le_card hs').trans Finset.card_le_two
    refine ⟨?_, ?_⟩
    · rcases hf.2 with h3 | h3
      · omega
      · exact h3
    · exact Finset.eq_of_subset_of_card_le hs' (Finset.card_le_two.trans (by omega))
  have hGsb : ∏ p ∈ Gs, ab p ≤ 19 / 18 := by
    rw [← ab_19, ← pow_one (ab 19)]
    refine prod_ab_le_pow (by norm_num) (fun p hp => seven_ge p (hsev p hp).1) ?_
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    have g := seven_coprime a (hsev a ha).1 b (hsev b hb).1 hab
    have hqa : q ∈ (Rv a).primeFactors := by rw [(hsev a ha).2]; simp
    have hqb : q ∈ (Rv b).primeFactors := by rw [(hsev b hb).2]; simp
    have hdv := Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hqa) (Nat.dvd_of_mem_primeFactors hqb)
    rw [g] at hdv
    exact (Nat.prime_of_mem_primeFactors hqa).one_lt.ne' (Nat.dvd_one.mp hdv)
  -- middle part
  set Gr := G.filter (fun p => ¬ p < 100) with hGr
  set Gm := Gr.filter (fun p => p ≤ 1600) with hGm'
  set Gb := Gr.filter (fun p => ¬ p ≤ 1600) with hGb
  have hGrG : Gr ⊆ G := Finset.filter_subset _ _
  have hGmb : ∏ p ∈ Gm, ab p ≤ (numL : ℚ) / denL := by
    rw [← prod_bigPrimes]
    refine prod_ab_mono (fun p hp => ?_) (fun p hp => ?_)
    · obtain ⟨hpGr, hle⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpG, hlt⟩ := Finset.mem_filter.mp hpGr
      rw [List.mem_toFinset]
      exact mem_bigPrimes (Nat.prime_of_mem_primeFactors (hGm p hpG).1) (by omega) hle
    · have := mem_bigPrimes_iff (List.mem_toFinset.mp hp)
      omega
  -- large part
  have hGbb : ∏ p ∈ Gb, ab p ≤ 1599 / 1407 := by
    have hbig : ∀ p ∈ Gb, 1600 < p := fun p hp => by
      have := (Finset.mem_filter.mp hp).2
      omega
    have hblock : ∀ j, 1 ≤ j →
        (Gb.filter (fun p => 1600 ^ j < p ∧ p ≤ 1600 ^ (j + 1))).card ≤ 192 := by
      intro j hj
      set T := 1600 ^ j with hTdef
      have hT : 1600 ≤ T := by
        rw [hTdef]
        calc 1600 = 1600 ^ 1 := (pow_one _).symm
          _ ≤ 1600 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      set Blk := Gb.filter (fun p => T < p ∧ p ≤ 1600 ^ (j + 1)) with hBlk
      have hBS : ∀ x ∈ Blk, T < x ∧ x ≤ T * 1600 := by
        intro x hx
        have hx' := (Finset.mem_filter.mp hx).2
        rw [hTdef, ← pow_succ]
        exact hx'
      have hBG : ∀ x ∈ Blk, x ∈ G := fun x hx =>
        hGrG (Finset.filter_subset _ _ (Finset.filter_subset _ _ hx))
      have hcover : Blk ⊆
          Blk.filter (fun x => T ^ 48 ≤ q ^ (∑ i ∈ Finset.range 97, x ^ i).factorization q) ∪
          Blk.filter (fun x => T ^ 48 ≤ d ^ (∑ i ∈ Finset.range 97, x ^ i).factorization d) := by
        intro x hx
        have hxG := hBG x hx
        have hle := le_mul_of_pf_subset (hRne x hxG) (hsub x hxG)
        have hlt : T ^ 96 < ∑ i ∈ Finset.range 97, x ^ i :=
          lt_of_lt_of_le (Nat.pow_lt_pow_left (hBS x hx).1 (by norm_num)) (R_ge x)
        by_cases h1 : T ^ 48 ≤ q ^ (∑ i ∈ Finset.range 97, x ^ i).factorization q
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h1⟩)
        by_cases h2 : T ^ 48 ≤ d ^ (∑ i ∈ Finset.range 97, x ^ i).factorization d
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, h2⟩)
        exfalso
        have := Nat.mul_lt_mul'' (not_le.mp h1) (not_le.mp h2)
        have hTT : T ^ 48 * T ^ 48 = T ^ 96 := by rw [← pow_add]
        omega
      have hq97 : q ≠ 97 := by omega
      have hd97 : d ≠ 97 := by omega
      calc (Gb.filter (fun p => 1600 ^ j < p ∧ p ≤ 1600 ^ (j + 1))).card = Blk.card := rfl
        _ ≤ _ := Finset.card_le_card hcover
        _ ≤ _ := Finset.card_union_le _ _
        _ ≤ 96 + 96 := Nat.add_le_add (blockCount H1 hT hBS hq97) (blockCount H1 hT hBS hd97)
        _ = 192 := by norm_num
    have hsum := H5 Gb 192 hbig hblock
    have hsum' : ∑ p ∈ Gb, (1 : ℚ) / ((p : ℚ) - 1) ≤ 192 / 1599 :=
      hsum.trans (le_of_eq (by norm_num))
    have := prod_ab_le_of_sum H3 (fun p hp => by have := hbig p hp; omega) hsum'
      (by norm_num)
    calc ∏ p ∈ Gb, ab p ≤ 1 / (1 - 192 / 1599) := this
      _ = 1599 / 1407 := by norm_num
  -- assemble
  have e1 : (∏ p ∈ G, ab p) * (∏ p ∈ P.filter (fun p => ¬ (p ≠ q ∧ p ≠ d)), ab p) =
      ∏ p ∈ P, ab p := Finset.prod_filter_mul_prod_filter_not P _ ab
  have e2 : (∏ p ∈ Gs, ab p) * (∏ p ∈ Gr, ab p) = ∏ p ∈ G, ab p :=
    Finset.prod_filter_mul_prod_filter_not G _ ab
  have e3 : (∏ p ∈ Gm, ab p) * (∏ p ∈ Gb, ab p) = ∏ p ∈ Gr, ab p :=
    Finset.prod_filter_mul_prod_filter_not Gr _ ab
  have n1 : 0 ≤ ∏ p ∈ Gs, ab p :=
    prod_ab_nonneg fun p hp => hP2 p (hGP (Finset.filter_subset _ _ hp))
  have n2 : 0 ≤ ∏ p ∈ Gm, ab p :=
    prod_ab_nonneg fun p hp => hP2 p (hGP (hGrG (Finset.filter_subset _ _ hp)))
  have n3 : 0 ≤ ∏ p ∈ Gb, ab p :=
    prod_ab_nonneg fun p hp => hP2 p (hGP (hGrG (Finset.filter_subset _ _ hp)))
  have n4 : 0 ≤ ∏ p ∈ P.filter (fun p => ¬ (p ≠ q ∧ p ≠ d)), ab p :=
    prod_ab_nonneg fun p hp => hP2 p (Finset.filter_subset _ _ hp)
  have hd : (0 : ℚ) ≤ (numL : ℚ) / denL := by positivity
  rw [← e1, ← e2, ← e3]
  have b3 : (∏ p ∈ Gm, ab p) * ∏ p ∈ Gb, ab p ≤ (numL : ℚ) / denL * (1599 / 1407) :=
    mul_le_mul hGmb hGbb n3 hd
  have b2 : (∏ p ∈ Gs, ab p) * ((∏ p ∈ Gm, ab p) * ∏ p ∈ Gb, ab p) ≤
      19 / 18 * ((numL : ℚ) / denL * (1599 / 1407)) :=
    mul_le_mul hGsb b3 (mul_nonneg n2 n3) (by norm_num)
  exact mul_le_mul b2 hE n4 (by positivity)

/-! ## One receiver -/

theorem case_b
    (H2 : ∀ {r p₁ p₂ b₁ b₂ : ℕ}, r.Prime → r ≠ 97 → p₁.Prime → p₂.Prime → p₁ < p₂ →
      ∑ i ∈ Finset.range 97, p₁ ^ i = r ^ b₁ → ∑ i ∈ Finset.range 97, p₂ ^ i = r ^ b₂ →
      p₁ ^ 96 < p₂)
    (H3 : ∀ (s : Finset ℕ) (x : ℕ → ℚ), (∀ i ∈ s, 0 ≤ x i) → ∑ i ∈ s, x i < 1 →
      ∏ i ∈ s, (1 + x i) ≤ 1 / (1 - ∑ i ∈ s, x i))
    (H5 : ∀ (s : Finset ℕ) (c : ℕ), (∀ p ∈ s, 1600 < p) →
      (∀ j, 1 ≤ j → (s.filter (fun p => 1600 ^ j < p ∧ p ≤ 1600 ^ (j + 1))).card ≤ c) →
      ∑ p ∈ s, (1 : ℚ) / ((p : ℚ) - 1) ≤ (c : ℚ) / (((1600 : ℕ) : ℚ) - 1))
    {N q d : ℕ} (h : OddPerfect N) (h97 : ¬ 97 ∣ N) (r : ℕ)
    (hr : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ d → ∀ s, s.Prime →
      s ∣ ∑ i ∈ Finset.range 97, p ^ i → s = r ∧ s % 97 = 1) :
    ∏ p ∈ N.primeFactors, ab p ≤ 100 / 99 * (1599 / 1598) * (15 / 8) := by
  set P := N.primeFactors with hP
  have hP2 : ∀ p ∈ P, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  set G := P.filter (fun p => p ≠ q ∧ p ≠ d) with hG
  have hGP : G ⊆ P := Finset.filter_subset _ _
  have hGm : ∀ p ∈ G, p ∈ P ∧ p ≠ q ∧ p ≠ d := fun p hp => Finset.mem_filter.mp hp
  have hpow : ∀ p ∈ G, ∑ i ∈ Finset.range 97, p ^ i =
      r ^ (∑ i ∈ Finset.range 97, p ^ i).primeFactorsList.length := by
    intro p hp
    obtain ⟨hpP, hpq, hpd⟩ := hGm p hp
    exact Nat.eq_prime_pow_of_unique_prime_dvd
      (lt_trans zero_lt_one (R_one_lt (hP2 p hpP))).ne'
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
    have h97' : p ≠ 97 := by
      rintro rfl
      exact h97 (Nat.dvd_of_mem_primeFactors hpP)
    have hm := mem_small23 hprime hlt h2 h97'
    have hc := kOf_le_card hm
    have hk2 := (kOf_facts p hm).1
    have hs' : (Rv p).primeFactors ⊆ {r} := by
      intro x hx
      have hx' := Nat.dvd_of_mem_primeFactors hx
      rw [← geom_eq_Rv hprime.two_le] at hx'
      have := (hr p hpP hpq hpd x (Nat.prime_of_mem_primeFactors hx) hx').1
      simp [this]
    have := Finset.card_le_card hs'
    rw [Finset.card_singleton] at this
    omega
  have hGb : ∏ p ∈ G, ab p ≤ 100 / 99 * (1599 / 1598) := by
    by_cases hne : G.Nonempty
    · set m := G.min' hne with hmdef
      have hm : m ∈ G := Finset.min'_mem G hne
      have hmin : ∀ p ∈ G, m ≤ p := fun p hp => Finset.min'_le G p hp
      obtain ⟨hmP, hmq, hmd⟩ := hGm m hm
      have hmprime := Nat.prime_of_mem_primeFactors hmP
      -- the receiver is a prime other than 97
      have hRm := R_one_lt (hP2 m hmP)
      have hmf := hr m hmP hmq hmd _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd _)
      have hrP : r.Prime := hmf.1 ▸ Nat.minFac_prime (by omega)
      have hr97 : r ≠ 97 := by
        have := hmf.2
        rw [hmf.1] at this
        omega
      have hgrow : ∀ a ∈ G, ∀ b ∈ G, a < b → a ^ 96 < b := fun a ha b hb hab =>
        H2 hrP hr97 (Nat.prime_of_mem_primeFactors (hGm a ha).1)
          (Nat.prime_of_mem_primeFactors (hGm b hb).1) hab (hpow a ha) (hpow b hb)
      rw [← Finset.mul_prod_erase G ab hm]
      have h1 : ab m ≤ 100 / 99 := by
        rw [← ab_100]
        exact ab_anti (by norm_num) (hG100 m hm)
      have hbig : ∀ p ∈ G.erase m, 1600 < p := by
        intro p hp
        obtain ⟨hpm, hpG⟩ := Finset.mem_erase.mp hp
        have hlt : m < p := lt_of_le_of_ne (hmin p hpG) (Ne.symm hpm)
        have e1 := hgrow m hm p hpG hlt
        have e2 : 100 ^ 96 ≤ m ^ 96 := Nat.pow_le_pow_left (hG100 m hm) 96
        have e3 : 1600 < 100 ^ 96 := by norm_num
        omega
      have hblock : ∀ j, 1 ≤ j →
          ((G.erase m).filter (fun p => 1600 ^ j < p ∧ p ≤ 1600 ^ (j + 1))).card ≤ 1 := by
        intro j hj
        have hT : 1600 ≤ 1600 ^ j := by
          calc 1600 = 1600 ^ 1 := (pow_one _).symm
            _ ≤ 1600 ^ j := Nat.pow_le_pow_right (by norm_num) hj
        have side : ∀ a b, a ∈ (G.erase m).filter (fun p => 1600 ^ j < p ∧ p ≤ 1600 ^ (j + 1))
            → b ∈ (G.erase m).filter (fun p => 1600 ^ j < p ∧ p ≤ 1600 ^ (j + 1)) →
            a < b → False := by
          intro a b ha hb hab
          rw [Finset.mem_filter] at ha hb
          have e1 := hgrow a (Finset.mem_of_mem_erase ha.1) b (Finset.mem_of_mem_erase hb.1) hab
          have e2 : a * a ≤ a ^ 96 := by
            rw [← pow_two]
            exact Nat.pow_le_pow_right (by omega) (by norm_num)
          have e3 : 1600 ^ j * 1600 ≤ a * a :=
            Nat.mul_le_mul (by omega) (by omega)
          have e4 : 1600 ^ (j + 1) = 1600 ^ j * 1600 := pow_succ _ _
          omega
        rw [Finset.card_le_one]
        intro a ha b hb
        by_contra hab
        rcases lt_or_gt_of_ne hab with hlt | hlt
        · exact side a b ha hb hlt
        · exact side b a hb ha hlt
      have hsum := H5 (G.erase m) 1 hbig hblock
      have hsum' : ∑ p ∈ G.erase m, (1 : ℚ) / ((p : ℚ) - 1) ≤ 1 / 1599 :=
        hsum.trans (le_of_eq (by norm_num))
      have h2 := prod_ab_le_of_sum H3 (fun p hp => by have := hbig p hp; omega) hsum'
        (by norm_num)
      have h2' : ∏ p ∈ G.erase m, ab p ≤ 1599 / 1598 := by
        calc ∏ p ∈ G.erase m, ab p ≤ 1 / (1 - 1 / 1599) := h2
          _ = 1599 / 1598 := by norm_num
      exact mul_le_mul h1 h2'
        (prod_ab_nonneg fun p hp => hP2 p (hGP (Finset.mem_of_mem_erase hp))) (by norm_num)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.prod_empty]
      norm_num
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
  exact mul_le_mul hGb hE (prod_ab_nonneg fun p hp => hP2 p (Finset.filter_subset _ _ hp))
    (by norm_num)

/-! ## The main statement with its inputs as hypotheses -/

/-- Let `q` and `d` be arbitrary natural numbers. If every prime factor of an odd perfect number
`N` other than `q` and `d` has an index divisible by `97`, then `97 ∣ N`; the five inputs are
hypotheses here. Restricted result; no published source was checked; novelty not verified. -/
theorem ninetyseven_dvd_of_two_exceptions_of {N q d : ℕ}
    (H1 : ∀ {r k a : ℕ}, r.Prime → r ≠ 97 → 0 < k →
      ((Finset.Ioc a (a + r ^ k)).filter
        (fun x => r ^ k ∣ ∑ i ∈ Finset.range 97, x ^ i)).card ≤ 96)
    (H2 : ∀ {r p₁ p₂ b₁ b₂ : ℕ}, r.Prime → r ≠ 97 → p₁.Prime → p₂.Prime → p₁ < p₂ →
      ∑ i ∈ Finset.range 97, p₁ ^ i = r ^ b₁ → ∑ i ∈ Finset.range 97, p₂ ^ i = r ^ b₂ →
      p₁ ^ 96 < p₂)
    (H3 : ∀ (s : Finset ℕ) (x : ℕ → ℚ), (∀ i ∈ s, 0 ≤ x i) → ∑ i ∈ s, x i < 1 →
      ∏ i ∈ s, (1 + x i) ≤ 1 / (1 - ∑ i ∈ s, x i))
    (H4 : (2 : ℚ) < ∏ p ∈ N.primeFactors, ((p : ℚ) / ((p : ℚ) - 1)))
    (H5 : ∀ (s : Finset ℕ) (c : ℕ), (∀ p ∈ s, 1600 < p) →
      (∀ j, 1 ≤ j → (s.filter (fun p => 1600 ^ j < p ∧ p ≤ 1600 ^ (j + 1))).card ≤ c) →
      ∑ p ∈ s, (1 : ℚ) / ((p : ℚ) - 1) ≤ (c : ℚ) / (((1600 : ℕ) : ℚ) - 1))
    (h : OddPerfect N)
    (hcomp : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ d → 97 ∣ N.factorization p + 1) :
    97 ∣ N := by
  by_contra h97
  have H4' : (2 : ℚ) < ∏ p ∈ N.primeFactors, ab p := H4
  by_cases hab : q % 97 = 1 ∧ d % 97 = 1
  · have := case_a H1 H3 H5 h h97 hab.1 hab.2
      (fun p hp hpq hpd s hs hsR => (key h h97 hcomp hp hpq hpd hs hsR).2.1)
    have := numeric_a
    linarith
  · obtain ⟨r, hr⟩ : ∃ r, ∀ p ∈ N.primeFactors, p ≠ q → p ≠ d → ∀ s, s.Prime →
        s ∣ ∑ i ∈ Finset.range 97, p ^ i → s = r ∧ s % 97 = 1 := by
      by_cases hq1 : q % 97 = 1
      · refine ⟨q, fun p hp hpq hpd s hs hsR => ?_⟩
        obtain ⟨-, hsqd, hs97⟩ := key h h97 hcomp hp hpq hpd hs hsR
        refine ⟨?_, hs97⟩
        rcases hsqd with h1 | h1
        · exact h1
        · subst h1
          exact absurd ⟨hq1, hs97⟩ hab
      · refine ⟨d, fun p hp hpq hpd s hs hsR => ?_⟩
        obtain ⟨-, hsqd, hs97⟩ := key h h97 hcomp hp hpq hpd hs hsR
        refine ⟨?_, hs97⟩
        rcases hsqd with h1 | h1
        · subst h1
          exact absurd hs97 hq1
        · exact h1
    have := case_b H2 H3 H5 h h97 r hr
    norm_num at this
    linarith

end OddPerfect.TwoExc97

#print axioms OddPerfect.TwoExc97.key
#print axioms OddPerfect.TwoExc97.case_a
#print axioms OddPerfect.TwoExc97.case_b
#print axioms OddPerfect.TwoExc97.ninetyseven_dvd_of_two_exceptions_of
