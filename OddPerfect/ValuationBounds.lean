import OddPerfect.Valuation
import OddPerfect.ExponentCap

/-!
# Valuation bounds from the number of prime factors

Let `N` be an odd perfect number with `k = ω(N)` distinct prime factors and let `q` be an
odd prime. The `q`-adic ledger `v_q(N) = ∑_{p ≠ q} v_q(σ(p ^ e_p))` is bounded term by term.
A component with `p ≡ 1 (mod q)` contributes `v_q(e_p + 1)`, and `q, q ^ 2, …, q ^ j` are
distinct divisors `≥ 3` of `e_p + 1` when `q ^ j ∣ e_p + 1`, so the fan bound gives
`v_q(e_p + 1) ≤ k - 1`. A component in which `p` has order `d > 1` modulo `q` contributes
`v_q(p ^ d - 1) + v_q((e_p + 1) / d)`, and the second summand is again at most `k - 1`.

* `sum_padicValNat_sigma_le_factorization`: budget overshoot in lower bound form; any set of
  components supplies at most `v_q(N)`.
* `factorization_le_sq_add_sum_orderWeight`: an analogue of Thackeray's Corollary 6, proved
  here directly for odd perfect numbers, `v_q(N) ≤ (k - 1) ^ 2 + ∑_{p ≠ q} orderWeight q p e_p`.
  Thackeray's corollary concerns an odd square with prescribed valuations, so its hypotheses
  differ; this theorem is proved independently and does not rely on it.
* `mod_eq_one_of_dvd_sigma_of_even`: for `q - 1` a power of two, an even exponent component
  divisible by `q` has `p ≡ 1 (mod q)` (Nielsen).
* `factorization_le_of_fermat`: for `q - 1` a power of two,
  `v_q(N) ≤ (k - 1) ^ 2 + v_q(s + 1)` with `s` the special prime.
* `factorization_three_le`: the instance `q = 3`.
* `three_mul_le_of_dvd_sigma`: Brent, Cohen, te Riele, Lemma 1 (Nielsen's Lemma 8).
-/

namespace OddPerfect

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

variable {N : ℕ}

/-! ## Budget overshoot -/

private theorem sum_le_sum_primeFactors (N q : ℕ) (S : Finset ℕ) :
    ∑ p ∈ S, padicValNat q (σ 1 (p ^ N.factorization p)) ≤
      ∑ p ∈ N.primeFactors, padicValNat q (σ 1 (p ^ N.factorization p)) := by
  rw [← Finset.sum_subset (Finset.inter_subset_left (s₁ := S) (s₂ := N.primeFactors))]
  · exact Finset.sum_le_sum_of_subset Finset.inter_subset_right
  · intro p hpS hp
    have hp' : p ∉ N.primeFactors := fun h => hp (Finset.mem_inter.mpr ⟨hpS, h⟩)
    rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp'
    simp [hp']

/-- Budget overshoot, lower bound form: for a perfect number `N` and an odd prime `q`, the
components over any finite set `S` of primes supply at most `v_q(N)`. Primes outside
`N.primeFactors` contribute zero. -/
theorem sum_padicValNat_sigma_le_factorization (hN : N.Perfect) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (S : Finset ℕ) :
    ∑ p ∈ S, padicValNat q (σ 1 (p ^ N.factorization p)) ≤ N.factorization q := by
  refine (sum_le_sum_primeFactors N q S).trans_eq ?_
  rw [← sigmaWeight_sum_eq hN hq hq2]
  exact Finset.sum_congr rfl fun p _ => (sigmaWeight_eq_padicValNat N p hq).symm

/-- Budget overshoot at `2`: for an odd perfect number the components over any finite set
supply at most one factor of `2`. -/
theorem sum_padicValNat_two_sigma_le_one (h : OddPerfect N) (S : Finset ℕ) :
    ∑ p ∈ S, padicValNat 2 (σ 1 (p ^ N.factorization p)) ≤ 1 := by
  refine (sum_le_sum_primeFactors N 2 S).trans_eq ?_
  calc _ = ∑ p ∈ N.primeFactors, sigmaWeight N p 2 :=
        Finset.sum_congr rfl fun p _ => (sigmaWeight_eq_padicValNat N p Nat.prime_two).symm
    _ = 1 := sigmaWeight_sum_two h

/-! ## The fan bound for `q`-adic valuations of `e + 1` -/

/-- A divisor `n'` of `n ≠ 0` has `q`-adic valuation at most the number of divisors `≥ 3`
of `n`, for a prime `q ≥ 3`: the powers `q, …, q ^ v_q(n')` are such divisors. -/
private theorem padicValNat_le_card_filter {q n n' : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q)
    (hn : n ≠ 0) (hn' : n' ∣ n) :
    padicValNat q n' ≤ ((Nat.divisors n).filter (3 ≤ ·)).card := by
  have : Fact q.Prime := ⟨hq⟩
  calc padicValNat q n' = ((Finset.range (padicValNat q n')).image fun i => q ^ (i + 1)).card := by
        rw [Finset.card_image_of_injective _ ?_, Finset.card_range]
        intro a b hab
        have := Nat.pow_right_injective hq.two_le hab
        omega
    _ ≤ _ := by
        apply Finset.card_le_card
        intro d hd
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
        rw [Finset.mem_range] at hi
        rw [Finset.mem_filter, Nat.mem_divisors]
        refine ⟨⟨(pow_dvd_pow q (by omega)).trans (pow_padicValNat_dvd.trans hn'), hn⟩, ?_⟩
        calc 3 ≤ q ^ 1 := by rw [pow_one]; exact hq3
          _ ≤ q ^ (i + 1) := Nat.pow_le_pow_right hq.pos (by omega)

/-- For a prime factor `p` of an odd perfect number, every divisor of `v_p(N) + 1` has
`q`-adic valuation at most `ω(N) - 1`, for every odd prime `q`. -/
theorem padicValNat_dvd_succ_le (h : OddPerfect N) {p q n : ℕ} (hp : p ∈ N.primeFactors)
    (hq : q.Prime) (hq2 : q ≠ 2) (hn : n ∣ N.factorization p + 1) :
    padicValNat q n ≤ N.primeFactors.card - 1 :=
  (padicValNat_le_card_filter hq (by have := hq.two_le; omega) (Nat.succ_ne_zero _) hn).trans
    (card_divisors_filter_le h hp)

/-! ## The general bound -/

/-- The part of `v_q(σ(p ^ a))` not controlled by the fan bound: `v_q(p ^ d - 1)` when the
order `d` of `p` modulo `q` exceeds `1` and divides `a + 1`, and `0` otherwise. -/
noncomputable def orderWeight (q p a : ℕ) : ℕ :=
  if 1 < orderOf (p : ZMod q) ∧ orderOf (p : ZMod q) ∣ a + 1 then
    padicValNat q (p ^ orderOf (p : ZMod q) - 1)
  else 0

/-- Per component bound: `v_q(σ(p ^ e)) ≤ (ω(N) - 1) + orderWeight q p e`. -/
theorem padicValNat_sigma_le_card_sub_one_add (h : OddPerfect N) {p q : ℕ}
    (hp : p ∈ N.primeFactors) (hq : q.Prime) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    padicValNat q (σ 1 (p ^ N.factorization p)) ≤
      (N.primeFactors.card - 1) + orderWeight q p (N.factorization p) := by
  have : Fact q.Prime := ⟨hq⟩
  have hpp := Nat.prime_of_mem_primeFactors hp
  unfold orderWeight
  split_ifs with hc
  · rw [padicValNat_sigma_prime_pow_of_orderOf_dvd hpp hq hq2 hpq hc.1 hc.2]
    have := padicValNat_dvd_succ_le h hp hq hq2 (Nat.div_dvd_of_dvd hc.2)
    omega
  · by_cases ho : orderOf (p : ZMod q) = 1
    · have h1 : (p : ZMod q) = 1 := orderOf_eq_one_iff.mp ho
      have hdvd : q ∣ p - 1 := by
        rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hpp.one_lt.le, h1, Nat.cast_one, sub_self]
      rw [padicValNat_sigma_prime_pow_of_dvd_pred hpp hq hq2 hdvd]
      have := padicValNat_dvd_succ_le h hp hq hq2 (dvd_refl _)
      omega
    · have hnd : ¬ orderOf (p : ZMod q) ∣ N.factorization p + 1 := by
        intro hd
        have h0 : orderOf (p : ZMod q) ≠ 0 := by
          rintro h0
          rw [h0, zero_dvd_iff] at hd
          omega
        exact hc ⟨by omega, hd⟩
      rw [padicValNat_sigma_prime_pow_of_not_orderOf_dvd hpp hq hnd]
      omega

/-- An analogue of Thackeray's Corollary 6, proved here directly for odd perfect numbers
(Thackeray's corollary concerns an odd square with prescribed valuations and has different
hypotheses): for every prime `q`,
`v_q(N) ≤ (ω(N) - 1) ^ 2 + ∑_{p ≠ q} orderWeight q p v_p(N)`. -/
theorem factorization_le_sq_add_sum_orderWeight (h : OddPerfect N) {q : ℕ} (hq : q.Prime) :
    N.factorization q ≤ (N.primeFactors.card - 1) ^ 2 +
      ∑ p ∈ N.primeFactors.erase q, orderWeight q p (N.factorization p) := by
  by_cases hq2 : q = 2
  · subst hq2
    rw [Nat.factorization_eq_zero_of_not_dvd h.not_two_dvd]
    exact Nat.zero_le _
  by_cases hqN : q ∈ N.primeFactors
  · rw [factorization_eq_sum_erase h.perfect hq hq2]
    calc _ ≤ ∑ p ∈ N.primeFactors.erase q,
            ((N.primeFactors.card - 1) + orderWeight q p (N.factorization p)) :=
          Finset.sum_le_sum fun p hp => padicValNat_sigma_le_card_sub_one_add h
            (Finset.mem_of_mem_erase hp) hq hq2 (Finset.ne_of_mem_erase hp)
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem hqN,
            smul_eq_mul, sq]
  · rw [Nat.factorization_eq_zero_of_not_dvd
      (fun hd => hqN (Nat.mem_primeFactors.mpr ⟨hq, hd, h.ne_zero⟩))]
    exact Nat.zero_le _

/-! ## Primes `q` with `q - 1` a power of two -/

/-- Nielsen: if `q - 1` is a power of two and `q ∣ σ(p ^ a)` with `a` even, then
`p ≡ 1 (mod q)`. The order of `p` modulo `q` divides `q - 1`, so an order above `1` is even
and cannot divide the odd number `a + 1`. -/
theorem mod_eq_one_of_dvd_sigma_of_even {p q a j : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqj : q - 1 = 2 ^ j) (ha : Even a) (hdvd : q ∣ σ 1 (p ^ a)) : p % q = 1 := by
  rcases (prime_dvd_sigma_prime_pow hp hq hdvd).2 with ⟨h1, -⟩ | ⟨h1, hd, hdq⟩
  · exact h1
  · exfalso
    rw [hqj] at hdq
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdq
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [hi, pow_zero] at h1
      exact lt_irrefl _ h1
    have h2 : 2 ∣ a + 1 := (dvd_pow_self 2 hi0).trans (hi ▸ hd)
    obtain ⟨b, hb⟩ := ha
    omega

/-- If `q - 1` is a power of two, components with even exponent have zero order weight. -/
private theorem orderWeight_eq_zero_of_even {p q a j : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqj : q - 1 = 2 ^ j) (ha : Even a) : orderWeight q p a = 0 := by
  have : Fact q.Prime := ⟨hq⟩
  unfold orderWeight
  rw [if_neg]
  rintro ⟨h1, hd⟩
  have hpq : p ≠ q := by
    rintro rfl
    rw [ZMod.natCast_self, orderOf_zero] at h1
    omega
  have hm := mod_eq_one_of_dvd_sigma_of_even hp hq hqj ha
    (dvd_sigma_prime_pow_of_orderOf_dvd hp hq hpq h1 hd)
  rw [← ZMod.natCast_mod, hm, Nat.cast_one, orderOf_one] at h1
  exact lt_irrefl _ h1

/-- For the special prime `s` and `q - 1` a power of two, the order weight is at most
`v_q(s + 1)`: the exponent `k ≡ 1 (mod 4)` forces the relevant order to be `2`. -/
private theorem orderWeight_special_le (h : OddPerfect N) {s q j : ℕ} (hs : s.Prime)
    (hodd : Odd (N.factorization s)) (hq : q.Prime) (hqj : q - 1 = 2 ^ j) :
    orderWeight q s (N.factorization s) ≤ padicValNat q (s + 1) := by
  have : Fact q.Prime := ⟨hq⟩
  unfold orderWeight
  split_ifs with hc
  · obtain ⟨h1, hd⟩ := hc
    have hs0 : (s : ZMod q) ≠ 0 := by
      intro h0
      rw [h0, orderOf_zero] at h1
      omega
    have hdq := ZMod.orderOf_dvd_card_sub_one hs0
    rw [hqj] at hdq
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdq
    have hk4 := (special_mod_four h hs hodd).2
    have hi1 : i = 1 := by
      rcases Nat.lt_or_ge i 2 with hlt | hge
      · interval_cases i
        · rw [hi, pow_zero] at h1; exact absurd h1 (lt_irrefl _)
        · rfl
      · have : 4 ∣ N.factorization s + 1 :=
          (pow_dvd_pow 2 hge).trans (hi ▸ hd)
        omega
    rw [hi, hi1, pow_one]
    have hs1 : ¬ q ∣ s - 1 := by
      intro hdvd
      have : (s : ZMod q) = 1 := by
        have := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
        rw [Nat.cast_sub hs.one_lt.le, Nat.cast_one, sub_eq_zero] at this
        exact this
      rw [this, orderOf_one] at h1
      exact lt_irrefl _ h1
    have hfac : s ^ 2 - 1 = (s + 1) * (s - 1) := by
      have := hs.one_lt
      zify [Nat.one_le_pow 2 s hs.pos, this.le]
      ring
    rw [hfac, padicValNat.mul (by omega) (by have := hs.one_lt; omega),
      padicValNat.eq_zero_of_not_dvd hs1, add_zero]
  · exact Nat.zero_le _

/-- Fermat type primes: if `q` is prime with `q - 1` a power of two and `s` is the special
prime of the odd perfect number `N`, then `v_q(N) ≤ (ω(N) - 1) ^ 2 + v_q(s + 1)`. The last
term vanishes unless `s ≡ -1 (mod q)`. -/
theorem factorization_le_of_fermat (h : OddPerfect N) {q j s : ℕ} (hq : q.Prime)
    (hqj : q - 1 = 2 ^ j) (hs : s.Prime) (hodd : Odd (N.factorization s)) :
    N.factorization q ≤ (N.primeFactors.card - 1) ^ 2 + padicValNat q (s + 1) := by
  refine (factorization_le_sq_add_sum_orderWeight h hq).trans (Nat.add_le_add_left ?_ _)
  have hsN : s ∈ N.primeFactors := by
    obtain ⟨b, hb⟩ := hodd
    exact Finsupp.mem_support_iff.mpr (show N.factorization s ≠ 0 by omega)
  calc ∑ p ∈ N.primeFactors.erase q, orderWeight q p (N.factorization p)
      ≤ ∑ p ∈ N.primeFactors, orderWeight q p (N.factorization p) :=
        Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
    _ = orderWeight q s (N.factorization s) := by
        refine Finset.sum_eq_single s (fun p hp hps => ?_) (fun hn => absurd hsN hn)
        exact orderWeight_eq_zero_of_even (Nat.prime_of_mem_primeFactors hp) hq hqj
          (even_factorization_of_ne h hs hodd (Nat.prime_of_mem_primeFactors hp) hps)
    _ ≤ _ := orderWeight_special_le h hs hodd hq hqj

/-- The prime `3`: `v_3(N) ≤ (ω(N) - 1) ^ 2 + v_3(s + 1)` for the special prime `s`; the
last term is `0` unless `s ≡ 2 (mod 3)`. -/
theorem factorization_three_le (h : OddPerfect N) {s : ℕ} (hs : s.Prime)
    (hodd : Odd (N.factorization s)) :
    N.factorization 3 ≤ (N.primeFactors.card - 1) ^ 2 + padicValNat 3 (s + 1) :=
  factorization_le_of_fermat h Nat.prime_three (j := 1) rfl hs hodd

/-! ## Brent, Cohen, te Riele, Lemma 1 -/

/-- Brent, Cohen and te Riele, Lemma 1 (Nielsen's Lemma 8): if `p` and `q` are odd primes
with `p ∣ σ(q ^ k)` and `q ^ m ∣ p + 1`, then `k ≥ 3 m`. Both oddness hypotheses are needed:
`(p, q, k, m) = (2, 3, 1, 1)` and `(7, 2, 2, 3)` violate the conclusion. -/
theorem three_mul_le_of_dvd_sigma {p q k m : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hdvd : p ∣ σ 1 (q ^ k)) (hm : q ^ m ∣ p + 1) : 3 * m ≤ k := by
  have hσ := sigma_prime_pow_mul_pred hq k
  obtain ⟨t, ht⟩ := hdvd
  obtain ⟨a, ha⟩ := hm
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have ht0 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · have := sigma_pos 1 (q ^ k) (pow_ne_zero _ hq.ne_zero)
      rw [ht, h0, mul_zero] at this
      omega
    · exact h0
  have haev : Even a := by
    have h1 : Even (q ^ m * a) := by rw [← ha]; exact hpodd.add_one
    rcases Nat.even_mul.mp h1 with h2 | h2
    · exact absurd h2 (Nat.not_even_iff_odd.mpr hqodd.pow)
    · exact h2
  have ha2 : 2 ≤ a := by
    obtain ⟨b, hb⟩ := haev
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · rw [hb, h0] at ha; omega
    · omega
  have hqZ : (1 : ℤ) < q := by exact_mod_cast hq.one_lt
  have hq3Z : (3 : ℤ) ≤ q := by exact_mod_cast hq3
  have htZ : (1 : ℤ) ≤ t := by exact_mod_cast ht0
  have haZ : (2 : ℤ) ≤ a := by exact_mod_cast ha2
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = (q : ℤ) ^ m := ⟨_, rfl⟩
  have hQ1 : 1 ≤ Q := hQ ▸ one_le_pow₀ hqZ.le
  obtain ⟨C, hC⟩ : ∃ C : ℤ, C = t * ((q : ℤ) - 1) := ⟨_, rfl⟩
  have hC2 : 2 ≤ C := by
    have : 0 ≤ ((t : ℤ) - 1) * ((q : ℤ) - 1) := mul_nonneg (by linarith) (by linarith)
    rw [hC]; nlinarith
  -- Integer form: `q ^ (k + 1) = p * C + 1`.
  have hmain : (q : ℤ) ^ (k + 1) = p * C + 1 := by
    have h1 : σ 1 (q ^ k) * (q - 1) + 1 = q ^ (k + 1) := by
      rw [hσ]; have := Nat.one_le_pow (k + 1) q hq.pos; omega
    rw [ht] at h1
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h1
    push_cast [hq.one_lt.le] at h2
    rw [hC]; linear_combination -h2
  have hpZ : (p : ℤ) = a * Q - 1 := by
    have h2 := congrArg (Nat.cast : ℕ → ℤ) ha
    push_cast at h2
    rw [hQ]; linear_combination h2
  -- Step 1: `m < k + 1`.
  have hmk : m < k + 1 := by
    rw [← pow_lt_pow_iff_right₀ hqZ, hmain, ← hQ]
    have : 0 ≤ (p : ℤ) * (C - 2) := mul_nonneg (by positivity) (by linarith)
    have : 0 ≤ ((a : ℤ) - 2) * Q := mul_nonneg (by linarith) (by linarith)
    linarith
  obtain ⟨r, hr⟩ : ∃ r, k + 1 = m + r := ⟨k + 1 - m, by omega⟩
  rw [hr, pow_add, ← hQ] at hmain
  -- Step 2: `C = d * Q + 1` with `d ≥ 1`.
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d = a * C - (q : ℤ) ^ r := ⟨_, rfl⟩
  have hCd : C = d * Q + 1 := by linear_combination hmain + C * hpZ - Q * hd
  have hd1 : 1 ≤ d := by
    by_contra hlt
    have : d * Q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) (by linarith)
    linarith
  -- Step 3: `q ^ r = a d Q + a - d`.
  have hX : (q : ℤ) ^ r = a * d * Q + a - d := by
    have h0 : Q * (q : ℤ) ^ r = Q * (a * d * Q + a - d) := by
      rw [hmain, hpZ, hCd]; ring
    exact mul_left_cancel₀ (by positivity) h0
  -- Step 4: `m < r`.
  have hmr : m < r := by
    rw [← pow_lt_pow_iff_right₀ hqZ, ← hQ, hX]
    have : 0 ≤ (d - 1) * ((a : ℤ) * Q - 1) := mul_nonneg (by linarith) (by nlinarith)
    have : 0 ≤ ((a : ℤ) - 2) * Q := mul_nonneg (by linarith) (by linarith)
    linarith
  obtain ⟨r', hr'⟩ : ∃ r', r = m + r' := ⟨r - m, by omega⟩
  rw [hr', pow_add, ← hQ] at hX
  -- Step 5: `a - d = Q * c` with `c ≠ 0`, hence `Q < q ^ r'`.
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = (q : ℤ) ^ r' - a * d := ⟨_, rfl⟩
  have hac : a - d = Q * c := by rw [hc]; linarith
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0, mul_zero, sub_eq_zero] at hac
    obtain ⟨b, hb⟩ := haev
    obtain ⟨w, hw⟩ : Odd ((q : ℤ) ^ r) := by exact_mod_cast hqodd.pow
    have hbZ : (a : ℤ) = b + b := by exact_mod_cast hb
    have h3 : 2 * w + 1 = 2 * (b * (b + b) * Q) := by
      rw [← hw, hr', pow_add, ← hQ, hX, ← hac, hbZ]; ring
    generalize (b : ℤ) * (b + b) * Q = z at h3
    omega
  have hQr : Q < (q : ℤ) ^ r' := by
    rcases lt_or_gt_of_ne hc0 with hneg | hpos
    · have e1 : Q * (c + 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by omega)
      have e2 : 0 ≤ d * ((a : ℤ) - 2) := mul_nonneg (by linarith) (by linarith)
      have e3 : (Q - 1) * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by omega)
      linarith
    · have e1 : 0 ≤ Q * (c - 1) := mul_nonneg (by linarith) (by omega)
      have e2 : 0 ≤ (a : ℤ) * (d - 1) := mul_nonneg (by linarith) (by linarith)
      linarith
  rw [hQ, pow_lt_pow_iff_right₀ hqZ] at hQr
  omega

end OddPerfect

#print axioms OddPerfect.sum_padicValNat_sigma_le_factorization
#print axioms OddPerfect.sum_padicValNat_two_sigma_le_one
#print axioms OddPerfect.padicValNat_dvd_succ_le
#print axioms OddPerfect.padicValNat_sigma_le_card_sub_one_add
#print axioms OddPerfect.factorization_le_sq_add_sum_orderWeight
#print axioms OddPerfect.mod_eq_one_of_dvd_sigma_of_even
#print axioms OddPerfect.factorization_le_of_fermat
#print axioms OddPerfect.factorization_three_le
#print axioms OddPerfect.three_mul_le_of_dvd_sigma
