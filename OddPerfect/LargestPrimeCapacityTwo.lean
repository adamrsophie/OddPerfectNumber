import OddPerfect.LargestPrimeCapacity

/-!
# Two primes that are not the largest prime factor of an odd perfect number

Let `N` be an odd perfect number and `P` a prime factor with `r ≤ P` for every prime factor
`r`, and write `P - 1 = 2 ^ a · m` with `m` odd. A *sender* is a prime factor `p ≠ P` with
`P ∣ σ(p ^ e_p)`. By `sender_largest_data`, a sender `p` is odd, `p < P`, and its order `t`
modulo `P` satisfies `3 ≤ t` and `4 ∤ t`; since `t ∣ 2 ^ a · m`, this gives `t ∣ 2 m`, so
`p ^ (2 m) ≡ 1 (mod P)`. The ledger `e_P = Σ_{p ≠ P} v_P(σ(p ^ e_p))` has a nonzero term
only at senders.

* `P = 40961 = 2 ^ 13 · 5 + 1`: the odd `x < P` with `x ^ 10 ≡ 1` are
  `1, 15883, 21083, 31851, 35847`, and none of them is prime. So there is no sender and
  `e_P = 0`, a contradiction.
* `P = 18433 = 2 ^ 11 · 9 + 1`: the odd `x < P` with `x ^ 18 ≡ 1` are
  `1, 2225, 3785, 4481, 10581, 12609, 14649, 16177, 16405`, and only `4481` is prime. Its
  order is even (as `4481 ^ 9 ≢ 1`), so if it is a sender its exponent is odd; its weight is
  `v_P(4481 ^ t - 1) ≤ v_P(4481 ^ 18 - 1) = 1`. Hence `e_P = 1` is odd, so `P` is the special
  prime, and a sender `4481` would be a second prime with odd exponent. So there is no sender,
  and again `e_P = 0`.

The coverage of the root lists is a kernel computation (`allRange`, a divide and conquer check
of depth `16`, respectively `15`, over all `x < P`).

These results exclude two isolated values of the largest prime factor; they do not say that
the largest prime factor exceeds `40961`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## A kernel checkable range test -/

/-- `allRange f d lo n` checks `f x` for `lo ≤ x < lo + n` by halving `d` times. -/
private def allRange (f : ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0, lo, n => n == 0 || (n == 1 && f lo)
  | d + 1, lo, n => allRange f d lo (n / 2) && allRange f d (lo + n / 2) (n - n / 2)

private theorem allRange_spec (f : ℕ → Bool) (d : ℕ) : ∀ lo n, allRange f d lo n = true →
    n ≤ 2 ^ d → ∀ x, lo ≤ x → x < lo + n → f x = true := by
  induction d with
  | zero =>
    intro lo n h hn x hx1 hx2
    simp only [allRange, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · omega
    · obtain rfl : x = lo := by omega
      exact h2
  | succ d ih =>
    intro lo n h hn x hx1 hx2
    simp only [allRange, Bool.and_eq_true] at h
    rw [pow_succ] at hn
    by_cases hx : x < lo + n / 2
    · exact ih lo (n / 2) h.1 (by omega) x hx1 hx
    · exact ih (lo + n / 2) (n - n / 2) h.2 (by omega) x (by omega) (by omega)

private theorem chk_40961 : allRange (fun x => x % 2 == 0 || x ^ 10 % 40961 != 1 ||
    [1, 15883, 21083, 31851, 35847].contains x) 16 0 40961 = true := by
  decide +kernel

private theorem chk_18433 : allRange (fun x => x % 2 == 0 || x ^ 18 % 18433 != 1 ||
    [1, 2225, 3785, 4481, 10581, 12609, 14649, 16177, 16405].contains x) 15 0 18433 = true := by
  decide +kernel

/-- Coverage modulo `40961`: every odd `x < 40961` with `x ^ 10 ≡ 1` is in the list. -/
private theorem cov_40961 (x : ℕ) (hx : x < 40961) (h2 : x % 2 = 1) (h : x ^ 10 % 40961 = 1) :
    x ∈ [1, 15883, 21083, 31851, 35847] := by
  have := allRange_spec _ 16 0 40961 chk_40961 (by norm_num) x (Nat.zero_le _) (by omega)
  simpa [h2, h] using this

/-- Coverage modulo `18433`: every odd `x < 18433` with `x ^ 18 ≡ 1` is in the list. -/
private theorem cov_18433 (x : ℕ) (hx : x < 18433) (h2 : x % 2 = 1) (h : x ^ 18 % 18433 = 1) :
    x ∈ [1, 2225, 3785, 4481, 10581, 12609, 14649, 16177, 16405] := by
  have := allRange_spec _ 15 0 18433 chk_18433 (by norm_num) x (Nat.zero_le _) (by omega)
  simpa [h2, h] using this

/-! ## Senders -/

/-- If `t ∣ 2 ^ a · m` and `4 ∤ t`, then `t ∣ 2 m`. -/
private theorem dvd_two_mul_of_dvd {t a m : ℕ} (h : t ∣ 2 ^ a * m) (h4 : ¬ 4 ∣ t) :
    t ∣ 2 * m := by
  rcases Nat.even_or_odd t with ⟨s, hs⟩ | ho
  · have hso : Odd s := by
      rcases Nat.even_or_odd s with ⟨u, hu⟩ | hu
      · exact absurd ⟨u, by omega⟩ h4
      · exact hu
    have hst : s ∣ 2 ^ a * m := Nat.dvd_trans ⟨2, by omega⟩ h
    have hsm : s ∣ m :=
      (Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hso)).dvd_of_dvd_mul_left hst
    rw [hs, ← two_mul]
    exact Nat.mul_dvd_mul_left 2 hsm
  · exact ((Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr ho)).dvd_of_dvd_mul_left h).mul_left 2

private theorem natPow_mod_of_zmod {P p k : ℕ} (hP : 1 < P) (h : (p : ZMod P) ^ k = 1) :
    p ^ k % P = 1 := by
  have : ((p ^ k : ℕ) : ZMod P) = ((1 : ℕ) : ZMod P) := by push_cast; exact h
  rw [ZMod.natCast_eq_natCast_iff'] at this
  rw [this, Nat.mod_eq_of_lt hP]

variable {N : ℕ}

/-- Data of a sender `p` into the largest prime factor `P` with `P - 1 = 2 ^ a · m`: `p < P`,
`p` odd, the order `t` of `p` modulo `P` divides `2 m` and `e_p + 1`, and the weight of `p`
is `v_P(p ^ t - 1)`. -/
private theorem sender_data (h : OddPerfect N) {P p a m : ℕ} (hP : P ∈ N.primeFactors)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hm : P - 1 = 2 ^ a * m)
    (hp : p ∈ N.primeFactors) (hpP : p ≠ P) (hd : P ∣ σ 1 (p ^ N.factorization p)) :
    p < P ∧ p % 2 = 1 ∧ orderOf (p : ZMod P) ∣ 2 * m ∧
      orderOf (p : ZMod P) ∣ N.factorization p + 1 ∧
      padicValNat P (σ 1 (p ^ N.factorization p)) =
        padicValNat P (p ^ orderOf (p : ZMod P) - 1) := by
  obtain ⟨hlt, hp2, ht, h4, hw⟩ := sender_largest_data h hP hmax hp hpP hd
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hpp := Nat.prime_of_mem_primeFactors hp
  have : Fact P.Prime := ⟨hPp⟩
  have hp0 : (p : ZMod P) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hh
    have := Nat.le_of_dvd hpp.pos hh
    omega
  have htP := ZMod.orderOf_dvd_card_sub_one hp0
  rw [hm] at htP
  have hdd := (dvd_sigma_prime_pow_iff hpp hPp hpP).mp hd
  rw [if_neg (by omega)] at hdd
  exact ⟨hlt, hp2, dvd_two_mul_of_dvd htP h4, hdd, hw⟩

/-! ## The two primes -/

/-- `40961` is not the largest prime factor of an odd perfect number: if it divides `N` and
every prime factor of `N` is at most `40961`, there is no sender into `40961`, so its exponent
is `0`. This excludes one value only; it does not say the largest prime factor exceeds
`40961`. -/
theorem false_of_largest_40961 {N : ℕ} (h : OddPerfect N) (hP : 40961 ∈ N.primeFactors)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ 40961) : False := by
  have hpos : N.factorization 40961 ≠ 0 := Finsupp.mem_support_iff.mp hP
  apply hpos
  rw [factorization_eq_sum_erase h.perfect (Nat.prime_of_mem_primeFactors hP) (by norm_num)]
  refine Finset.sum_eq_zero fun p hp => ?_
  obtain ⟨hpP, hpN⟩ := Finset.mem_erase.mp hp
  refine padicValNat.eq_zero_of_not_dvd fun hd => ?_
  obtain ⟨hlt, hp2, ht, -, -⟩ :=
    sender_data h hP hmax (a := 13) (m := 5) (by norm_num) hpN hpP hd
  have : Fact (40961).Prime := ⟨Nat.prime_of_mem_primeFactors hP⟩
  have hpow := natPow_mod_of_zmod (by norm_num) (orderOf_dvd_iff_pow_eq_one.mp ht)
  have hpp := Nat.prime_of_mem_primeFactors hpN
  have hmem := cov_40961 p hlt hp2 hpow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> norm_num at hpp

/-- `18433` is not the largest prime factor of an odd perfect number. The only candidate
sender is `4481`; it would carry weight at most `1` and have odd exponent, while the exponent
of `18433` would then be `1`, giving two primes of odd exponent. This excludes one value only;
it does not say the largest prime factor exceeds `18433`. -/
theorem false_of_largest_18433 {N : ℕ} (h : OddPerfect N) (hP : 18433 ∈ N.primeFactors)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ 18433) : False := by
  have hPp : (18433).Prime := Nat.prime_of_mem_primeFactors hP
  have : Fact (18433).Prime := ⟨hPp⟩
  have hsum := factorization_eq_sum_erase h.perfect hPp (by norm_num)
  have hpos : N.factorization 18433 ≠ 0 := Finsupp.mem_support_iff.mp hP
  -- every sender is `4481`, with odd exponent and weight at most `1`
  have key : ∀ p ∈ N.primeFactors.erase 18433, 18433 ∣ σ 1 (p ^ N.factorization p) →
      p = 4481 ∧ Odd (N.factorization p) ∧
        padicValNat 18433 (σ 1 (p ^ N.factorization p)) ≤ 1 := by
    intro p hp hd
    obtain ⟨hpP, hpN⟩ := Finset.mem_erase.mp hp
    obtain ⟨hlt, hp2, ht, hte, hw⟩ :=
      sender_data h hP hmax (a := 11) (m := 9) (by norm_num) hpN hpP hd
    have hpow := natPow_mod_of_zmod (by norm_num) (orderOf_dvd_iff_pow_eq_one.mp ht)
    have hpp := Nat.prime_of_mem_primeFactors hpN
    have hmem := cov_18433 p hlt hp2 hpow
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at hpp
    refine ⟨rfl, ?_, ?_⟩
    · -- the order is even, since `4481 ^ 9 ≢ 1`
      have hev : Even (orderOf ((4481 : ℕ) : ZMod 18433)) := by
        rcases Nat.even_or_odd (orderOf ((4481 : ℕ) : ZMod 18433)) with he | ho
        · exact he
        · have h9 : orderOf ((4481 : ℕ) : ZMod 18433) ∣ 9 :=
            (Nat.coprime_two_right.mpr ho).dvd_of_dvd_mul_left ht
          have := natPow_mod_of_zmod (by norm_num) (orderOf_dvd_iff_pow_eq_one.mp h9)
          norm_num at this
      obtain ⟨c, hc⟩ := hte
      have : Even (N.factorization 4481 + 1) := hc ▸ hev.mul_right c
      exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp this)
    · rw [hw]
      set t := orderOf ((4481 : ℕ) : ZMod 18433)
      have ht0 : 0 < t := Nat.pos_of_dvd_of_pos ht (by norm_num)
      have hne : 4481 ^ t - 1 ≠ 0 := by
        have := Nat.one_lt_pow ht0.ne' (show 1 < 4481 by norm_num)
        omega
      by_contra hw2
      push Not at hw2
      have h1 : 18433 ^ 2 ∣ 4481 ^ t - 1 := (padicValNat_dvd_iff_le hne).mpr hw2
      obtain ⟨c, hc⟩ := ht
      have h2 : 4481 ^ t - 1 ∣ 4481 ^ 18 - 1 := by
        simpa only [one_pow, ← pow_mul, ← hc] using Nat.sub_dvd_pow_sub_pow (4481 ^ t) 1 c
      have h3 : ¬ 18433 ^ 2 ∣ 4481 ^ 18 - 1 := by norm_num
      exact h3 (h1.trans h2)
  by_cases hs : ∃ p ∈ N.primeFactors.erase 18433, 18433 ∣ σ 1 (p ^ N.factorization p)
  · obtain ⟨p, hp, hd⟩ := hs
    obtain ⟨rfl, hodd, -⟩ := key p hp hd
    -- the exponent of `18433` is at most `1`
    have hle : N.factorization 18433 ≤ 1 := by
      rw [hsum]
      calc ∑ q ∈ N.primeFactors.erase 18433, padicValNat 18433 (σ 1 (q ^ N.factorization q))
          ≤ ∑ q ∈ N.primeFactors.erase 18433, (if q = 4481 then 1 else 0) := by
            refine Finset.sum_le_sum fun q hq => ?_
            by_cases hqd : 18433 ∣ σ 1 (q ^ N.factorization q)
            · obtain ⟨rfl, -, hw⟩ := key q hq hqd
              simpa using hw
            · rw [padicValNat.eq_zero_of_not_dvd hqd]
              exact Nat.zero_le _
        _ ≤ 1 := by
            rw [Finset.sum_ite_eq']
            split_ifs
            all_goals norm_num
    have hPodd : Odd (N.factorization 18433) := by
      rw [show N.factorization 18433 = 1 by omega]
      exact odd_one
    have := (existsUnique_odd_exponent h).unique
      ⟨Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp hp).2, hodd⟩ ⟨hPp, hPodd⟩
    norm_num at this
  · apply hpos
    rw [hsum]
    refine Finset.sum_eq_zero fun q hq => padicValNat.eq_zero_of_not_dvd fun hd => hs ⟨q, hq, hd⟩

/-- `40961` is not the largest prime factor of an odd perfect number `N`: if `40961 ∣ N`,
some prime factor of `N` exceeds `40961`. This excludes one isolated value; it does not say
that the largest prime factor of `N` exceeds `40961`. -/
theorem largest_primeFactor_ne_40961 {N : ℕ} (h : OddPerfect N)
    (hP : 40961 ∈ N.primeFactors) : ∃ r ∈ N.primeFactors, 40961 < r := by
  by_contra hc
  push Not at hc
  exact false_of_largest_40961 h hP hc

/-- `18433` is not the largest prime factor of an odd perfect number `N`: if `18433 ∣ N`,
some prime factor of `N` exceeds `18433`. This excludes one isolated value; it does not say
that the largest prime factor of `N` exceeds `18433`. -/
theorem largest_primeFactor_ne_18433 {N : ℕ} (h : OddPerfect N)
    (hP : 18433 ∈ N.primeFactors) : ∃ r ∈ N.primeFactors, 18433 < r := by
  by_contra hc
  push Not at hc
  exact false_of_largest_18433 h hP hc

end OddPerfect

#print axioms OddPerfect.false_of_largest_40961
#print axioms OddPerfect.false_of_largest_18433
#print axioms OddPerfect.largest_primeFactor_ne_40961
#print axioms OddPerfect.largest_primeFactor_ne_18433
