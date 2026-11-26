import OddPerfect.Zsigmondy
import OddPerfect.Euler
import OddPerfect.SpecialPrime
import OddPerfect.UpperBound

/-!
# Exponent caps from primitive prime divisors

Let `N` be an odd perfect number and `e = N.factorization p` the exact exponent of a prime
factor `p`. Every divisor `d ≥ 3` of `e + 1` yields a prime factor `q` of `N` in which `p` has
order exactly `d` (`exists_primeFactor_modEq_one`). Consequences:

* Row length: if every prime factor is at most `R`, then `2 e + 3 ≤ R` for every prime
  factor `p`; in particular `e + 2 ≤ R`.
* Fan bound: the divisors `d ≥ 3` of `e + 1` give distinct prime factors other than `p`.
* Size: `N ≤ R ^ ((R - 2) * ω(N))` and `ω(N) ≤ R - 2`.
* Finiteness: odd perfect numbers with a fixed number of prime factors, or with all prime
  factors below a fixed bound, form a finite set.
* Small primes absent from `N`: an odd prime `l ∤ N` divides no component divisor sum,
  which restricts the exponents. For `l = 3`: the special prime is `≡ 1 (mod 12)`.
-/

namespace OddPerfect

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

variable {N : ℕ}

private lemma primeFactor_mod_two (h : OddPerfect N) {q : ℕ} (hq : q ∈ N.primeFactors) :
    q % 2 = 1 :=
  Nat.odd_iff.mp (h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq))

private lemma one_le_factorization {p : ℕ} (hp : p ∈ N.primeFactors) :
    1 ≤ N.factorization p :=
  Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)

/-- The primitive witness in the form used below. -/
private lemma witness (h : OddPerfect N) {p d : ℕ} (hp : p ∈ N.primeFactors) (hd3 : 3 ≤ d)
    (hd : d ∣ N.factorization p + 1) :
    ∃ q ∈ N.primeFactors, orderOf (p : ZMod q) = d ∧ d ∣ q - 1 ∧ q ≠ p := by
  obtain ⟨q, hq, ho, hmod⟩ := exists_primeFactor_modEq_one h hp hd3 hd
  have hqp := Nat.prime_of_mem_primeFactors hq
  refine ⟨q, hq, ho, ?_, ?_⟩
  · refine (Nat.modEq_iff_dvd' hqp.one_lt.le).mp ?_
    change 1 % d = q % d
    rw [hmod, Nat.mod_eq_of_lt (by omega)]
  · rintro rfl
    have : Fact q.Prime := ⟨hqp⟩
    rw [ZMod.natCast_self, orderOf_zero] at ho
    omega

private lemma two_mul_dvd_of_odd {m q : ℕ} (hm : m % 2 = 1) (hq : q % 2 = 1) (h : m ∣ q - 1) :
    2 * m ∣ q - 1 :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hm))
    (Nat.dvd_of_mod_eq_zero (by omega)) h

private lemma two_mul_succ_le_max {n r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (hrs : r ≠ s)
    (hnr : n ∣ r - 1) (hns : n ∣ s - 1) : 2 * n + 1 ≤ max r s := by
  rcases lt_or_gt_of_ne hrs with hlt | hlt
  · have h1 := Nat.le_of_dvd (by omega) hnr
    have h2 := Nat.le_of_dvd (by omega) (Nat.dvd_sub hns hnr)
    omega
  · have h1 := Nat.le_of_dvd (by omega) hns
    have h2 := Nat.le_of_dvd (by omega) (Nat.dvd_sub hnr hns)
    omega

/-! ## Row length -/

/-- For every prime factor `p` of an odd perfect number with exponent `e`, some prime factor
is at least `2 e + 3`. For an ordinary prime this is a primitive prime of order `e + 1`, which
is `≡ 1 (mod 2 (e + 1))`. For the special prime with exponent `k ≥ 5` the primitive primes of
orders `k + 1` and `(k + 1) / 2` are distinct and both `≡ 1 (mod k + 1)`. For `k = 1` the
special prime itself is `≡ 1 (mod 4)`, hence at least `5`. -/
theorem exists_primeFactor_two_mul_factorization_add_three_le (h : OddPerfect N) {p : ℕ}
    (hp : p ∈ N.primeFactors) : ∃ r ∈ N.primeFactors, 2 * N.factorization p + 3 ≤ r := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have he1 := one_le_factorization hp
  set e := N.factorization p with he
  rcases Nat.even_or_odd e with ⟨j, hj⟩ | hodd
  · obtain ⟨q, hq, -, hdq, -⟩ := witness h hp (d := e + 1) (by omega) dvd_rfl
    have h2 := two_mul_dvd_of_odd (by omega) (primeFactor_mod_two h hq) hdq
    have := Nat.le_of_dvd (by have := (Nat.prime_of_mem_primeFactors hq).two_le; omega) h2
    exact ⟨q, hq, by omega⟩
  · have h4 := special_mod_four h hpp hodd
    rw [← he] at h4
    by_cases hk : e = 1
    · have := hpp.two_le
      exact ⟨p, hp, by omega⟩
    · obtain ⟨q, hq, hoq, hdq, -⟩ := witness h hp (d := e + 1) (by omega) dvd_rfl
      obtain ⟨r, hr, hor, hdr, -⟩ :=
        witness h hp (d := (e + 1) / 2) (by omega) (Nat.div_dvd_of_dvd (by omega))
      have h2 := two_mul_dvd_of_odd (m := (e + 1) / 2) (by omega) (primeFactor_mod_two h hr) hdr
      rw [show 2 * ((e + 1) / 2) = e + 1 by omega] at h2
      have hqr : q ≠ r := by
        rintro rfl
        rw [hoq] at hor
        omega
      have := two_mul_succ_le_max (Nat.prime_of_mem_primeFactors hq).two_le
        (Nat.prime_of_mem_primeFactors hr).two_le hqr hdq h2
      rcases max_choice q r with hm | hm <;> rw [hm] at this
      · exact ⟨q, hq, by omega⟩
      · exact ⟨r, hr, by omega⟩

/-- Row length, sharp form: if every prime factor of an odd perfect number is at most `R`,
then every exponent `e` satisfies `2 e + 3 ≤ R`. -/
theorem two_mul_factorization_add_three_le (h : OddPerfect N) {p R : ℕ}
    (hp : p ∈ N.primeFactors) (hR : ∀ r ∈ N.primeFactors, r ≤ R) :
    2 * N.factorization p + 3 ≤ R := by
  obtain ⟨r, hr, hle⟩ := exists_primeFactor_two_mul_factorization_add_three_le h hp
  exact hle.trans (hR r hr)

/-- Row length: if every prime factor of an odd perfect number is at most `R`, then every
exponent `e` satisfies `e + 2 ≤ R`. -/
theorem factorization_add_two_le (h : OddPerfect N) {p R : ℕ}
    (hp : p ∈ N.primeFactors) (hR : ∀ r ∈ N.primeFactors, r ≤ R) :
    N.factorization p + 2 ≤ R := by
  have := two_mul_factorization_add_three_le h hp hR
  omega

/-! ## Fan bound -/

/-- Distinct divisors `d ≥ 3` of `e + 1` give distinct prime factors other than `p`, since
`p` has order exactly `d` modulo the prime attached to `d`. -/
theorem card_divisors_filter_le (h : OddPerfect N) {p : ℕ} (hp : p ∈ N.primeFactors) :
    ((Nat.divisors (N.factorization p + 1)).filter (3 ≤ ·)).card ≤ N.primeFactors.card - 1 := by
  rw [← Finset.card_erase_of_mem hp]
  calc _ ≤ ((N.primeFactors.erase p).image fun q => orderOf (p : ZMod q)).card := by
        apply Finset.card_le_card
        intro d hd
        rw [Finset.mem_filter, Nat.mem_divisors] at hd
        obtain ⟨q, hq, ho, -, hqp⟩ := witness h hp hd.2 hd.1.1
        exact Finset.mem_image.mpr ⟨q, Finset.mem_erase.mpr ⟨hqp, hq⟩, ho⟩
    _ ≤ _ := Finset.card_image_le

/-- Fan bound for an ordinary prime: if the exponent `e` is even, then `e + 1` has at most
`ω(N)` divisors. -/
theorem card_divisors_le_of_even (h : OddPerfect N) {p : ℕ} (hp : p ∈ N.primeFactors)
    (hev : Even (N.factorization p)) :
    (Nat.divisors (N.factorization p + 1)).card ≤ N.primeFactors.card := by
  obtain ⟨j, hj⟩ := hev
  have h1 := card_divisors_filter_le h hp
  have h2 := Finset.card_filter_add_card_filter_not
    (s := Nat.divisors (N.factorization p + 1)) (3 ≤ ·)
  have hone : ∀ a ∈ (Nat.divisors (N.factorization p + 1)).filter (fun d => ¬ 3 ≤ d), a = 1 := by
    intro a ha
    rw [Finset.mem_filter, Nat.mem_divisors] at ha
    obtain ⟨⟨hdvd, -⟩, h3⟩ := ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_dvd_iff] at hdvd
      omega
    have ha2 : a ≠ 2 := by
      rintro rfl
      omega
    omega
  have h3 : ((Nat.divisors (N.factorization p + 1)).filter fun d => ¬ 3 ≤ d).card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb => (hone a ha).trans (hone b hb).symm
  have h4 := Finset.card_pos.mpr ⟨p, hp⟩
  omega

/-! ## Size from the largest prime -/

/-- If every prime factor of an odd perfect number is at most `R`, then `ω(N) ≤ R - 2`,
since the prime factors are distinct odd primes in `[3, R]`. -/
theorem card_primeFactors_le (h : OddPerfect N) {R : ℕ} (hR : ∀ r ∈ N.primeFactors, r ≤ R) :
    N.primeFactors.card ≤ R - 2 := by
  have hsub : N.primeFactors ⊆ Finset.Icc 3 R := by
    intro q hq
    have := (Nat.prime_of_mem_primeFactors hq).two_le
    have := primeFactor_mod_two h hq
    have := hR q hq
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc] at this
  omega

/-- If every prime factor of an odd perfect number is at most `R`, then
`N ≤ R ^ ((R - 2) * ω(N))`: each component `p ^ e` is at most `R ^ (R - 2)`. -/
theorem le_pow_of_primeFactors_le (h : OddPerfect N) {R : ℕ}
    (hR : ∀ r ∈ N.primeFactors, r ≤ R) : N ≤ R ^ ((R - 2) * N.primeFactors.card) := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self h.ne_zero]
  rw [Nat.prod_factorization_eq_prod_primeFactors, pow_mul]
  apply Finset.prod_le_pow_card
  intro p hp
  have hpR := hR p hp
  have := (Nat.prime_of_mem_primeFactors hp).two_le
  have := factorization_add_two_le h hp hR
  calc p ^ N.factorization p ≤ R ^ N.factorization p := Nat.pow_le_pow_left hpR _
    _ ≤ R ^ (R - 2) := Nat.pow_le_pow_right (by omega) (by omega)

/-! ## Finiteness -/

/-- For each `k`, there are finitely many odd perfect numbers with exactly `k` distinct prime
factors (Nielsen's bound `N < 2 ^ 4 ^ k`). -/
theorem finite_setOf_card_primeFactors_eq (k : ℕ) :
    {N | OddPerfect N ∧ N.primeFactors.card = k}.Finite :=
  (Finset.range (2 ^ 4 ^ k)).finite_toSet.subset fun _ ⟨h, hk⟩ =>
    Finset.mem_coe.mpr (Finset.mem_range.mpr (hk ▸ lt_two_pow_four_pow h))

/-- For each `R`, there are finitely many odd perfect numbers all of whose prime factors are
at most `R`. -/
theorem finite_setOf_primeFactors_le (R : ℕ) :
    {N | OddPerfect N ∧ ∀ r ∈ N.primeFactors, r ≤ R}.Finite :=
  (Set.finite_Iic (R ^ ((R - 2) * (R - 2)))).subset fun N ⟨h, hR⟩ => by
    obtain ⟨q, hq, hqN, -⟩ := exists_special_prime h
    have hqR := hR q (Nat.mem_primeFactors.mpr ⟨hq, hqN, h.ne_zero⟩)
    have := hq.two_le
    exact (le_pow_of_primeFactors_le h hR).trans (Nat.pow_le_pow_right (by omega)
      (Nat.mul_le_mul_left _ (card_primeFactors_le h hR)))

/-! ## Odd primes not dividing `N` -/

/-- An odd prime `l` that does not divide `N` divides no component divisor sum
`σ 1 (p ^ e)`. -/
theorem not_dvd_sigma_of_not_mem (h : OddPerfect N) {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2)
    (hlN : l ∉ N.primeFactors) {p : ℕ} (hp : p ∈ N.primeFactors) :
    ¬ l ∣ σ 1 (p ^ N.factorization p) := fun hd =>
  hlN (Nat.mem_primeFactors.mpr ⟨hl, OPNStarter.force_prime h.perfect
    (Nat.prime_of_mem_primeFactors hp) rfl hl hl2 hd, h.ne_zero⟩)

/-- If an odd prime `l ∤ N` and a prime factor `p ≡ 1 (mod l)`, then `l ∤ e + 1`. -/
theorem not_dvd_succ_of_mod_eq_one (h : OddPerfect N) {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2)
    (hlN : l ∉ N.primeFactors) {p : ℕ} (hp : p ∈ N.primeFactors) (hpl : p % l = 1) :
    ¬ l ∣ N.factorization p + 1 := by
  intro hd
  have : Fact l.Prime := ⟨hl⟩
  have hpp := Nat.prime_of_mem_primeFactors hp
  apply not_dvd_sigma_of_not_mem h hl hl2 hlN hp
  have hlp : l ∣ p - 1 := by
    refine (Nat.modEq_iff_dvd' hpp.one_lt.le).mp ?_
    change 1 % l = p % l
    rw [hpl, Nat.mod_eq_of_lt hl.one_lt]
  have hv := padicValNat_sigma_prime_pow_of_dvd_pred (a := N.factorization p) hpp hl hl2 hlp
  have hpos := one_le_padicValNat_of_dvd (Nat.succ_ne_zero _) hd
  rw [← Nat.padicValNat_def, ← hv] at hpos
  exact dvd_of_one_le_padicValNat (by rw [← Nat.padicValNat_def]; exact hpos)

/-- If an odd prime `l ∤ N` and a prime factor `p` has order `d > 1` modulo `l`, then
`d ∤ e + 1`. -/
theorem not_orderOf_dvd_succ (h : OddPerfect N) {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2)
    (hlN : l ∉ N.primeFactors) {p : ℕ} (hp : p ∈ N.primeFactors)
    (h1 : 1 < orderOf (p : ZMod l)) : ¬ orderOf (p : ZMod l) ∣ N.factorization p + 1 :=
  fun hd => not_dvd_sigma_of_not_mem h hl hl2 hlN hp
    (dvd_sigma_prime_pow_of_orderOf_dvd (Nat.prime_of_mem_primeFactors hp) hl
      (by rintro rfl; exact hlN hp) h1 hd)

/-- If `3 ∤ N`, every prime factor `p ≡ 1 (mod 3)` has exponent `e` with `e % 3 ≠ 2`. -/
theorem factorization_mod_three_ne_two (h : OddPerfect N) (h3 : ¬ 3 ∣ N) {p : ℕ}
    (hp : p ∈ N.primeFactors) (hp1 : p % 3 = 1) : N.factorization p % 3 ≠ 2 := by
  have := not_dvd_succ_of_mod_eq_one h Nat.prime_three (by decide)
    (fun hm => h3 (Nat.dvd_of_mem_primeFactors hm)) hp hp1
  omega

/-- If `3 ∤ N`, every prime factor `p ≡ 2 (mod 3)` has even exponent. -/
theorem even_factorization_of_mod_three_eq_two (h : OddPerfect N) (h3 : ¬ 3 ∣ N) {p : ℕ}
    (hp : p ∈ N.primeFactors) (hp2 : p % 3 = 2) : Even (N.factorization p) := by
  have ho : orderOf (p : ZMod 3) = 2 := by
    rw [← ZMod.natCast_mod, hp2]
    exact orderOf_eq_prime (by decide) (by decide)
  have := not_orderOf_dvd_succ h Nat.prime_three (by decide)
    (fun hm => h3 (Nat.dvd_of_mem_primeFactors hm)) hp (by omega)
  rw [ho] at this
  exact Nat.even_iff.mpr (by omega)

/-- If `3 ∤ N`, the special prime (the prime of odd exponent) is `≡ 1 (mod 12)`. -/
theorem special_mod_twelve (h : OddPerfect N) (h3 : ¬ 3 ∣ N) {s : ℕ} (hs : s.Prime)
    (hodd : Odd (N.factorization s)) : s % 12 = 1 := by
  have hmem : s ∈ N.primeFactors := by
    obtain ⟨j, hj⟩ := hodd
    exact Finsupp.mem_support_iff.mpr (show N.factorization s ≠ 0 by omega)
  have h4 := (special_mod_four h hs hodd).1
  have hs3 : s % 3 ≠ 0 := by
    intro h0
    obtain rfl : 3 = s := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hs).mp
      (Nat.dvd_of_mod_eq_zero h0)
    exact h3 (Nat.dvd_of_mem_primeFactors hmem)
  have hs2 : s % 3 ≠ 2 := fun h2 =>
    Nat.not_even_iff_odd.mpr hodd (even_factorization_of_mod_three_eq_two h h3 hmem h2)
  omega

end OddPerfect

#print axioms OddPerfect.exists_primeFactor_two_mul_factorization_add_three_le
#print axioms OddPerfect.two_mul_factorization_add_three_le
#print axioms OddPerfect.factorization_add_two_le
#print axioms OddPerfect.card_divisors_filter_le
#print axioms OddPerfect.card_divisors_le_of_even
#print axioms OddPerfect.card_primeFactors_le
#print axioms OddPerfect.le_pow_of_primeFactors_le
#print axioms OddPerfect.finite_setOf_card_primeFactors_eq
#print axioms OddPerfect.finite_setOf_primeFactors_le
#print axioms OddPerfect.not_dvd_sigma_of_not_mem
#print axioms OddPerfect.not_dvd_succ_of_mod_eq_one
#print axioms OddPerfect.not_orderOf_dvd_succ
#print axioms OddPerfect.factorization_mod_three_ne_two
#print axioms OddPerfect.even_factorization_of_mod_three_eq_two
#print axioms OddPerfect.special_mod_twelve
