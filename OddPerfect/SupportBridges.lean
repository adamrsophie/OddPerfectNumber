import OddPerfect.Zsigmondy
import OddPerfect.ClosedLoop
import OddPerfect.ValuationBounds
import OddPerfect.Reciprocity
import OddPerfect.SpecialPrime
import OddPerfect.Pratt
import OddPerfect.Cyclotomic

/-!
# Bridges between the support of an odd perfect number and its divisor sums

Consequences of results already in the library.

* Group A: order menus and Fermat type primes. Every prime factor of exponent `e ≥ 2` has a
  receiver of exact order `e + 1`; an even exponent forces a receiver that is not of Fermat
  type; the special prime has a receiver of order two; and an odd perfect number has at
  least two prime factors that are not of Fermat type.
* Group B: direct edges into the special prime `s`. An edge from `q ≡ 3 (mod 4)` forces
  `q ∤ s + 1`; an edge from `3` forces `s ≡ 1 (mod 3)` and `v_3(N) ≤ (ω(N) - 1) ^ 2`; an edge
  from a Fermat type prime `q` forces `2 v_q(N) ≤ 3 (ω(N) - 1) ^ 2`.
* Group C: a kernel checked control support.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

variable {N : ℕ}

/-! ## Group A: order menus and Fermat type primes -/

/-- A number `p` is of Fermat type when `p - 1` is a power of two. -/
def FermatType (p : ℕ) : Prop := ∃ j : ℕ, p - 1 = 2 ^ j

/-- Order menu: for a prime factor `p` of an odd perfect number, either `v_p(N) = 1` or some
other prime factor `r` has `p` of exact order `v_p(N) + 1` modulo `r`. -/
theorem factorization_eq_one_or_exists_orderOf (h : OddPerfect N) {p : ℕ}
    (hp : p ∈ N.primeFactors) :
    N.factorization p = 1 ∨
      ∃ r ∈ N.primeFactors.erase p, N.factorization p + 1 = orderOf (p : ZMod r) := by
  have hpos : 0 < N.factorization p := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd
    h.ne_zero (Nat.dvd_of_mem_primeFactors hp)
  rcases Nat.lt_or_ge (N.factorization p) 2 with h1 | h2
  · left; omega
  · right
    obtain ⟨r, hr, ho, -⟩ := exists_primeFactor_modEq_one h hp (d := N.factorization p + 1)
      (by omega) dvd_rfl
    refine ⟨r, Finset.mem_erase.mpr ⟨?_, hr⟩, ho.symm⟩
    rintro rfl
    have : Fact (Nat.Prime _) := ⟨Nat.prime_of_mem_primeFactors hr⟩
    rw [ZMod.natCast_self, orderOf_zero] at ho
    omega

/-- An odd number at least `3` does not divide a power of two. -/
private theorem not_dvd_two_pow_of_odd {d j : ℕ} (hd : Odd d) (hd3 : 3 ≤ d) :
    ¬ d ∣ 2 ^ j := by
  intro hdvd
  have hcop : Nat.Coprime d (2 ^ j) :=
    Nat.Coprime.pow_right _ hd.coprime_two_right
  have := Nat.Coprime.eq_one_of_dvd hcop hdvd
  omega

/-- A prime factor `p` with even exponent has a receiver `r ≠ p` in the support that is not of
Fermat type: the order `v_p(N) + 1` of `p` modulo `r` is odd, at least `3`, and divides
`r - 1`. -/
theorem exists_not_fermatType_of_even (h : OddPerfect N) {p : ℕ} (hp : p ∈ N.primeFactors)
    (he : Even (N.factorization p)) :
    ∃ r ∈ N.primeFactors, r ≠ p ∧ ¬ FermatType r := by
  have hpos : 0 < N.factorization p := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd
    h.ne_zero (Nat.dvd_of_mem_primeFactors hp)
  obtain ⟨b, hb⟩ := he
  obtain ⟨r, hr, ho, hmod⟩ := exists_primeFactor_modEq_one h hp (d := N.factorization p + 1)
    (by omega) dvd_rfl
  refine ⟨r, hr, ?_, ?_⟩
  · rintro rfl
    have : Fact (Nat.Prime _) := ⟨Nat.prime_of_mem_primeFactors hr⟩
    rw [ZMod.natCast_self, orderOf_zero] at ho
    omega
  · rintro ⟨j, hj⟩
    have hr1 : 1 ≤ r := (Nat.prime_of_mem_primeFactors hr).one_lt.le
    have hdvd : N.factorization p + 1 ∣ r - 1 :=
      (Nat.modEq_iff_dvd' hr1).mp (by
        rw [Nat.ModEq, hmod, Nat.mod_eq_of_lt (by omega)])
    rw [hj] at hdvd
    exact not_dvd_two_pow_of_odd ⟨b, by omega⟩ (by omega) hdvd

/-- Order two witness for the special prime: if `q` has odd exponent in an odd perfect
number, some prime factor `r ≠ q` divides `(q + 1) / 2` and `q` has order `2` modulo `r`. -/
theorem exists_orderOf_eq_two_special (h : OddPerfect N) {q : ℕ} (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    ∃ r ∈ N.primeFactors, r ≠ q ∧ r ∣ (q + 1) / 2 ∧ orderOf (q : ZMod r) = 2 := by
  have hq4 := (special_mod_four h hq hodd).1
  have hq5 : 5 ≤ q := by
    have := hq.two_le
    rcases Nat.lt_or_ge q 5 with hlt | hge
    · interval_cases q <;> simp_all
    · exact hge
  set m := (q + 1) / 2 with hm
  have hm1 : m ≠ 1 := by omega
  set r := m.minFac
  have hr : r.Prime := Nat.minFac_prime hm1
  have hrm : r ∣ m := Nat.minFac_dvd m
  have hmodd : m % 2 = 1 := by omega
  have hr2 : r ≠ 2 := by
    intro h2
    rw [h2] at hrm
    omega
  have hrq1 : r ∣ q + 1 := hrm.trans ⟨2, by omega⟩
  obtain ⟨hrN, hrq⟩ := prime_dvd_of_dvd_succ_special h hq hodd hr hr2 hrq1
  refine ⟨r, Nat.mem_primeFactors.mpr ⟨hr, hrN, h.ne_zero⟩, hrq, hrm, ?_⟩
  have : Fact r.Prime := ⟨hr⟩
  have hneg : (q : ZMod r) = -1 := by
    have := (ZMod.natCast_eq_zero_iff (q + 1) r).mpr hrq1
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  rw [hneg, orderOf_neg_one, ZMod.ringChar_zmod_n, if_neg hr2]

open Classical in
/-- An odd perfect number has at least two prime factors that are not of Fermat type. The
filter uses classical decidability. -/
theorem two_le_card_not_fermatType (h : OddPerfect N) :
    2 ≤ (N.primeFactors.filter fun r => ¬ FermatType r).card := by
  classical
  by_contra hlt
  have hle : (N.primeFactors.filter fun r => ¬ FermatType r).card ≤ 1 := by omega
  have huniq := Finset.card_le_one.mp hle
  have hmem : ∀ {r}, r ∈ N.primeFactors → ¬ FermatType r →
      r ∈ N.primeFactors.filter fun r => ¬ FermatType r :=
    fun hr hf => Finset.mem_filter.mpr ⟨hr, hf⟩
  obtain ⟨s, hs, -, -, hk4, hev⟩ := exists_special_prime h
  have hsodd : Odd (N.factorization s) := Nat.odd_iff.mpr (by omega)
  -- every non Fermat prime factor equals `s`
  have hall : ∀ r ∈ N.primeFactors, ¬ FermatType r → r = s := by
    intro t ht htf
    by_contra hts
    obtain ⟨r, hr, hrt, hrf⟩ :=
      exists_not_fermatType_of_even h ht (hev t (Nat.prime_of_mem_primeFactors ht) hts)
    exact hrt (huniq r (hmem hr hrf) t (hmem ht htf))
  apply not_all_components_special_powers h hs hsodd
  intro p hp hps
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpe := hev p hpp hps
  have hpF : FermatType p := by
    by_contra hf
    exact hps (hall p hp hf)
  obtain ⟨j, hj⟩ := hpF
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hp)
  have hσ0 : σ 1 (p ^ N.factorization p) ≠ 0 :=
    (sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)).ne'
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hσ0 fun {r} hr hrd => ?_⟩
  obtain ⟨b, hb⟩ := hpe
  have hr2 : r ≠ 2 := by
    rintro rfl
    rcases (prime_dvd_sigma_prime_pow hpp Nat.prime_two hrd).2 with ⟨-, h2⟩ | ⟨h1, -, h3⟩
    · omega
    · have := Nat.le_of_dvd one_pos h3
      omega
  have hrN : r ∈ N.primeFactors := Nat.mem_primeFactors.mpr
    ⟨hr, OPNStarter.force_prime h.perfect hpp rfl hr hr2 hrd, h.ne_zero⟩
  rcases (prime_dvd_sigma_prime_pow hpp hr hrd).2 with ⟨h1, -⟩ | ⟨h1, hd, hdr⟩
  · exfalso
    have hrp : r ∣ p - 1 :=
      (Nat.modEq_iff_dvd' hpp.one_lt.le).mp (by
        rw [Nat.ModEq, h1, Nat.mod_eq_of_lt hr.one_lt])
    rw [hj] at hrp
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hrp))
  · refine hall r hrN fun ⟨i, hi⟩ => ?_
    rw [hi] at hdr
    have hoddd : Odd (orderOf (p : ZMod r)) := Odd.of_dvd_nat ⟨b, by omega⟩ hd
    exact not_dvd_two_pow_of_odd hoddd (by
      obtain ⟨c, hc⟩ := hoddd
      omega) hdr

/-! ## Group B: direct edges into the special prime -/

/-- An edge from a prime `q ≡ 3 (mod 4)` into the special prime `s` forces `q ∤ s + 1`. The
exponent of `q` is even, so `q` is a square modulo `s`; as `s ≡ 1 (mod 4)`, reciprocity
makes `s` a square modulo `q`, while `-1` is not a square modulo `q`. No membership or
parity hypothesis on `q` is needed. -/
theorem not_dvd_succ_special_of_mod_four_eq_three (h : OddPerfect N) {s q : ℕ}
    (hs : s.Prime) (hodd : Odd (N.factorization s)) (hq : q.Prime) (hq4 : q % 4 = 3)
    (hdvd : s ∣ σ 1 (q ^ N.factorization q)) : ¬ q ∣ s + 1 := by
  intro hqs
  have hs4 := (special_mod_four h hs hodd).1
  have hqs' : q ≠ s := by rintro rfl; omega
  have he := even_factorization_of_ne h hs hodd hq hqs'
  have : Fact q.Prime := ⟨hq⟩
  have : Fact s.Prime := ⟨hs⟩
  have hq2 : q ≠ 2 := by rintro rfl; omega
  have hs2 : s ≠ 2 := by rintro rfl; omega
  have h1 := legendreSym_receiver_of_dvd_sigma_even (p := q) (r := s) hq2 hs2 he hdvd
  rw [if_neg (by omega)] at h1
  have hz := (ZMod.natCast_eq_zero_iff (s + 1) q).mpr hqs
  push_cast at hz
  have hneg : ((s : ℤ) : ZMod q) = ((-1 : ℤ) : ZMod q) := by
    rw [Int.cast_natCast, Int.cast_neg, Int.cast_one]
    exact eq_neg_of_add_eq_zero_left hz
  have h2 : legendreSym q s = legendreSym q (-1) := by
    rw [legendreSym, legendreSym, hneg]
  rw [h2, legendreSym.at_neg_one hq2, ZMod.χ₄_nat_three_mod_four hq4] at h1
  norm_num at h1

/-- An edge from `3` into the special prime `s` forces `3 ∤ s + 1`. -/
theorem not_three_dvd_succ_special (h : OddPerfect N) {s : ℕ} (hs : s.Prime)
    (hodd : Odd (N.factorization s)) (hdvd : s ∣ σ 1 (3 ^ N.factorization 3)) :
    ¬ 3 ∣ s + 1 :=
  not_dvd_succ_special_of_mod_four_eq_three h hs hodd Nat.prime_three rfl hdvd

/-- An edge from `3` into the special prime `s` forces `s ≡ 1 (mod 3)`. -/
theorem special_mod_three_of_dvd_sigma_three (h : OddPerfect N) {s : ℕ} (hs : s.Prime)
    (hodd : Odd (N.factorization s)) (hdvd : s ∣ σ 1 (3 ^ N.factorization 3)) :
    s % 3 = 1 := by
  have h1 := not_three_dvd_succ_special h hs hodd hdvd
  have hs4 := (special_mod_four h hs hodd).1
  have h3 : ¬ 3 ∣ s := fun h3 => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hs).mp h3
    omega
  omega

/-- An edge from `3` into the special prime gives `v_3(N) ≤ (ω(N) - 1) ^ 2`. -/
theorem factorization_three_le_sq_of_dvd_sigma (h : OddPerfect N) {s : ℕ} (hs : s.Prime)
    (hodd : Odd (N.factorization s)) (hdvd : s ∣ σ 1 (3 ^ N.factorization 3)) :
    N.factorization 3 ≤ (N.primeFactors.card - 1) ^ 2 := by
  have := factorization_three_le h hs hodd
  rwa [padicValNat.eq_zero_of_not_dvd (not_three_dvd_succ_special h hs hodd hdvd),
    add_zero] at this

/-- An edge from an odd Fermat type prime `q` into the special prime `s` gives
`2 v_q(N) ≤ 3 (ω(N) - 1) ^ 2`: with `t = v_q(s + 1)`, the Fermat bound gives
`v_q(N) ≤ (ω(N) - 1) ^ 2 + t` and Lemma 1 of Brent, Cohen and te Riele gives `3 t ≤ v_q(N)`. -/
theorem two_mul_factorization_le_of_fermat_of_dvd_sigma (h : OddPerfect N) {s q j : ℕ}
    (hs : s.Prime) (hodd : Odd (N.factorization s)) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqj : q - 1 = 2 ^ j) (hdvd : s ∣ σ 1 (q ^ N.factorization q)) :
    2 * N.factorization q ≤ 3 * (N.primeFactors.card - 1) ^ 2 := by
  have h1 := factorization_le_of_fermat h hq hqj hs hodd
  have hs2 : s ≠ 2 := by
    have := (special_mod_four h hs hodd).1
    rintro rfl
    omega
  have h2 := three_mul_le_of_dvd_sigma hs hq hs2 hq2 hdvd
    (pow_padicValNat_dvd (p := q) (n := s + 1))
  omega

/-! ## Group C: a kernel checked control -/

/-- `4294967291 = 2 ^ 32 - 5` is prime, by a Pratt certificate. -/
theorem prime_4294967291 : Nat.Prime 4294967291 :=
  Pratt.prime_of_checkPrime (c := [(22605091, 11, [2, 3, 5, 23, 181, 181]),
    (4294967291, 2, [2, 5, 19, 22605091])]) (by decide +kernel)

/-- Control only. The set `{3, 5, 17, 257, 65537, 4294967291}` consists of primes, its
product `R` is `18446744047939747845`, and with `F` the product of `p - 1` over the set,
`R - 2 F = 5`. This shows that the integrality gap of a squarefree odd radical can be tiny.
The set is not the support of an odd perfect number (see
`primeFactors_ne_control`); it is only a control. -/
theorem control_support_facts :
    (∀ p ∈ ({3, 5, 17, 257, 65537, 4294967291} : Finset ℕ), p.Prime) ∧
      (∏ p ∈ ({3, 5, 17, 257, 65537, 4294967291} : Finset ℕ), p) = 18446744047939747845 ∧
      (∏ p ∈ ({3, 5, 17, 257, 65537, 4294967291} : Finset ℕ), p) -
          2 * (∏ p ∈ ({3, 5, 17, 257, 65537, 4294967291} : Finset ℕ), (p - 1)) = 5 := by
  refine ⟨?_, by simp, by simp⟩
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact prime_4294967291

/-- No odd perfect number has support exactly `{3, 5, 17, 257, 65537, 4294967291}`. The prime
`4294967291 ≡ 3 (mod 4)` has even exponent, so it needs a receiver of non Fermat type other
than itself, but `3, 5, 17, 257, 65537` are all of Fermat type. -/
theorem primeFactors_ne_control (h : OddPerfect N)
    (hN : N.primeFactors = {3, 5, 17, 257, 65537, 4294967291}) : False := by
  have hP : 4294967291 ∈ N.primeFactors := by rw [hN]; simp
  have hPp := Nat.prime_of_mem_primeFactors hP
  have he : Even (N.factorization 4294967291) := by
    by_contra ho
    have := (special_mod_four h hPp (Nat.not_even_iff_odd.mp ho)).1
    norm_num at this
  obtain ⟨r, hr, hrP, hrf⟩ := exists_not_fermatType_of_even h hP he
  rw [hN] at hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hrf ⟨1, rfl⟩
  · exact hrf ⟨2, rfl⟩
  · exact hrf ⟨4, rfl⟩
  · exact hrf ⟨8, rfl⟩
  · exact hrf ⟨16, rfl⟩
  · exact hrP rfl

end OddPerfect

#print axioms OddPerfect.factorization_eq_one_or_exists_orderOf
#print axioms OddPerfect.exists_not_fermatType_of_even
#print axioms OddPerfect.exists_orderOf_eq_two_special
#print axioms OddPerfect.two_le_card_not_fermatType
#print axioms OddPerfect.not_dvd_succ_special_of_mod_four_eq_three
#print axioms OddPerfect.not_three_dvd_succ_special
#print axioms OddPerfect.special_mod_three_of_dvd_sigma_three
#print axioms OddPerfect.factorization_three_le_sq_of_dvd_sigma
#print axioms OddPerfect.two_mul_factorization_le_of_fermat_of_dvd_sigma
#print axioms OddPerfect.prime_4294967291
#print axioms OddPerfect.control_support_facts
#print axioms OddPerfect.primeFactors_ne_control
