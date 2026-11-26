import OddPerfect.UniformExponents
import OddPerfect.Zsigmondy
import OddPerfect.EqualExponentNotSpecial

/-!
# Equal exponents `l - 1`: a divisor fan at the special prime

Let `N` be an odd perfect number with special prime `q` of exponent `a`, and let `l` be an odd
prime such that every prime factor `p ≠ q` of `N` has exponent `l - 1`. Write
`c = v_l(a + 1)` and `B = (a + 1) / l ^ c`.

* `card_divisors_filter_dvd_le_card_congrPrimes` (the fan): every divisor `d` of `a + 1` with
  `l ∣ d` is the order of `q` modulo its own prime factor `r_d ≠ q` of `N`, and `r_d ≡ 1 (mod l)`.
  This part needs no hypothesis on the exponents.
* `card_divisors_filter_dvd_eq`: for `n ≠ 0` and `l` prime, the divisors of `n` divisible by `l`
  number `v_l(n) τ(n / l ^ v_l(n))`.
* `padicValNat_mul_succ_card_divisors_le`: `c (τ(B) + 1) ≤ l - 1`.
* `three_mul_padicValNat_le`: `3 c ≤ l - 1`.
* `padicValNat_mul_two_mul_add_three_le`: for a prime factor `w ≠ l` of `N` with
  `b = v_w(a + 1)`, `c (2 b + 3) ≤ l - 1`.

When `c = 0` every inequality is trivial. These statements bound `v_l(a + 1)` inside the
family; they do not exclude the family.

Restricted result; no published source was checked; novelty not verified.
-/

namespace OddPerfect

/-- **The fan.** For an odd perfect number `N` with special prime `q` and an odd prime `l`, the
divisors `d` of `v_q(N) + 1` with `l ∣ d` are at most as many as the prime factors `s ≠ q` of
`N` with `s ≡ 1 (mod l)`. -/
theorem card_divisors_filter_dvd_le_card_congrPrimes {N q l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2) :
    ((N.factorization q + 1).divisors.filter (l ∣ ·)).card ≤ (congrPrimes N q l).card := by
  have : Fact q.Prime := ⟨hq⟩
  have hqN : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq,
    Nat.dvd_of_factorization_pos (by obtain ⟨k, hk⟩ := hodd; omega), h.ne_zero⟩
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have hex : ∀ d ∈ (N.factorization q + 1).divisors.filter (l ∣ ·),
      ∃ t ∈ congrPrimes N q l, orderOf (q : ZMod t) = d := by
    intro d hd
    obtain ⟨hdn, hld⟩ := Finset.mem_filter.mp hd
    have hd3 : 3 ≤ d := le_trans hl3 (Nat.le_of_dvd (Nat.pos_of_mem_divisors hdn) hld)
    obtain ⟨t, htN, ho, hmod⟩ :=
      exists_primeFactor_modEq_one h hqN hd3 (Nat.dvd_of_mem_divisors hdn)
    refine ⟨t, ?_, ho⟩
    unfold congrPrimes
    refine Finset.mem_filter.mpr ⟨htN, ?_, ?_⟩
    · rintro rfl
      rw [ZMod.natCast_self, orderOf_zero] at ho
      omega
    · rw [← Nat.mod_mod_of_dvd t hld, hmod]
      exact Nat.mod_eq_of_lt hl.one_lt
  choose! f hf hfo using hex
  exact Finset.card_le_card_of_injOn f (fun a ha => hf a ha)
    (fun a ha b hb hab => by rw [← hfo a ha, ← hfo b hb, hab])

/-- `l ^ v_l(n) ∣ n`. -/
private lemma divFan_pow_dvd (l n : ℕ) : l ^ padicValNat l n ∣ n := by
  rw [Nat.padicValNat_def]; exact pow_multiplicity_dvd _ _

/-- `n = l ^ v_l(n) * (n / l ^ v_l(n))`. -/
private lemma divFan_eq_mul (n l : ℕ) :
    n = l ^ padicValNat l n * (n / l ^ padicValNat l n) :=
  (Nat.mul_div_cancel' (divFan_pow_dvd l n)).symm

/-- A divisor of `n` coprime to `l` divides `n / l ^ v_l(n)`. -/
private lemma divFan_dvd_div {m n l : ℕ} (hml : Nat.Coprime m l) (hmn : m ∣ n) :
    m ∣ n / l ^ padicValNat l n := by
  rw [divFan_eq_mul n l] at hmn
  exact (Nat.Coprime.pow_right _ hml).dvd_of_dvd_mul_left hmn

/-- `n / l ^ v_l(n) ≠ 0` for `n ≠ 0` and `l` prime. -/
private lemma divFan_div_ne_zero {n l : ℕ} (hn : n ≠ 0) (hl : l.Prime) :
    n / l ^ padicValNat l n ≠ 0 :=
  (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (divFan_pow_dvd l n))
    (pow_pos hl.pos _)).ne'

/-- **Counting the divisors divisible by `l`.** For `n ≠ 0` and a prime `l`, with
`c = v_l(n)`, the divisors `d` of `n` with `l ∣ d` number `c τ(n / l ^ c)`. -/
theorem card_divisors_filter_dvd_eq {n l : ℕ} (hn : n ≠ 0) (hl : l.Prime) :
    (n.divisors.filter (l ∣ ·)).card =
      padicValNat l n * (n / l ^ padicValNat l n).divisors.card := by
  have : Fact l.Prime := ⟨hl⟩
  have hn' := divFan_eq_mul n l
  have hB0 := divFan_div_ne_zero hn hl
  have hns : ¬ l ^ (padicValNat l n + 1) ∣ n := by
    intro hd
    have := (multiplicity_dvd_iff_le hn).mp hd
    rw [← Nat.padicValNat_def] at this
    omega
  set c := padicValNat l n
  set B := n / l ^ c
  have hlB : ¬ l ∣ B := by
    rintro ⟨k, hk⟩
    exact hns ⟨k, by rw [hn', hk]; ring⟩
  have hcop : Nat.Coprime (l ^ c) B :=
    Nat.Coprime.pow_left c ((Nat.Prime.coprime_iff_not_dvd hl).mpr hlB)
  have hpow : (l ^ c).divisors.card = c + 1 := by
    rw [← ArithmeticFunction.sigma_zero_apply,
      ArithmeticFunction.sigma_zero_apply_prime_pow hl]
  have hτn : n.divisors.card = (c + 1) * B.divisors.card := by
    rw [hn', Nat.Coprime.card_divisors_mul hcop, hpow]
  have hfilt : n.divisors.filter (fun d => ¬ l ∣ d) = B.divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, -⟩, hld⟩
      refine ⟨?_, hB0⟩
      have hcd : Nat.Coprime d (l ^ c) := Nat.Coprime.pow_right c
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hl).mpr hld))
      rw [hn'] at hd
      exact hcd.dvd_of_dvd_mul_left hd
    · rintro ⟨hd, -⟩
      exact ⟨⟨by rw [hn']; exact Dvd.dvd.mul_left hd _, hn⟩, fun h => hlB (h.trans hd)⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := n.divisors) (fun d => l ∣ d)
  rw [hfilt, hτn] at hsplit
  have : (c + 1) * B.divisors.card = c * B.divisors.card + B.divisors.card := by ring
  omega

/-- **The divisor fan inequality.** Let `N` be an odd perfect number with special prime `q`,
and let `l` be an odd prime such that every prime factor `p ≠ q` of `N` has exponent `l - 1`.
With `c = v_l(v_q(N) + 1)` and `B = (v_q(N) + 1) / l ^ c`, `c (τ(B) + 1) ≤ l - 1`. -/
theorem padicValNat_mul_succ_card_divisors_le {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    padicValNat l (N.factorization q + 1) *
        (((N.factorization q + 1) / l ^ padicValNat l (N.factorization q + 1)).divisors.card
          + 1) ≤ l - 1 := by
  obtain ⟨hlN, hlq⟩ := ordinary_of_all_exponents_eq_pred h hq hodd hl hl2 hexp
  have hcard := card_congrPrimes_add_padicValNat h hq hodd hl hexp hlN hlq
  have hfan := card_divisors_filter_dvd_le_card_congrPrimes h hq hodd hl hl2
  rw [card_divisors_filter_dvd_eq (n := N.factorization q + 1) (by omega) hl] at hfan
  rw [Nat.mul_add_one]
  omega

/-- `2 ≤ τ(B)` for even `B ≠ 0`. -/
private lemma divFan_two_le_card {B : ℕ} (hB : B ≠ 0) (h2 : 2 ∣ B) : 2 ≤ B.divisors.card := by
  have h2d : (Nat.divisors 2).card = 2 := by decide
  have := Finset.card_le_card (Nat.divisors_subset_of_dvd hB h2)
  rw [h2d] at this
  exact this

/-- In the family of `padicValNat_mul_succ_card_divisors_le`, `3 v_l(v_q(N) + 1) ≤ l - 1`. -/
theorem three_mul_padicValNat_le {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    3 * padicValNat l (N.factorization q + 1) ≤ l - 1 := by
  have hmain := padicValNat_mul_succ_card_divisors_le h hq hodd hl hl2 hexp
  have h2 : 2 ∣ N.factorization q + 1 := by obtain ⟨k, hk⟩ := hodd; exact ⟨k + 1, by omega⟩
  have hn0 : N.factorization q + 1 ≠ 0 := by omega
  have hB2 := divFan_dvd_div ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm hl2)) h2
  have hτ := divFan_two_le_card (divFan_div_ne_zero hn0 hl) hB2
  rw [Nat.mul_comm]
  exact le_trans (Nat.mul_le_mul_left _ (by omega)) hmain

/-- In the family of `padicValNat_mul_succ_card_divisors_le`, for a prime factor `w ≠ l` of
`N` with `b = v_w(v_q(N) + 1)`, `v_l(v_q(N) + 1) (2 b + 3) ≤ l - 1`. -/
theorem padicValNat_mul_two_mul_add_three_le {N q l w : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hw : w ∈ N.primeFactors) (hwl : w ≠ l) :
    padicValNat l (N.factorization q + 1) * (2 * padicValNat w (N.factorization q + 1) + 3) ≤
      l - 1 := by
  have hmain := padicValNat_mul_succ_card_divisors_le h hq hodd hl hl2 hexp
  have hwp := Nat.prime_of_mem_primeFactors hw
  have hw2 : w ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hw)
  have h2 : 2 ∣ N.factorization q + 1 := by obtain ⟨k, hk⟩ := hodd; exact ⟨k + 1, by omega⟩
  have hn0 : N.factorization q + 1 ≠ 0 := by omega
  set n := N.factorization q + 1
  set b := padicValNat w n
  have hB2 := divFan_dvd_div ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm hl2)) h2
  have hBw : w ^ b ∣ n / l ^ padicValNat l n :=
    divFan_dvd_div (Nat.Coprime.pow_left b ((Nat.coprime_primes hwp hl).mpr hwl))
      (divFan_pow_dvd w n)
  have hcop : Nat.Coprime 2 (w ^ b) :=
    Nat.Coprime.pow_right b ((Nat.coprime_primes Nat.prime_two hwp).mpr (Ne.symm hw2))
  have hdvd := hcop.mul_dvd_of_dvd_of_dvd hB2 hBw
  have h2d : (Nat.divisors 2).card = 2 := by decide
  have hcard : (2 * w ^ b).divisors.card = 2 * (b + 1) := by
    rw [Nat.Coprime.card_divisors_mul hcop, h2d, ← ArithmeticFunction.sigma_zero_apply,
      ArithmeticFunction.sigma_zero_apply_prime_pow hwp]
  have hτ := Finset.card_le_card (Nat.divisors_subset_of_dvd (divFan_div_ne_zero hn0 hl) hdvd)
  rw [hcard] at hτ
  exact le_trans (Nat.mul_le_mul_left _ (by omega)) hmain

end OddPerfect

#print axioms OddPerfect.card_divisors_filter_dvd_le_card_congrPrimes
#print axioms OddPerfect.card_divisors_filter_dvd_eq
#print axioms OddPerfect.padicValNat_mul_succ_card_divisors_le
#print axioms OddPerfect.three_mul_padicValNat_le
#print axioms OddPerfect.padicValNat_mul_two_mul_add_three_le
