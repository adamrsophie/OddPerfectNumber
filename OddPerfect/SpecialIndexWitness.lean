import OddPerfect.Zsigmondy
import OddPerfect.EqualExponents

/-!
# Witnesses of the special index and the budget of an odd prime

Let `N` be an odd perfect number with special prime `q` of exponent `a`, and let `l` be an odd
prime. Put `v = v_l(a + 1)`, `s = v_l(σ(q ^ a))` and `c = v_l(N)`. Then

    2 v + s ≤ c + #{p prime, p ∣ N, p ≠ q, p ≡ 1 (mod l), l ∤ v_p(N) + 1}

(`special_index_witnesses`). For `l = 3` the counted primes have exponent at least `4`
(`special_index_three`), and `v ≤ s` (`padicValNat_three_succ_le_sigma`), so
`3 v ≤ c + #{…}` (`three_mul_special_index_le`). In particular, if `3 ^ 2` exactly divides `N`
and `9 ∣ a + 1`, then at least four prime factors `p ≠ q` with `p ≡ 1 (mod 3)` have exponent at
least `4` (`four_exceptions_of_three_sq_of_nine_dvd`).

Proof idea. For `1 ≤ j ≤ v` both `l ^ j` and `2 l ^ j` divide `a + 1`, and Zsigmondy gives a
prime factor of `σ(q ^ a)` modulo which `q` has exactly that order; these `2 v` primes are distinct
prime factors of `N`, different from `q` and `1` modulo `l`. The budget
`c = Σ_p v_l(σ(p ^ (v_p(N))))` pays `s` for `q` and at least `1` for each witness `r` with
`l ∣ v_r(N) + 1`, so the remaining witnesses are in the counted set.

Whether this inequality is in the literature was not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The witness step: an odd perfect number has at least `2 v_l(a + 1)` prime factors other
than the special prime `q` (of exponent `a`) that are `1` modulo the odd prime `l`. -/
theorem two_mul_special_index_le_card {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2) :
    2 * padicValNat l (N.factorization q + 1) ≤
      (N.primeFactors.filter fun p => p ≠ q ∧ p % l = 1).card := by
  have : Fact l.Prime := ⟨hl⟩
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have hq3 : 3 ≤ q := by have := (special_mod_four h hq hodd).1; have := hq.two_le; omega
  have hlv : l ^ padicValNat l (N.factorization q + 1) ∣ N.factorization q + 1 := by
    rw [Nat.padicValNat_def]; exact pow_multiplicity_dvd _ _
  have h2a : 2 ∣ N.factorization q + 1 := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k + 1, by omega⟩
  have hcop : Nat.Coprime 2 l := (Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm hl2)
  set v := padicValNat l (N.factorization q + 1)
  let I := Finset.Icc 1 v ×ˢ Finset.range 2
  let d : ℕ × ℕ → ℕ := fun x => 2 ^ x.2 * l ^ x.1
  have hd : ∀ x ∈ I, 3 ≤ d x ∧ d x ∣ N.factorization q + 1 ∧ l ∣ d x := by
    rintro ⟨j, k⟩ hx
    simp only [I, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hx
    obtain ⟨⟨hj1, hjv⟩, hk⟩ := hx
    have hlj : l ≤ l ^ j := Nat.le_self_pow (by omega) l
    have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    refine ⟨?_, ?_, ?_⟩
    · show 3 ≤ 2 ^ k * l ^ j
      nlinarith
    · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow _ _ hcop)
        ((Nat.pow_dvd_pow 2 (by omega : k ≤ 1)).trans (by simpa using h2a))
        ((Nat.pow_dvd_pow l hjv).trans hlv)
    · exact Dvd.dvd.mul_left (dvd_pow_self l (by omega)) _
  have hw : ∀ x : ℕ × ℕ, ∃ r : ℕ, x ∈ I → r.Prime ∧ r ∣ σ 1 (q ^ N.factorization q) ∧
      orderOf (q : ZMod r) = d x ∧ r % d x = 1 := by
    intro x
    by_cases hx : x ∈ I
    · obtain ⟨r, hr⟩ := exists_prime_dvd_sigma_orderOf_eq hq hq3 (hd x hx).1 (hd x hx).2.1
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h' => absurd h' hx⟩
  choose w hw using hw
  have hcard : I.card = 2 * v := by
    rw [Finset.card_product, Nat.card_Icc, Finset.card_range]
    omega
  rw [← hcard]
  refine Finset.card_le_card_of_injOn w ?_ ?_
  · intro x hx
    have hx' : x ∈ I := hx
    obtain ⟨hr, hrσ, ho, hm⟩ := hw x hx'
    obtain ⟨hd3, -, hld⟩ := hd x hx'
    have hr2 : w x ≠ 2 := by
      intro h2
      rw [h2, Nat.mod_eq_of_lt (by omega : 2 < d x)] at hm
      omega
    have hrN := OPNStarter.force_prime h.2 hq rfl hr hr2 hrσ
    have hrq : w x ≠ q := by
      intro hrq
      rw [hrq] at ho
      have : Fact (1 < q) := ⟨hq.one_lt⟩
      rw [ZMod.natCast_self, orderOf_eq_zero_iff'.mpr] at ho
      · omega
      · intro k hk h0
        rw [zero_pow hk.ne'] at h0
        exact zero_ne_one h0
    have hml : w x % l = 1 := by
      rw [← Nat.mod_mod_of_dvd (w x) hld, hm, Nat.mod_eq_of_lt hl.one_lt]
    exact Finset.mem_coe.mpr
      (Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hr, hrN, h.ne_zero⟩, hrq, hml⟩)
  · rintro ⟨j, k⟩ hx ⟨j', k'⟩ hy hxy
    have hx' : (j, k) ∈ I := hx
    have hy' : (j', k') ∈ I := hy
    have h1 := (hw _ hx').2.2.1
    have h2 := (hw _ hy').2.2.1
    rw [hxy, h2] at h1
    simp only [I, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hx' hy'
    simp only [d] at h1
    have hol : Odd l := hl.odd_of_ne_two hl2
    obtain ⟨m, hm⟩ := hol.pow (n := j)
    obtain ⟨m', hm'⟩ := hol.pow (n := j')
    have hkk : k' = k := by
      have hk : k < 2 := hx'.2
      have hk' : k' < 2 := hy'.2
      interval_cases k <;> interval_cases k' <;>
        simp only [pow_zero, pow_one, one_mul] at h1 <;> omega
    subst hkk
    have hjj := Nat.pow_right_injective hl.two_le
      (Nat.eq_of_mul_eq_mul_left (by positivity) h1)
    rw [hjj]

/-- The budget of an odd prime `l`: the special prime `q` pays `v_l(σ(q ^ a))`, and every prime
factor `p ≠ q` with `p ≡ 1 (mod l)` and `l ∣ v_p(N) + 1` pays at least one factor `l`. -/
theorem special_index_budget {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2) :
    padicValNat l (σ 1 (q ^ N.factorization q)) +
        (N.primeFactors.filter fun p =>
          p ≠ q ∧ p % l = 1 ∧ l ∣ N.factorization p + 1).card ≤
      N.factorization l := by
  have : Fact l.Prime := ⟨hl⟩
  have hbal := OPNStarter.valuation_balance h.2 l
  have h2 : Nat.factorization 2 l = 0 := by
    rw [Nat.prime_two.factorization, Finsupp.single_apply, if_neg (Ne.symm hl2)]
  have hqN : q ∈ N.primeFactors := by
    have : N.factorization q ≠ 0 := by obtain ⟨k, hk⟩ := hodd; omega
    exact Nat.mem_primeFactors.mpr
      ⟨hq, Nat.dvd_of_factorization_pos this, h.ne_zero⟩
  set G := N.primeFactors.filter fun p => p ≠ q ∧ p % l = 1 ∧ l ∣ N.factorization p + 1
  let f : ℕ → ℕ := fun p => (σ 1 (p ^ N.factorization p)).factorization l
  have hqG : q ∉ G := by simp [G]
  have hsub : insert q G ⊆ N.primeFactors :=
    Finset.insert_subset hqN (Finset.filter_subset _ _)
  have hle := Finset.sum_le_sum_of_subset (f := f) hsub
  rw [Finset.sum_insert hqG] at hle
  have hone : ∀ p ∈ G, 1 ≤ f p := by
    intro p hp
    simp only [G, Finset.mem_filter] at hp
    obtain ⟨hpN, -, hp1, hpl⟩ := hp
    have hpp := Nat.prime_of_mem_primeFactors hpN
    simp only [f]
    rw [Nat.factorization_def _ hl, ← Nat.padicValNat_def,
      padicValNat_sigma_of_mod_eq_one hpp hl hl2 hp1, Nat.padicValNat_def]
    exact one_le_padicValNat_of_dvd (by omega) hpl
  have hc : G.card ≤ ∑ p ∈ G, f p := by simpa using Finset.card_nsmul_le_sum G f 1 hone
  have hfq : f q = padicValNat l (σ 1 (q ^ N.factorization q)) := by
    rw [Nat.padicValNat_def]; exact Nat.factorization_def _ hl
  simp only [f] at hle hbal hfq hc
  omega

/-- The special index inequality: `2 v_l(a + 1) + v_l(σ(q ^ a)) ≤ v_l(N) + #{p}` over the prime
factors `p ≠ q` of `N` with `p ≡ 1 (mod l)` and `l ∤ v_p(N) + 1`, for every odd prime `l`. -/
theorem special_index_witnesses {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2) :
    2 * padicValNat l (N.factorization q + 1) +
        padicValNat l (σ 1 (q ^ N.factorization q)) ≤
      N.factorization l + (N.primeFactors.filter fun p =>
        p ≠ q ∧ p % l = 1 ∧ ¬ l ∣ N.factorization p + 1).card := by
  have hw := two_mul_special_index_le_card h hq hodd hl hl2
  have hb := special_index_budget h hq hodd hl hl2
  have hs := Finset.card_filter_add_card_filter_not
    (s := N.primeFactors.filter fun p => p ≠ q ∧ p % l = 1)
    (fun p => l ∣ N.factorization p + 1)
  simp only [Finset.filter_filter, and_assoc] at hs
  omega

/-- The case `l = 3`: a counted prime has exponent at least `4`. -/
theorem special_index_three {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    2 * padicValNat 3 (N.factorization q + 1) +
        padicValNat 3 (σ 1 (q ^ N.factorization q)) ≤
      N.factorization 3 + (N.primeFactors.filter fun p =>
        p ≠ q ∧ p % 3 = 1 ∧ 4 ≤ N.factorization p ∧ ¬ 3 ∣ N.factorization p + 1).card := by
  have hm := special_index_witnesses h hq hodd Nat.prime_three (by decide)
  have hc : (N.primeFactors.filter fun p =>
        p ≠ q ∧ p % 3 = 1 ∧ ¬ 3 ∣ N.factorization p + 1) =
      (N.primeFactors.filter fun p =>
        p ≠ q ∧ p % 3 = 1 ∧ 4 ≤ N.factorization p ∧ ¬ 3 ∣ N.factorization p + 1) := by
    apply Finset.filter_congr
    intro p hpN
    have hpp := Nat.prime_of_mem_primeFactors hpN
    constructor
    · rintro ⟨hpq, hp1, hp3⟩
      obtain ⟨k, hk⟩ := even_factorization_of_ne h hq hodd hpp hpq
      have hpos := hpp.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hpN)
      refine ⟨hpq, hp1, ?_, hp3⟩
      have hne : N.factorization p ≠ 2 := fun h2 => hp3 (by rw [h2])
      omega
    · rintro ⟨hpq, hp1, -, hp3⟩
      exact ⟨hpq, hp1, hp3⟩
  rw [hc] at hm
  exact hm

/-- For a prime `q ≠ 3` and an odd `a`, `v_3(a + 1) ≤ v_3(σ(q ^ a))`. -/
theorem padicValNat_three_succ_le_sigma {q a : ℕ} (hq : q.Prime) (hq3 : q ≠ 3) (ha : Odd a) :
    padicValNat 3 (a + 1) ≤ padicValNat 3 (σ 1 (q ^ a)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := ha
  have hq1 : 1 < q := hq.one_lt
  have hnd : ¬ 3 ∣ q := fun h3 => hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp h3).symm
  have hsq : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod]
    have : q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases this with h | h <;> rw [h]
  have hxy : 3 ∣ q ^ 2 - 1 := by omega
  have hx : ¬ 3 ∣ q ^ 2 := by omega
  have h1q : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero hq1
  have hlte := padicValNat.pow_sub_pow (p := 3) ⟨1, rfl⟩ h1q hxy hx (n := m + 1) (by omega)
  have key := sigma_prime_pow_mul_pred hq a
  have hpow : q ^ (a + 1) = (q ^ 2) ^ (m + 1) := by rw [← pow_mul]; congr 1; omega
  have key' : σ 1 (q ^ a) * (q - 1) = (q ^ 2) ^ (m + 1) - 1 ^ (m + 1) := by
    rw [key, hpow, one_pow]
  have hσ0 : σ 1 (q ^ a) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hq.ne_zero)).ne'
  rw [← key', padicValNat.mul hσ0 (by omega)] at hlte
  simp only [← Nat.padicValNat_def] at hlte
  have hdiv : q - 1 ∣ q ^ 2 - 1 := by simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow q 1 2
  have hle : padicValNat 3 (q - 1) ≤ padicValNat 3 (q ^ 2 - 1) :=
    by simp only [Nat.padicValNat_def]
       exact (padicValNat_dvd_iff_le (by omega)).mp ((pow_multiplicity_dvd _ _).trans hdiv)
  have hv : padicValNat 3 (a + 1) = padicValNat 3 (m + 1) := by
    rw [show a + 1 = 2 * (m + 1) by omega]
    simp only [Nat.padicValNat_def]
    rw [padicValNat.mul (by omega) (by omega),
      multiplicity_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2), zero_add]
  omega

/-- `3 v_3(a + 1) ≤ v_3(N) + #{p ≠ q : p ≡ 1 (mod 3), v_p(N) ≥ 4, 3 ∤ v_p(N) + 1}`. -/
theorem three_mul_special_index_le {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    3 * padicValNat 3 (N.factorization q + 1) ≤
      N.factorization 3 + (N.primeFactors.filter fun p =>
        p ≠ q ∧ p % 3 = 1 ∧ 4 ≤ N.factorization p ∧ ¬ 3 ∣ N.factorization p + 1).card := by
  have hm := special_index_three h hq hodd
  have hq3 : q ≠ 3 := by have := (special_mod_four h hq hodd).1; omega
  have hv := padicValNat_three_succ_le_sigma hq hq3 hodd
  omega

/-- If `3 ^ 2` exactly divides the odd perfect number `N` and `9 ∣ a + 1` for the exponent `a`
of the special prime `q`, then at least four prime factors `p ≠ q` with `p ≡ 1 (mod 3)` have
exponent at least `4`. -/
theorem four_exceptions_of_three_sq_of_nine_dvd {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (h3 : N.factorization 3 = 2)
    (h9 : 9 ∣ N.factorization q + 1) :
    4 ≤ (N.primeFactors.filter fun p => p ≠ q ∧ p % 3 = 1 ∧ 4 ≤ N.factorization p).card := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hm := three_mul_special_index_le h hq hodd
  have hv : 2 ≤ padicValNat 3 (N.factorization q + 1) := by
    rw [Nat.padicValNat_def]; exact (padicValNat_dvd_iff_le (by omega)).mp (by simpa using h9)
  have hsub : (N.primeFactors.filter fun p =>
        p ≠ q ∧ p % 3 = 1 ∧ 4 ≤ N.factorization p ∧ ¬ 3 ∣ N.factorization p + 1).card ≤
      (N.primeFactors.filter fun p => p ≠ q ∧ p % 3 = 1 ∧ 4 ≤ N.factorization p).card := by
    apply Finset.card_le_card
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  omega

/-- The witness step for `q = 13` and `a = 17`: Zsigmondy primes of orders `9` and `18`. -/
example : ∃ r₉ r₁₈ : ℕ, r₉.Prime ∧ r₉ ∣ σ 1 (13 ^ 17) ∧ orderOf (13 : ZMod r₉) = 9 ∧
    r₁₈.Prime ∧ r₁₈ ∣ σ 1 (13 ^ 17) ∧ orderOf (13 : ZMod r₁₈) = 18 := by
  obtain ⟨r, hr, hrd, hro, -⟩ :=
    exists_prime_dvd_sigma_orderOf_eq (p := 13) (e := 17) (d := 9) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  obtain ⟨s, hs, hsd, hso, -⟩ :=
    exists_prime_dvd_sigma_orderOf_eq (p := 13) (e := 17) (d := 18) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  exact ⟨r, s, hr, hrd, by exact_mod_cast hro, hs, hsd, by exact_mod_cast hso⟩

/-- The concrete witnesses: `1609669` (order `9`) and `19` (order `18`) divide `σ(13 ^ 17)`. -/
example : 1609669 ∣ σ 1 (13 ^ 17) ∧ 13 ^ 9 % 1609669 = 1 ∧ 13 ^ 3 % 1609669 ≠ 1 ∧
    19 ∣ σ 1 (13 ^ 17) ∧ 13 ^ 18 % 19 = 1 ∧ 13 ^ 9 % 19 ≠ 1 ∧ 13 ^ 6 % 19 ≠ 1 := by
  rw [sigma_one_apply_prime_pow (by norm_num)]
  norm_num [Finset.sum_range_succ]

end OddPerfect

#print axioms OddPerfect.two_mul_special_index_le_card
#print axioms OddPerfect.special_index_budget
#print axioms OddPerfect.special_index_witnesses
#print axioms OddPerfect.special_index_three
#print axioms OddPerfect.padicValNat_three_succ_le_sigma
#print axioms OddPerfect.three_mul_special_index_le
#print axioms OddPerfect.four_exceptions_of_three_sq_of_nine_dvd
