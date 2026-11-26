import OddPerfect.EulerIndexPairFrame
import OddPerfect.HalfSigmaTen
import OddPerfect.EulerIndexPairTenArith
import OddPerfect.NagellPrime
import OddPerfect.PureRows
import OddPerfect.SpecialPrime
import OddPerfect.SmallPrimes
import OddPerfect.OmegaSevenFinal

/-!
# Two prime Euler index: emitter exponent at least 12 in the branch `v = 0`

Restricted result; no published source was checked; novelty not verified.

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly the two prime factors
`r ≠ s`, oriented by a frame `PairFrame N q r s t u` with emitter row `σ(t ^ e) = q * u ^ v`
and return row `σ(u ^ f) = t ^ j`.

* `PairFrame.emitter_twelve`: in the branch `v = 0` (`σ(t ^ e) = q`) the exponent
  `e = v_t(N)` is at least `12`.
* `eulerIndex_pair_emitter_twelve`: the same for every member of the family, through
  `exists_pairFrame`.

The landed bound is `e ≥ 10` with `e + 1` prime, so only `e = 10` is excluded here. Proof
for `e = 10`: then `q + 1 = F(t) = t ^ 10 + ... + t + 2 = 2 u ^ d w ^ 2`, with `w` the product
over the outsiders. If `d = 0`, `σ(t ^ 10) + 1 = 2 w ^ 2`, excluded by
`sigma_prime_pow_ten_add_one_ne_two_mul_sq`. If `d > 0`, then `u ∣ F(t)` and `t ^ j ≡ 1 (mod u)`
with `j` odd, `j < 10`, so `u = 3`, or `(u, j) = (43, 7)`, or `(u, j) = (19, 9)`
(`pairTen_receiver_cases`). The case `u = 43` is closed modulo `43 ^ 3`
(`pairTen_fortythree_not`). For `u ∈ {3, 19}` no outsider row is a pure power of `u`, so every
outsider row is divisible by `t`, and the ledger `10 = j + Σ v_t(σ(p ^ g))` bounds the number
of outsiders by `10 - j`. There are at least four outsiders (`ω(N) ≥ 7`), which excludes
`j = 7, 9`; `j = 3` is excluded modulo `27` (`pairTen_three_mod27`). For `u = 3` and
`j ∈ {1, 5}` the primes `5, 7, 11, 13, 17` (and `19` when `j = 1`) do not divide `N`, and
`N` has at most `8` (resp. `12`) prime factors; the product `∏ p / (p - 1)` then stays below
`2`.

The family is not excluded by this. The odd perfect number conjecture is open, and nothing
here decides it.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace EulerIndexPairEmitterTwelve

/-- `σ(p ^ g) ≡ 1 (mod p)` for a prime `p` and `g ≥ 2`. -/
private lemma sigma_mod_self {p g : ℕ} (hp : p.Prime) (hg : 2 ≤ g) : σ 1 (p ^ g) % p = 1 := by
  have h3 : p ∣ p ^ 3 := dvd_pow_self p (by norm_num)
  rw [← Nat.mod_mod_of_dvd _ h3, sigma_prime_pow_mod_cube hp hg, Nat.mod_mod_of_dvd _ h3]
  have e : 1 + p + p ^ 2 = 1 + p * (1 + p) := by ring
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp.one_lt]

/-- `σ(p ^ 2) = p ^ 2 + p + 1` divides `σ(p ^ g)` for `g ∈ {2, 8}`. -/
private lemma phi3_dvd {p g : ℕ} (hp : p.Prime) (hg : g = 2 ∨ g = 8) :
    p ^ 2 + p + 1 ∣ σ 1 (p ^ g) := by
  rw [sigma_one_apply_prime_pow hp]
  rcases hg with rfl | rfl
  · exact ⟨1, by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; ring⟩
  · exact ⟨p ^ 6 + p ^ 3 + 1, by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; ring⟩

/-- No row of an odd prime with even exponent `g ≥ 2` is a pure power of `3` or of `19`. -/
private lemma no_pure {p g u y : ℕ} (hu : u = 3 ∨ u = 19) (hp : p.Prime) (hp2 : p ≠ 2)
    (hg : Even g) (hg2 : 2 ≤ g) (h : σ 1 (p ^ g) = u ^ y) : False := by
  rcases hu with rfl | rfl
  · have hm := receiver_mod_index_of_pure hp hp2 hg2 Nat.prime_three h
    rcases (show g = 2 ∨ 3 ≤ g by omega) with rfl | hg3
    · norm_num at hm
    · rw [Nat.mod_eq_of_lt (by omega)] at hm; omega
  · have hm := receiver_mod_index_of_pure hp hp2 hg2 (by norm_num) h
    have hg18 : g ≤ 18 := by
      by_contra hg'
      rw [Nat.mod_eq_of_lt (by omega)] at hm
      omega
    have hg28 : g = 2 ∨ g = 8 := by
      obtain ⟨k, rfl⟩ := hg
      have hk : k ≤ 9 := by omega
      interval_cases k <;> omega
    have hdiv := phi3_dvd hp hg28
    rw [h] at hdiv
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 19)).mp hdiv
    have hp3 : 2 ≤ p := hp.two_le
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · rw [pow_zero] at ha
      have : 0 ≤ p ^ 2 := Nat.zero_le _
      omega
    · have ha1 := nagellPrimePower p 19 a hp (by norm_num) ha0 ha
      rw [ha1, pow_one] at ha
      have hp4 : p ≤ 4 := by nlinarith
      interval_cases p <;> omega

/-- Periodicity of geometric sums modulo `m`. -/
private lemma geom_mod_period {p k m : ℕ} (h1 : p ^ k % m = 1)
    (h0 : (∑ i ∈ Finset.range k, p ^ i) % m = 0) (a r : ℕ) :
    (∑ i ∈ Finset.range (k * a + r), p ^ i) % m = (∑ i ∈ Finset.range r, p ^ i) % m := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show k * (a + 1) + r = k + (k * a + r) by ring, Finset.sum_range_add,
      Nat.add_mod (∑ i ∈ Finset.range k, p ^ i), h0, zero_add, Nat.mod_mod]
    simp_rw [pow_add]
    rw [← Finset.mul_sum, Nat.mul_mod, h1, one_mul, Nat.mod_mod, ih]

/-- A small prime `p` whose row is divisible by `3` has `p ≡ 1 (mod 3)` and `3 ∣ g + 1`. -/
private lemma mixed_index {p g : ℕ} (hp : p.Prime)
    (hl : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19) (hgev : Even g)
    (h3 : 3 ∣ σ 1 (p ^ g)) : 3 ∣ g + 1 ∧ (p = 7 ∨ p = 13 ∨ p = 19) := by
  rw [sigma_one_apply_prime_pow hp] at h3
  have hm := Nat.mod_eq_zero_of_dvd h3
  have key : p ^ 6 % 3 = 1 → (∑ i ∈ Finset.range 6, p ^ i) % 3 = 0 →
      (∑ i ∈ Finset.range ((g + 1) % 6), p ^ i) % 3 = 0 := fun h1 h0 => by
    rw [← geom_mod_period h1 h0 ((g + 1) / 6) ((g + 1) % 6), Nat.div_add_mod]; exact hm
  have hr : (g + 1) % 6 = 1 ∨ (g + 1) % 6 = 3 ∨ (g + 1) % 6 = 5 := by
    obtain ⟨k, rfl⟩ := hgev; omega
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (have hk := key (by norm_num) (by norm_num [Finset.sum_range_succ])
     rcases hr with hr | hr | hr <;> rw [hr] at hk <;>
       norm_num [Finset.sum_range_succ] at hk <;> exact ⟨by omega, by norm_num⟩)

end EulerIndexPairEmitterTwelve

open EulerIndexPairEmitterTwelve

variable {N q m r s t u : ℕ}

namespace PairFrame

set_option maxHeartbeats 1600000 in
/-- **Emitter exponent at least 12 in the branch `v = 0`.** For a frame of the two prime Euler
index family, if `σ(t ^ e) = q` (`e = v_t(N)`), then `e ≥ 12`. Restricted result; no published
source was checked; novelty not verified. This case is not excluded here. -/
theorem emitter_twelve (F : PairFrame N q r s t u) (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s})
    (hv0 : σ 1 (t ^ N.factorization t) = q) : 12 ≤ N.factorization t := by
  obtain ⟨ht, ht2, v, j, -, hj0, hjo, hB, hje, hprime, h10, -⟩ :=
    F.emitter_ten_all h hq hN hqm hr hs hrs hJ
  by_contra hlt
  have he : N.factorization t = 10 := by
    rcases (show N.factorization t = 10 ∨ N.factorization t = 11 by omega) with h1 | h1
    · exact h1
    · rw [h1] at hprime; norm_num at hprime
  have hj10 : j < 10 := by omega
  obtain ⟨-, -, -, -, hf1, -, -, -, -, hout, d, hd⟩ := F.cofactor h hq hN hqm hr hs hrs hJ
  obtain ⟨-, -, -, j', -, -, hB', hled, -, -, -, -⟩ := F.t_count h hq hN hqm hr hs hrs hJ
  rw [F.j_eq hB' hB] at hled
  obtain ⟨-, -, -, -, -, ht43⟩ := F.emitter_ge h hq hN hqm hr hs hrs hJ
  have ht43' : 43 ≤ t := by rcases ht43 with ⟨h1, -⟩ | h1 <;> omega
  have hu := F.u_prime
  -- `q + 1 = F(t)`
  have hs10 : σ 1 (t ^ 10) = q := by rw [← he]; exact hv0
  have hqF : q + 1 =
      t ^ 10 + t ^ 9 + t ^ 8 + t ^ 7 + t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 + t ^ 2 + t + 2 := by
    rw [← hs10, sigma_one_apply_prime_pow ht]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
    ring
  have hq20 : 20 ≤ q := by
    have : 59049 ≤ t ^ 10 :=
      calc (59049 : ℕ) = 3 ^ 10 := by norm_num
        _ ≤ t ^ 10 := Nat.pow_le_pow_left (by omega) 10
    omega
  -- the receiver `u`
  have hfpos : N.factorization u ≠ 0 := fun h0 => by rw [h0] at hf1; norm_num at hf1
  have huN : u ∣ N := Nat.dvd_of_factorization_pos hfpos
  have hu2 : u ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ huN)
  have hf2 : 2 ≤ N.factorization u := by
    by_contra hf
    have hf' : N.factorization u = 1 := by omega
    rw [hf', sigma_one_apply_prime_pow hu] at hB
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one] at hB
    have hu1 : u % 2 = 1 := Nat.odd_iff.mp (hu.odd_of_ne_two hu2)
    have h2t : 2 ∣ t ^ j := Nat.dvd_of_mod_eq_zero (by omega)
    exact ht2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two ht).mp
      (Nat.prime_two.dvd_of_dvd_pow h2t)).symm
  have htu : t ^ j % u = 1 := by rw [← hB]; exact sigma_mod_self hu hf2
  -- outsiders
  have hmem : ∀ x, x ∈ ({t, u} : Finset ℕ) ↔ x ∈ ({r, s} : Finset ℕ) := fun x => by rw [F.pair]
  have hOiff : ∀ p, p ∈ N.primeFactors \ {q, r, s} ↔
      p ∈ N.primeFactors ∧ p ≠ q ∧ p ≠ t ∧ p ≠ u := by
    intro p
    have := hmem p
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at this ⊢
    tauto
  have hq1 : N.factorization q = 1 := by
    have hm0 : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
    rw [hN, Nat.factorization_mul hq.ne_zero (pow_ne_zero 2 hm0), Finsupp.add_apply,
      Nat.factorization_pow, hq.factorization_self, Finsupp.smul_apply,
      Nat.factorization_eq_zero_of_not_dvd hqm]
    simp
  have hgev : ∀ p ∈ N.primeFactors, p ≠ q →
      Even (N.factorization p) ∧ 2 ≤ N.factorization p := by
    intro p hpN hpq
    have hpp := Nat.prime_of_mem_primeFactors hpN
    have hev := even_factorization_of_ne h hq (by rw [hq1]; exact odd_one) hpp hpq
    have h0 := hpp.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hpN)
    obtain ⟨k, hk⟩ := hev
    exact ⟨⟨k, hk⟩, by omega⟩
  have hodd2 : ∀ p ∈ N.primeFactors, p ≠ 2 := fun p hp h2 =>
    h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hp)
  have hcardO : N.primeFactors.card ≤ (N.primeFactors \ {q, r, s}).card + 3 := by
    have h1 : N.primeFactors.card ≤
        (N.primeFactors \ {q, r, s}).card + ({q, r, s} : Finset ℕ).card :=
      Finset.card_le_card_sdiff_add_card
    have h2 : ({q, r, s} : Finset ℕ).card ≤ 3 := Finset.card_le_three
    omega
  have hcard7 := seven_le_card_primeFactors h
  -- every outsider row is divisible by `t` when `u ∈ {3, 19}`
  have hfeeds : u = 3 ∨ u = 19 → ∀ p ∈ N.primeFactors \ {q, r, s},
      1 ≤ (σ 1 (p ^ N.factorization p)).factorization t := by
    intro hu319 p hpO
    obtain ⟨hpN, hpq, hpt, hpu⟩ := (hOiff p).mp hpO
    have hpp := Nat.prime_of_mem_primeFactors hpN
    obtain ⟨hg, hg2⟩ := hgev p hpN hpq
    obtain ⟨⟨x, y, hxy⟩, -, -⟩ := hout p hpN hpq hpt hpu
    have hs0 : σ 1 (p ^ N.factorization p) ≠ 0 := by
      rw [hxy]; exact mul_ne_zero (pow_ne_zero _ ht.ne_zero) (pow_ne_zero _ hu.ne_zero)
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · rw [pow_zero, one_mul] at hxy
      exact (no_pure hu319 hpp (hodd2 p hpN) hg hg2 hxy).elim
    · have htd : t ∣ σ 1 (p ^ N.factorization p) := by
        rw [hxy]; exact Dvd.dvd.mul_right (dvd_pow_self t hx.ne') _
      exact (ht.dvd_iff_one_le_factorization hs0).mp htd
  have hcount : u = 3 ∨ u = 19 → (N.primeFactors \ {q, r, s}).card + j ≤ 10 := by
    intro hu319
    have := Finset.card_nsmul_le_sum _ _ 1 (hfeeds hu319)
    simp only [smul_eq_mul, mul_one] at this
    omega
  -- the case `d = 0`
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · rw [pow_zero, mul_one] at hd
    exact sigma_prime_pow_ten_add_one_ne_two_mul_sq ht ht2 (by rw [hs10]; exact hd)
  have hFu :
      u ∣ t ^ 10 + t ^ 9 + t ^ 8 + t ^ 7 + t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 + t ^ 2 + t + 2 := by
    rw [← hqF, hd]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self u hdpos.ne') 2) _
  rcases pairTen_receiver_cases hu hu2 hFu htu hjo hj10 with hu3 | ⟨rfl, hu43⟩ | ⟨rfl, hu19⟩
  rotate_left
  · -- `u = 43`, `j = 7`
    subst hu43
    have ht7 : t ^ 7 % 79507 = 1893 := by
      rw [← hB, show (79507 : ℕ) = 43 ^ 3 by norm_num,
        sigma_prime_pow_mod_cube (by norm_num : Nat.Prime 43) hf2] <;> norm_num
    have hW : ¬ 43 ∣ ∏ p ∈ N.primeFactors \ {q, r, s}, p ^ (N.factorization p / 2) := by
      intro hdvd
      obtain ⟨p, hpO, hp⟩ := ((Nat.prime_iff.mp hu).dvd_finsetProd_iff _).mp hdvd
      have hpp := Nat.prime_of_mem_primeFactors ((hOiff p).mp hpO).1
      have := (Nat.prime_dvd_prime_iff_eq hu hpp).mp (hu.dvd_of_dvd_pow hp)
      exact ((hOiff p).mp hpO).2.2.2 this.symm
    exact pairTen_fortythree_not ht7 hFu hW (by rw [← hqF]; exact hd)
  · -- `u = 19`, `j = 9`
    have := hcount (Or.inr hu19)
    omega
  -- `u = 3`
  have ht27 : t ^ j % 27 = 13 := by
    subst hu3
    rw [← hB, show (27 : ℕ) = 3 ^ 3 by norm_num, sigma_prime_pow_mod_cube Nat.prime_three hf2]
      <;> norm_num
  have hcnt := hcount (Or.inl hu3)
  -- small primes do not divide `N`, except possibly `19` with `t ≡ 17 (mod 19)`
  have hexcl : ∀ p ∈ N.primeFactors,
      (p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19) → p = 19 ∧ t % 19 = 17 := by
    intro p hpN hpl
    have hp19 : p ≤ 19 := by omega
    have hpq : p ≠ q := by omega
    have hpt : p ≠ t := by omega
    have hpu : p ≠ u := by omega
    have hpp := Nat.prime_of_mem_primeFactors hpN
    obtain ⟨hg, hg2⟩ := hgev p hpN hpq
    obtain ⟨⟨x, y, hxy⟩, hpd, hgl⟩ := hout p hpN hpq hpt hpu
    have hpF : p ∣ t ^ 10 + t ^ 9 + t ^ 8 + t ^ 7 + t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 + t ^ 2 + t +
        2 := by
      have hg0 : N.factorization p ≠ 0 := by omega
      have h1 : p ∣ p ^ N.factorization p := dvd_pow_self p hg0
      rw [← hqF]
      exact Nat.dvd_trans h1 hpd
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · rw [pow_zero, one_mul] at hxy
      exact (no_pure (Or.inl hu3) hpp (hodd2 p hpN) hg hg2 hxy).elim
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · rw [pow_zero, mul_one] at hxy
      have hxo : Odd x := (odd_weight_or_three_pow_four hpp (hodd2 p hpN) hg (by omega) ht
        hxy).resolve_right (fun h' => hpu (h'.1.trans hu3.symm))
      have htx : t ^ x % p = 1 := by rw [← hxy]; exact sigma_mod_self hpp hg2
      exact pairTen_small_prime hpl hxo htx hpF
    exfalso
    have h3 : 3 ∣ σ 1 (p ^ N.factorization p) := by
      rw [hxy, hu3]; exact Dvd.dvd.mul_left (dvd_pow_self 3 hy.ne') _
    obtain ⟨h3g, hp71319⟩ := mixed_index hpp hpl hg h3
    have hg28 : N.factorization p = 2 ∨ N.factorization p = 8 := by
      rcases hgl with hgp | ⟨P, hP, hPe⟩
      · rcases hgp.eq_one_or_self_of_dvd 3 h3g with h1 | h1 <;> omega
      · rw [hPe] at h3g
        have h3P := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hP).mp
          (Nat.prime_three.dvd_of_dvd_pow h3g)
        subst h3P
        norm_num at hPe
        omega
    have hdiv := phi3_dvd hpp hg28
    rw [hxy, hu3] at hdiv
    -- the cofactor `c` of `p ^ 2 + p + 1 = 3 c` equals `t`
    have hc : ∀ c : ℕ, c.Prime → c ≠ 3 → c ∣ t ^ x * 3 ^ y → c = t := fun c hc hc3 hct =>
      (Nat.prime_dvd_prime_iff_eq hc ht).mp (hc.dvd_of_dvd_pow
        ((Nat.Coprime.pow_right y
          ((Nat.coprime_primes hc Nat.prime_three).mpr hc3)).dvd_of_dvd_mul_right hct))
    rcases hp71319 with rfl | rfl | rfl
    · have := hc 19 (by norm_num) (by norm_num)
        ((show 19 ∣ 7 ^ 2 + 7 + 1 by norm_num).trans hdiv)
      omega
    · have := hc 61 (by norm_num) (by norm_num)
        ((show 61 ∣ 13 ^ 2 + 13 + 1 by norm_num).trans hdiv)
      subst this
      norm_num at hpF
    · have := hc 127 (by norm_num) (by norm_num)
        ((show 127 ∣ 19 ^ 2 + 19 + 1 by norm_num).trans hdiv)
      subst this
      norm_num at hpF
  -- abundancy envelope
  have habund : ∀ (T : Finset ℕ) (M : ℕ), (∀ x ∈ T, 2 ≤ x ∧ x ≤ M) →
      (∀ p ∈ N.primeFactors, p < M → p ∈ T) → N.primeFactors.card ≤ T.card →
      ∏ x ∈ T, (x : ℚ) / (x - 1) ≤ 2 → False := by
    intro T M hT hcov hk hval
    have := two_lt_prod_of_card_le h (fun x hx => (hT x hx).1) (fun p hp hpT x hx => by
      by_contra hlt'
      exact hpT (hcov p hp (by have := (hT x hx).2; omega))) hk
    linarith
  rcases pairTen_three_mod27 ht27 hjo hj10 with ⟨rfl, ht13, -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩
  · -- `j = 1`: `t = σ(3 ^ f)`, so `2 t + 1 = 3 ^ (f + 1)`
    have hgeo : ∀ n, 2 * ∑ i ∈ Finset.range n, 3 ^ i + 1 = 3 ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega
    have h2t : 2 * t + 1 = 3 ^ (N.factorization u + 1) := by
      rw [pow_one] at hB
      subst hu3
      rw [← hB, sigma_one_apply_prime_pow Nat.prime_three, hgeo]
    have hfo : Odd (N.factorization u + 1) :=
      hf1.eq_two_or_odd'.resolve_left (by omega)
    refine habund {3, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67} 67 (by decide) ?_
      (by rw [show ({3, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67} : Finset ℕ).card = 12
        by decide]; omega) (by norm_num [Finset.prod_insert])
    intro p hp hlt'
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp2 := hodd2 p hp
    have hsm : ¬ (p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19) := fun hl => by
      obtain ⟨-, h17⟩ := hexcl p hp hl
      exact pairTen_nineteen_not h17 hfo h2t
    interval_cases p <;> first | decide | exact absurd rfl hp2 | exact (hsm (by decide)).elim |
      (exfalso; norm_num at hpp; done)
  · -- `j = 5`
    refine habund {3, 19, 23, 29, 31, 37, 41, 43} 43 (by decide) ?_
      (by rw [show ({3, 19, 23, 29, 31, 37, 41, 43} : Finset ℕ).card = 8 by decide]; omega)
      (by norm_num [Finset.prod_insert])
    intro p hp hlt'
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp2 := hodd2 p hp
    have hsm : ¬ (p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17) := fun hl => by
      have := hexcl p hp (by omega)
      omega
    interval_cases p <;> first | decide | exact absurd rfl hp2 | exact (hsm (by decide)).elim |
      (exfalso; norm_num at hpp; done)
  · -- `j = 7`
    omega

end PairFrame

/-- **Family form.** In the two prime Euler index family, the emitter `t` of the frame satisfies
`v_t(N) ≥ 12` in the branch `σ(t ^ v_t(N)) = q`. Restricted result; no published source was
checked; novelty not verified. This case is not excluded here. -/
theorem eulerIndex_pair_emitter_twelve (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, PairFrame N q r s t u ∧
      (σ 1 (t ^ N.factorization t) = q → 12 ≤ N.factorization t) := by
  obtain ⟨t, u, F⟩ := exists_pairFrame h hq hN hqm hr hs hrs hJ
  exact ⟨t, u, F, F.emitter_twelve h hq hN hqm hr hs hrs hJ⟩

end OddPerfect

#print axioms OddPerfect.PairFrame.emitter_twelve
#print axioms OddPerfect.eulerIndex_pair_emitter_twelve
