import OddPerfect.Valuation
import OddPerfect.SpecialPrime
import OddPerfect.Reciprocity

/-!
# Prime component divisor sums need five distinct ordinary exponents

Let `N` be an odd perfect number with special prime `q` (the prime of odd exponent). Call the
other prime factors ordinary. If the divisor sum `σ(p ^ e_p)` of every ordinary component is
prime, then at least five distinct values occur among the ordinary exponents `e_p`.

The argument reads the valuation ledger `v_t(N) = ∑_p v_t(σ(p ^ e_p))`. Each ordinary
component then sends exactly one unit, to the prime `σ(p ^ e_p)`. For a fixed exponent the
map `p ↦ σ(p ^ e)` is injective, and an ordinary prime `s` never receives from an ordinary
prime of its own exponent, so a receiver gets at most `k` ordinary units (at most `k - 1` if
it is ordinary), where `k` is the number of distinct ordinary exponents. With `k ≤ 4` this
forces the special exponent to be `1`, then a chain `p → s → q` with `e_p = e_s = 2`, which
contradicts the same exponent rule.

Whether this result is new was not verified against the literature.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- For a fixed positive exponent `e`, `σ(p ^ e)` is strictly increasing in the prime `p`. -/
theorem sigma_prime_pow_lt_of_lt {p p' e : ℕ} (hp : p.Prime) (hp' : p'.Prime) (he : e ≠ 0)
    (hlt : p < p') : σ 1 (p ^ e) < σ 1 (p' ^ e) := by
  rw [sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hp']
  exact Finset.sum_lt_sum (fun i _ => Nat.pow_le_pow_left hlt.le i)
    ⟨e, Finset.mem_range.mpr (by omega), Nat.pow_lt_pow_left hlt he⟩

/-- For a fixed positive exponent `e`, the prime `p` is determined by `σ(p ^ e)`. -/
theorem eq_of_sigma_prime_pow_eq {p p' e : ℕ} (hp : p.Prime) (hp' : p'.Prime) (he : e ≠ 0)
    (h : σ 1 (p ^ e) = σ 1 (p' ^ e)) : p = p' := by
  rcases lt_trichotomy p p' with hlt | heq | hgt
  · exact absurd h (sigma_prime_pow_lt_of_lt hp hp' he hlt).ne
  · exact heq
  · exact absurd h (sigma_prime_pow_lt_of_lt hp' hp he hgt).ne'

/-- `p < σ(p ^ e)` for a prime `p` and `e ≥ 1`. -/
theorem lt_sigma_prime_pow {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) : p < σ 1 (p ^ e) := by
  rw [sigma_one_apply_prime_pow hp]
  have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (e + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_range]
    omega
  have := Finset.sum_le_sum_of_subset (f := fun k => p ^ k) hsub
  rw [Finset.sum_pair (by norm_num)] at this
  simp only [pow_zero, pow_one] at this
  omega

/-- `e + 1 < σ(s ^ e)` for a prime `s` and `e ≥ 1`. -/
theorem succ_lt_sigma_prime_pow {s e : ℕ} (hs : s.Prime) (he : e ≠ 0) :
    e + 1 < σ 1 (s ^ e) := by
  rw [sigma_one_apply_prime_pow hs]
  have := Finset.sum_lt_sum (s := Finset.range (e + 1)) (f := fun _ => 1) (g := fun k => s ^ k)
    (fun i _ => Nat.one_le_pow _ _ hs.pos)
    ⟨e, Finset.mem_range.mpr (by omega), Nat.one_lt_pow he hs.one_lt⟩
  simpa using this

/-- Same exponent rule: if `σ(p ^ e) = s` for primes `p`, `s` and `e ≥ 1`, then `σ(s ^ e)` is
not prime. Indeed the order of `p` modulo `s` is `e + 1`, so `s ≡ 1 (mod e + 1)` and
`e + 1 ∣ σ(s ^ e)`, while `σ(s ^ e) > e + 1`. -/
theorem not_prime_sigma_of_sigma_eq {p s e : ℕ} (hp : p.Prime) (hs : s.Prime) (he : e ≠ 0)
    (hps : σ 1 (p ^ e) = s) : ¬ (σ 1 (s ^ e)).Prime := by
  intro hP
  have : Fact s.Prime := ⟨hs⟩
  have hlt : p < s := hps ▸ lt_sigma_prime_pow hp he
  have hsd : s ∣ σ 1 (p ^ e) := hps ▸ dvd_refl s
  rcases (prime_dvd_sigma_prime_pow hp hs hsd).2 with ⟨h1, -⟩ | ⟨h1, hd, hd'⟩
  · rw [Nat.mod_eq_of_lt hlt] at h1
    exact hp.one_lt.ne' h1
  · have hord : orderOf (p : ZMod s) = e + 1 := by
      by_contra hne
      set d := orderOf (p : ZMod s) with hdd
      have hdlt : d < e + 1 := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hd) hne
      have hpow : (p : ZMod s) ^ d = 1 := pow_orderOf_eq_one _
      have hdvd : s ∣ p ^ d - 1 := by
        rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hp.pos)]
        push_cast
        rw [hpow, sub_self]
      have hmul := sigma_prime_pow_mul_pred hp (d - 1)
      rw [show d - 1 + 1 = d by omega] at hmul
      rw [← hmul] at hdvd
      have hp1 : 0 < p - 1 := by have := hp.one_lt; omega
      rcases (Nat.Prime.dvd_mul hs).mp hdvd with h | h
      · have hpos : 0 < σ 1 (p ^ (d - 1)) := sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)
        have hle := Nat.le_of_dvd hpos h
        have h1 : p ^ d - 1 < p ^ (e + 1) - 1 := by
          have := Nat.pow_lt_pow_right hp.one_lt hdlt
          have := Nat.one_le_pow d p hp.pos
          omega
        have h2 := sigma_prime_pow_mul_pred hp e
        rw [hps] at h2
        have hlt2 : σ 1 (p ^ (d - 1)) * (p - 1) < s * (p - 1) := by
          rw [hmul, h2]
          exact h1
        have := Nat.lt_of_mul_lt_mul_right hlt2
        omega
      · have := Nat.le_of_dvd hp1 h
        omega
    rw [hord] at hd'
    have hmod : s % (e + 1) = 1 := by
      have := (Nat.modEq_iff_dvd' hs.one_lt.le).mpr hd'
      rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega : 1 < e + 1)] at this
      exact this.symm
    have hdvd : e + 1 ∣ σ 1 (s ^ e) := by
      have hc : ((s : ℕ) : ZMod (e + 1)) = 1 := by
        have := (ZMod.natCast_eq_natCast_iff' s 1 (e + 1)).mpr
          (by rw [hmod, Nat.mod_eq_of_lt (by omega : 1 < e + 1)])
        simpa using this
      rw [← ZMod.natCast_eq_zero_iff, sigma_one_apply_prime_pow hs]
      push_cast
      simp only [hc, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      exact_mod_cast ZMod.natCast_self (e + 1)
    rcases (Nat.dvd_prime hP).mp hdvd with h | h
    · omega
    · have := succ_lt_sigma_prime_pow hs he
      omega

/-- The ordinary senders into `t`: the ordinary prime factors `p` (those other than `q`)
with `σ(p ^ e_p) = t`. -/
def primeSenders (N q t : ℕ) : Finset ℕ :=
  (N.primeFactors.erase q).filter fun p => σ 1 (p ^ N.factorization p) = t

/-- The ledger when every ordinary component divisor sum is prime: for an odd prime `t`,
`v_t(N)` is the weight sent by the special component plus the number of ordinary `p` with
`σ(p ^ e_p) = t`. -/
theorem factorization_eq_add_card_primeSenders {N q : ℕ} (h : OddPerfect N)
    (hqN : q ∈ N.primeFactors)
    (hP : ∀ p ∈ N.primeFactors, p ≠ q → (σ 1 (p ^ N.factorization p)).Prime)
    {t : ℕ} (ht : t.Prime) (ht2 : t ≠ 2) :
    N.factorization t = sigmaWeight N q t + (primeSenders N q t).card := by
  rw [← sigmaWeight_sum_eq h.perfect ht ht2,
    ← Finset.add_sum_erase _ (fun p => sigmaWeight N p t) hqN, primeSenders, Finset.card_filter]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  have hPp := hP p (Finset.mem_erase.mp hp).2 (Finset.mem_erase.mp hp).1
  rw [sigmaWeight, hPp.factorization, Finsupp.single_apply]

/-- Sender count: the ordinary senders into `t` have pairwise distinct exponents, so there are
at most as many as distinct ordinary exponents; if `t` is itself ordinary, none of them has the
exponent of `t`, so there is at least one fewer. -/
theorem card_primeSenders_le {N q : ℕ}
    (hP : ∀ p ∈ N.primeFactors, p ≠ q → (σ 1 (p ^ N.factorization p)).Prime) (t : ℕ) :
    (primeSenders N q t).card ≤ ((N.primeFactors.erase q).image N.factorization).card ∧
      (t ∈ N.primeFactors.erase q →
        (primeSenders N q t).card + 1 ≤ ((N.primeFactors.erase q).image N.factorization).card) := by
  have hmem : ∀ p ∈ primeSenders N q t, p.Prime ∧ N.factorization p ≠ 0 ∧
      σ 1 (p ^ N.factorization p) = t := by
    intro p hp
    rw [primeSenders, Finset.mem_filter] at hp
    have hpN := (Finset.mem_erase.mp hp.1).2
    exact ⟨Nat.prime_of_mem_primeFactors hpN,
      Finsupp.mem_support_iff.mp (Nat.support_factorization N ▸ hpN), hp.2⟩
  have hinj : Set.InjOn N.factorization (primeSenders N q t) := by
    intro p hp p' hp' hpp
    obtain ⟨hpp1, hpe, hpt⟩ := hmem p hp
    obtain ⟨hpp1', -, hpt'⟩ := hmem p' hp'
    refine eq_of_sigma_prime_pow_eq hpp1 hpp1' hpe ?_
    have := hpt'
    rw [← hpp] at this
    rw [hpt, this]
  have hcard := Finset.card_image_of_injOn hinj
  have hsub : (primeSenders N q t).image N.factorization ⊆
      (N.primeFactors.erase q).image N.factorization :=
    Finset.image_subset_image (Finset.filter_subset _ _)
  refine ⟨hcard ▸ Finset.card_le_card hsub, fun ht => ?_⟩
  have htE : N.factorization t ∈ (N.primeFactors.erase q).image N.factorization :=
    Finset.mem_image_of_mem _ ht
  have hsub' : (primeSenders N q t).image N.factorization ⊆
      ((N.primeFactors.erase q).image N.factorization).erase (N.factorization t) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_erase.mpr ⟨fun heq => ?_, hsub hx⟩
    obtain ⟨hpp1, hpe, hpt⟩ := hmem p hp
    have htN := (Finset.mem_erase.mp ht)
    have hPt := hP t htN.2 htN.1
    rw [← heq] at hPt
    exact not_prime_sigma_of_sigma_eq hpp1 (Nat.prime_of_mem_primeFactors htN.2) hpe hpt hPt
  have := Finset.card_le_card hsub'
  rw [Finset.card_erase_of_mem htE, hcard] at this
  have := Finset.card_pos.mpr ⟨_, htE⟩
  omega

/-- **Prime component divisor sums need five exponents.** Let `N` be an odd perfect number and
`q` its special prime (the prime of odd exponent). If `σ(p ^ e_p)` is prime for every prime
factor `p ≠ q`, then at least five distinct values occur among the exponents `e_p`, `p ≠ q`.
The primality of all these divisor sums is a case hypothesis, not known to hold.
Whether this result is new was not verified against the literature. -/
theorem five_le_card_exponents_of_sigma_prime {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hP : ∀ p ∈ N.primeFactors, p ≠ q → (σ 1 (p ^ N.factorization p)).Prime) :
    5 ≤ ((N.primeFactors.erase q).image N.factorization).card := by
  by_contra hk
  push Not at hk
  have hqN : q ∈ N.primeFactors :=
    Nat.support_factorization N ▸ Finsupp.mem_support_iff.mpr (by rintro h0; simp [h0] at hodd)
  have hodd2 : ∀ r ∈ N.primeFactors, r ≠ 2 := fun r hr h2 =>
    h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hr)
  have hq2 := hodd2 q hqN
  have hled := fun {t : ℕ} (ht : t.Prime) (ht2 : t ≠ 2) =>
    factorization_eq_add_card_primeSenders h hqN hP ht ht2
  have hcnt := card_primeSenders_le hP
  -- the special exponent is `1`
  have hledq := hled hq hq2
  rw [sigmaWeight_self hq, zero_add] at hledq
  have ha4 := (special_mod_four h hq hodd).2
  have ha1 : N.factorization q = 1 := by
    have := (hcnt q).1
    omega
  have hσq : σ 1 (q ^ N.factorization q) = q + 1 := by
    rw [ha1, sigma_one_apply_prime_pow hq]
    simp [Finset.sum_range_succ, add_comm]
  have hwq : ∀ r : ℕ, ¬ r ∣ q + 1 → sigmaWeight N q r = 0 := fun r hr => by
    rw [sigmaWeight, hσq]
    exact Nat.factorization_eq_zero_of_not_dvd hr
  -- an ordinary sender `s` into `q`
  obtain ⟨s, hs⟩ := Finset.card_pos.mp (show 0 < (primeSenders N q q).card by omega)
  rw [primeSenders, Finset.mem_filter] at hs
  obtain ⟨hsO, hσs⟩ := hs
  have hsN := (Finset.mem_erase.mp hsO).2
  have hsq : s ≠ q := (Finset.mem_erase.mp hsO).1
  have hs' := Nat.prime_of_mem_primeFactors hsN
  have hs3 : 3 ≤ s := by have := hs'.two_le; have := hodd2 s hsN; omega
  have hsdvd : ¬ s ∣ q + 1 := by
    have hqs := sigma_prime_pow_mod_self hs' (N.factorization s)
    rw [hσs] at hqs
    have : (q + 1) % s = 2 := by
      rw [Nat.add_mod, hqs, Nat.mod_eq_of_lt (by omega : 1 < s),
        Nat.mod_eq_of_lt (by omega : 2 < s)]
    rw [Nat.dvd_iff_mod_eq_zero, this]
    omega
  have hes : N.factorization s = 2 := by
    have hl := hled hs' (hodd2 s hsN)
    rw [hwq s hsdvd, zero_add] at hl
    have := (hcnt s).2 hsO
    have hev := even_factorization_of_ne h hq hodd hs' hsq
    have hne : N.factorization s ≠ 0 :=
      Finsupp.mem_support_iff.mp (Nat.support_factorization N ▸ hsN)
    obtain ⟨j, hj⟩ := hev
    omega
  -- an ordinary sender `p` into `s`
  have hcs : 0 < (primeSenders N q s).card := by
    have hl := hled hs' (hodd2 s hsN)
    rw [hwq s hsdvd, zero_add] at hl
    omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcs
  rw [primeSenders, Finset.mem_filter] at hp
  obtain ⟨hpO, hσp⟩ := hp
  have hpN := (Finset.mem_erase.mp hpO).2
  have hpq : p ≠ q := (Finset.mem_erase.mp hpO).1
  have hp' := Nat.prime_of_mem_primeFactors hpN
  have hpdvd : ¬ p ∣ q + 1 := by
    have hsp := sigma_prime_pow_mod_self hp' (N.factorization p)
    rw [hσp] at hsp
    obtain ⟨c, hc⟩ : ∃ c, s = p * c + 1 := ⟨s / p, by have := Nat.div_add_mod s p; omega⟩
    have hq' : q + 1 = p * (p * c ^ 2 + 3 * c) + 4 := by
      rw [← hσs, hes, sigma_one_apply_prime_pow hs', hc]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      ring
    intro hd
    rw [hq'] at hd
    have h4 : p ∣ 2 ^ 2 := (Nat.dvd_add_right (dvd_mul_right p _)).mp hd
    exact hodd2 p hpN ((Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).mp
      (hp'.dvd_of_dvd_pow h4))
  have hep : N.factorization p = 2 := by
    have hl := hled hp' (hodd2 p hpN)
    rw [hwq p hpdvd, zero_add] at hl
    have := (hcnt p).2 hpO
    have hev := even_factorization_of_ne h hq hodd hp' hpq
    have hne : N.factorization p ≠ 0 :=
      Finsupp.mem_support_iff.mp (Nat.support_factorization N ▸ hpN)
    obtain ⟨j, hj⟩ := hev
    omega
  rw [hep] at hσp
  have hPs := hP s hsN hsq
  rw [hes] at hPs
  exact not_prime_sigma_of_sigma_eq hp' hs' (by norm_num) hσp hPs

end OddPerfect

#print axioms OddPerfect.sigma_prime_pow_lt_of_lt
#print axioms OddPerfect.eq_of_sigma_prime_pow_eq
#print axioms OddPerfect.lt_sigma_prime_pow
#print axioms OddPerfect.succ_lt_sigma_prime_pow
#print axioms OddPerfect.not_prime_sigma_of_sigma_eq
#print axioms OddPerfect.factorization_eq_add_card_primeSenders
#print axioms OddPerfect.card_primeSenders_le
#print axioms OddPerfect.five_le_card_exponents_of_sigma_prime
