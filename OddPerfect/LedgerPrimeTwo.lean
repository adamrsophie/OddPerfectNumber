import OddPerfect.LedgerPrime
import OddPerfect.EulerIndexPrimePower
import OddPerfect.Counting

/-!
# Prime component divisor sums: eleven exponents and a forced collision

Let `N` be an odd perfect number with special prime `q` (the prime of odd exponent `a`), and
call the other prime factors ordinary. This module works under the case hypothesis that the
full divisor sum `σ(p ^ e_p)` of every ordinary component is prime. That hypothesis is not
known to hold for a hypothetical odd perfect number; every result here is conditional on it.

Write `k` for the number of distinct ordinary exponent values and `S(t)` for the set of
ordinary primes `p` with `σ(p ^ e_p) = t`. The ledger of `OddPerfect.LedgerPrime` gives
`e_t = v_t(σ(q ^ a)) + |S(t)|`, `|S(t)| ≤ k`, and `|S(t)| ≤ k - 1` for ordinary `t`.

* `eleven_le_card_exponents_of_sigma_prime`: at least eleven distinct ordinary exponent values
  occur (`OddPerfect.LedgerPrime` proves five).
* `exists_prime_sigma_collision`: with no bound on `k`, there is an ordinary sender `s` into
  `q` that receives nothing from the special component, has even exponent at least `2`, and
  receives from two distinct ordinary primes of distinct exponents.
* `prime_sigma_counting`: `ω N ≥ 12`, `Ω N ≥ 185` and `Ω N ≥ 2 ω N + 161`.

Whether these results are in the literature was not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.omega ArithmeticFunction.Omega

namespace OddPerfect

/-- If `x` is a prime with `x ≡ 1 (mod m)`, then `σ(x ^ e) ≡ e + 1 (mod m)`. -/
theorem sigma_prime_pow_modEq_succ {x m : ℕ} (hx : x.Prime) (h : x ≡ 1 [MOD m]) (e : ℕ) :
    σ 1 (x ^ e) ≡ e + 1 [MOD m] := by
  rw [← ZMod.natCast_eq_natCast_iff] at h ⊢
  rw [sigma_one_apply_prime_pow hx]
  push_cast at h ⊢
  simp [h]

/-- If `σ(p ^ e) = t` for a prime `p`, then `t ≡ 1 (mod p)`. -/
theorem modEq_one_of_sigma_prime_pow_eq {p e t : ℕ} (hp : p.Prime) (h : σ 1 (p ^ e) = t) :
    t ≡ 1 [MOD p] := by
  have := sigma_prime_pow_mod_self hp e
  rw [h] at this
  rw [Nat.ModEq, this, Nat.mod_eq_of_lt hp.one_lt]

private theorem lp2_spec {N q t p : ℕ} (hp : p ∈ primeSenders N q t) :
    p ∈ N.primeFactors ∧ p ≠ q ∧ p.Prime ∧ N.factorization p ≠ 0 ∧
      σ 1 (p ^ N.factorization p) = t := by
  rw [primeSenders, Finset.mem_filter, Finset.mem_erase] at hp
  exact ⟨hp.1.2, hp.1.1, Nat.prime_of_mem_primeFactors hp.1.2,
    Finsupp.mem_support_iff.mp (Nat.support_factorization N ▸ hp.1.2), hp.2⟩

private theorem lp2_qN {N q : ℕ} (hodd : Odd (N.factorization q)) : q ∈ N.primeFactors :=
  Nat.support_factorization N ▸ Finsupp.mem_support_iff.mpr (by rintro h0; simp [h0] at hodd)

private theorem lp2_injOn {N q t : ℕ} : Set.InjOn N.factorization (primeSenders N q t) := by
  intro p hp p' hp' hpp
  obtain ⟨-, -, hp1, hpe, hpt⟩ := lp2_spec hp
  obtain ⟨-, -, hp1', -, hpt'⟩ := lp2_spec hp'
  refine eq_of_sigma_prime_pow_eq hp1 hp1' hpe ?_
  rw [hpt, hpp, hpt']

private theorem lp2_card_le {N q t : ℕ} (F E : Finset ℕ) (hF : F ⊆ primeSenders N q t)
    (hE : ∀ p ∈ F, N.factorization p ∈ E) : F.card ≤ E.card := by
  rw [← Finset.card_image_of_injOn (lp2_injOn.mono (Finset.coe_subset.mpr hF))]
  refine Finset.card_le_card fun x hx => ?_
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  exact hE p hp

private theorem lp2_card_le_add_one {N q t : ℕ} (x : ℕ) (E : Finset ℕ)
    (hE : ∀ p ∈ primeSenders N q t, p ≠ x → N.factorization p ∈ E) :
    (primeSenders N q t).card ≤ E.card + 1 := by
  have h1 := lp2_card_le ((primeSenders N q t).erase x) E (Finset.erase_subset _ _)
    (fun p hp => hE p (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp))
  have h2 := Finset.pred_card_le_card_erase (s := primeSenders N q t) (a := x)
  omega

private theorem lp2_exp_ne {N q t p : ℕ}
    (hP : ∀ p ∈ N.primeFactors, p ≠ q → (σ 1 (p ^ N.factorization p)).Prime)
    (htN : t ∈ N.primeFactors) (htq : t ≠ q) (hp : p ∈ primeSenders N q t) :
    N.factorization p ≠ N.factorization t := by
  obtain ⟨-, -, hp1, hpe, hpt⟩ := lp2_spec hp
  intro heq
  have hPt := hP t htN htq
  rw [← heq] at hPt
  exact not_prime_sigma_of_sigma_eq hp1 (Nat.prime_of_mem_primeFactors htN) hpe hpt hPt

/-- An ordinary prime `t` that receives nothing from the special component has exponent
`|S(t)|`, even and positive. -/
private theorem lp2_free {N q t : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hP : ∀ p ∈ N.primeFactors, p ≠ q → (σ 1 (p ^ N.factorization p)).Prime)
    (htN : t ∈ N.primeFactors) (htq : t ≠ q) (hnd : ¬ t ∣ σ 1 (q ^ N.factorization q)) :
    N.factorization t = (primeSenders N q t).card ∧ Even (N.factorization t) ∧
      N.factorization t ≠ 0 := by
  have ht := Nat.prime_of_mem_primeFactors htN
  have ht2 : t ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors htN)
  have hl := factorization_eq_add_card_primeSenders h (lp2_qN hodd) hP ht ht2
  have hw : sigmaWeight N q t = 0 := Nat.factorization_eq_zero_of_not_dvd hnd
  rw [hw, zero_add] at hl
  exact ⟨hl, even_factorization_of_ne h hq hodd ht htq,
    Finsupp.mem_support_iff.mp (Nat.support_factorization N ▸ htN)⟩

/-- Under `k ≤ 10`, an ordinary prime that receives nothing from the special component has
exponent `2`, `4` or `6`: the exponent is `|S(t)| ≤ 9`, even and positive, and not `8`
because `σ(t ^ 8)` prime forces `9` prime. -/
private theorem lp2_free_small {N q t : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hP : ∀ p ∈ N.primeFactors, p ≠ q → (σ 1 (p ^ N.factorization p)).Prime)
    (hk : ((N.primeFactors.erase q).image N.factorization).card ≤ 10)
    (htN : t ∈ N.primeFactors) (htq : t ≠ q) (hnd : ¬ t ∣ σ 1 (q ^ N.factorization q)) :
    N.factorization t = (primeSenders N q t).card ∧
      (N.factorization t = 2 ∨ N.factorization t = 4 ∨ N.factorization t = 6) := by
  obtain ⟨hl, ⟨j, hj⟩, hne⟩ := lp2_free h hq hodd hP htN htq hnd
  have hc := (card_primeSenders_le hP t).2 (Finset.mem_erase.mpr ⟨htq, htN⟩)
  have hidx := prime_succ_of_prime_sigma_prime_pow (Nat.prime_of_mem_primeFactors htN)
    (hP t htN htq)
  have h8 : N.factorization t ≠ 8 := fun h8 => by rw [h8] at hidx; norm_num at hidx
  refine ⟨hl, ?_⟩
  omega

/-- **Prime component divisor sums need eleven exponents.** Let `N` be an odd perfect number
and `q` its special prime (the prime of odd exponent). If the full divisor sum `σ(p ^ e_p)` is
prime for every prime factor `p ≠ q`, then at least eleven distinct values occur among the
exponents `e_p`, `p ≠ q`. The primality of all these divisor sums is a case hypothesis, not
known to hold for a hypothetical odd perfect number. Whether this result is in the literature
was not verified. -/
theorem eleven_le_card_exponents_of_sigma_prime {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hP : ∀ p ∈ N.primeFactors, p ≠ q → (σ 1 (p ^ N.factorization p)).Prime) :
    11 ≤ ((N.primeFactors.erase q).image N.factorization).card := by
  by_contra hk
  push Not at hk
  have hk' : ((N.primeFactors.erase q).image N.factorization).card ≤ 10 := by omega
  have hqN := lp2_qN hodd
  have hodd2 : ∀ r ∈ N.primeFactors, r ≠ 2 := fun r hr h2 =>
    h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hr)
  have hcnt := card_primeSenders_le hP
  have hledq := factorization_eq_add_card_primeSenders h hqN hP hq (hodd2 q hqN)
  rw [sigmaWeight_self hq, zero_add] at hledq
  have ha4 := (special_mod_four h hq hodd).2
  have ha10 : N.factorization q ≤ 10 := by have := (hcnt q).1; omega
  -- a sender into `q` not dividing `a + 1` receives nothing from the special component
  have hfreeQ : ∀ p ∈ primeSenders N q q, ¬ p ∣ N.factorization q + 1 →
      N.factorization p = (primeSenders N q p).card ∧
        (N.factorization p = 2 ∨ N.factorization p = 4 ∨ N.factorization p = 6) := by
    intro p hp hnd
    obtain ⟨hpN, hpq, hp1, -, hpt⟩ := lp2_spec hp
    refine lp2_free_small h hq hodd hP hk' hpN hpq fun hd => hnd ?_
    exact ((sigma_prime_pow_modEq_succ hq (modEq_one_of_sigma_prime_pow_eq hp1 hpt)
      (N.factorization q)).dvd_iff dvd_rfl).mp hd
  -- the special exponent is `1`
  have ha1 : N.factorization q = 1 := by
    have hc := lp2_card_le_add_one (N := N) (q := q) (t := q) ((N.factorization q + 1) / 2)
      {2, 4, 6} (fun p hp hpx => by
        obtain ⟨hpN, -, hp1, -, -⟩ := lp2_spec hp
        have hp2 := hodd2 p hpN
        have hpge := hp1.two_le
        have hnd : ¬ p ∣ N.factorization q + 1 := by
          intro hd
          have := Nat.le_of_dvd (by omega) hd
          have : p ≤ 10 := by omega
          interval_cases p <;> first | omega | norm_num at hp1
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact (hfreeQ p hp hnd).2)
    have h3 : ({2, 4, 6} : Finset ℕ).card = 3 := by decide
    omega
  have hσq : σ 1 (q ^ N.factorization q) = q + 1 := by
    rw [ha1, sigma_one_apply_prime_pow hq]
    simp [Finset.sum_range_succ, add_comm]
  -- the unique sender `s` into `q`
  obtain ⟨s, hs⟩ := Finset.card_pos.mp (show 0 < (primeSenders N q q).card by omega)
  obtain ⟨hsN, hsq, hs1, -, hσs⟩ := lp2_spec hs
  have hsdvd : ¬ s ∣ N.factorization q + 1 := by
    intro hd
    rw [ha1] at hd
    have := Nat.le_of_dvd (by omega) hd
    have := hs1.two_le
    exact hodd2 s hsN (by omega)
  obtain ⟨hls, hes⟩ := hfreeQ s hs hsdvd
  -- a child `p` of `s` divides `q + 1` only if `p = 3` and `e_s = 4`
  have hchild : ∀ p ∈ primeSenders N q s, p ∣ q + 1 → p = 3 ∧ N.factorization s = 4 := by
    intro p hp hd
    obtain ⟨hpN, -, hp1, -, hpt⟩ := lp2_spec hp
    have hm := sigma_prime_pow_modEq_succ hs1 (modEq_one_of_sigma_prime_pow_eq hp1 hpt)
      (N.factorization s)
    rw [hσs] at hm
    have hd' := ((hm.add_right 1).dvd_iff dvd_rfl).mp hd
    have hp2 := hodd2 p hpN
    have hpge := hp1.two_le
    have : p ≤ 8 := by have := Nat.le_of_dvd (by omega) hd'; omega
    interval_cases p <;> first | omega | norm_num at hp1
  have hfreeS : ∀ p ∈ primeSenders N q s, ¬ (p = 3 ∧ N.factorization s = 4) →
      N.factorization p = (primeSenders N q p).card ∧
        N.factorization p ∈ ({2, 4, 6} : Finset ℕ).erase (N.factorization s) := by
    intro p hp hx
    obtain ⟨hpN, hpq, -, -, -⟩ := lp2_spec hp
    obtain ⟨hl, he⟩ := lp2_free_small h hq hodd hP hk' hpN hpq
      (by rw [hσq]; exact fun hd => hx (hchild p hp hd))
    refine ⟨hl, Finset.mem_erase.mpr ⟨lp2_exp_ne hP hsN hsq hp, ?_⟩⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact he
  have hcard2 : (({2, 4, 6} : Finset ℕ).erase (N.factorization s)).card = 2 := by
    rcases hes with h' | h' | h' <;> rw [h'] <;> decide
  -- hence `e_s = 2`
  have hes2 : N.factorization s = 2 := by
    have hc := lp2_card_le_add_one (N := N) (q := q) (t := s) 3
      (({2, 4, 6} : Finset ℕ).erase (N.factorization s))
      (fun p hp hp3 => (hfreeS p hp (fun hx => hp3 hx.1)).2)
    omega
  have hq' : q + 1 = s ^ 2 + s + 2 := by
    rw [← hσs, hes2, sigma_one_apply_prime_pow hs1]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
    ring
  -- a child `p` of `s`: exponent `4` or `6`, receiving nothing from the special component
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (primeSenders N q s).card by omega)
  obtain ⟨hpN, hpq, hp1, -, hσp⟩ := lp2_spec hp
  obtain ⟨hlp, hep⟩ := hfreeS p hp (fun hx => by omega)
  rw [hes2] at hep
  have hep' : N.factorization p = 4 ∨ N.factorization p = 6 := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hep
    omega
  -- a child `r` of `p` divides `q + 1` only if `r = 29`
  have hgrand : ∀ r ∈ primeSenders N q p, r ≠ 29 →
      N.factorization r ∈ ({2, 4, 6} : Finset ℕ).erase (N.factorization p) := by
    intro r hr hr29
    obtain ⟨hrN, hrq, hr1, -, hrt⟩ := lp2_spec hr
    have hsr : s ≡ N.factorization p + 1 [MOD r] := by
      have := sigma_prime_pow_modEq_succ hp1 (modEq_one_of_sigma_prime_pow_eq hr1 hrt)
        (N.factorization p)
      rwa [hσp] at this
    have hm : q + 1 ≡ (N.factorization p + 1) ^ 2 + (N.factorization p + 1) + 2 [MOD r] := by
      rw [hq']
      exact ((hsr.pow 2).add hsr).add_right 2
    have hr2 := hodd2 r hrN
    have hnd : ¬ r ∣ q + 1 := by
      intro hd
      have hd' := (hm.dvd_iff dvd_rfl).mp hd
      rcases hep' with h' | h' <;> rw [h'] at hd' <;> norm_num at hd'
      · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr1 Nat.prime_two).mp
          (hr1.dvd_of_dvd_pow (show r ∣ 2 ^ 5 by norm_num; exact hd')))
      · rcases (Nat.Prime.dvd_mul hr1).mp (show r ∣ 2 * 29 by norm_num; exact hd') with h2 | h2
        · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr1 Nat.prime_two).mp h2)
        · exact hr29 ((Nat.prime_dvd_prime_iff_eq hr1 (by norm_num)).mp h2)
    obtain ⟨-, he⟩ := lp2_free_small h hq hodd hP hk' hrN hrq (by rw [hσq]; exact hnd)
    refine Finset.mem_erase.mpr ⟨lp2_exp_ne hP hpN hpq hr, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact he
  have hcardp : (({2, 4, 6} : Finset ℕ).erase (N.factorization p)).card = 2 := by
    rcases hep' with h' | h' <;> rw [h'] <;> decide
  have hc := lp2_card_le_add_one (N := N) (q := q) (t := p) 29
    (({2, 4, 6} : Finset ℕ).erase (N.factorization p)) hgrand
  omega

/-- **A forced collision among prime full divisor sums.** Let `N` be an odd perfect number and
`q` its special prime. If the full divisor sum `σ(p ^ e_p)` is prime for every prime factor
`p ≠ q`, then there are an ordinary prime `s` with `σ(s ^ e_s) = q` and `s ∤ σ(q ^ a)`, whose
exponent is even and at least `2`, and two distinct ordinary primes `p ≠ r` with
`σ(p ^ e_p) = σ(r ^ e_r) = s` and `e_p ≠ e_r`. No bound on the number of exponent values is
assumed. The primality of all these divisor sums is a case hypothesis, not known to hold for a
hypothetical odd perfect number. Whether this result is in the literature was not verified. -/
theorem exists_prime_sigma_collision {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hP : ∀ p ∈ N.primeFactors, p ≠ q → (σ 1 (p ^ N.factorization p)).Prime) :
    ∃ s p r : ℕ, s ∈ N.primeFactors ∧ s ≠ q ∧ σ 1 (s ^ N.factorization s) = q ∧
      ¬ s ∣ σ 1 (q ^ N.factorization q) ∧ Even (N.factorization s) ∧
      2 ≤ N.factorization s ∧
      p ∈ N.primeFactors ∧ p ≠ q ∧ r ∈ N.primeFactors ∧ r ≠ q ∧ p ≠ r ∧
      σ 1 (p ^ N.factorization p) = s ∧ σ 1 (r ^ N.factorization r) = s ∧
      N.factorization p ≠ N.factorization r := by
  have hqN := lp2_qN hodd
  have hodd2 : ∀ r ∈ N.primeFactors, r ≠ 2 := fun r hr h2 =>
    h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hr)
  have hledq := factorization_eq_add_card_primeSenders h hqN hP hq (hodd2 q hqN)
  rw [sigmaWeight_self hq, zero_add] at hledq
  have ha0 : N.factorization q ≠ 0 := by obtain ⟨j, hj⟩ := hodd; omega
  -- not every sender into `q` divides `a + 1`: they are distinct primes in `[3, a + 1]`
  obtain ⟨s, hs, hnd⟩ : ∃ s ∈ primeSenders N q q, ¬ s ∣ N.factorization q + 1 := by
    by_contra hall
    push Not at hall
    have hsub : primeSenders N q q ⊆ Finset.Icc 3 (N.factorization q + 1) := by
      intro p hp
      obtain ⟨hpN, -, hp1, -, -⟩ := lp2_spec hp
      have := hp1.two_le
      have := hodd2 p hpN
      have := Nat.le_of_dvd (by omega) (hall p hp)
      exact Finset.mem_Icc.mpr ⟨by omega, this⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    omega
  obtain ⟨hsN, hsq, hs1, -, hσs⟩ := lp2_spec hs
  have hnd' : ¬ s ∣ σ 1 (q ^ N.factorization q) := fun hd => hnd
    (((sigma_prime_pow_modEq_succ hq (modEq_one_of_sigma_prime_pow_eq hs1 hσs)
      (N.factorization q)).dvd_iff dvd_rfl).mp hd)
  obtain ⟨hl, ⟨j, hj⟩, hne⟩ := lp2_free h hq hodd hP hsN hsq hnd'
  obtain ⟨p, hp, r, hr, hpr⟩ := Finset.one_lt_card.mp (show 1 < (primeSenders N q s).card by
    omega)
  obtain ⟨hpN, hpq, hp1, hpe, hpt⟩ := lp2_spec hp
  obtain ⟨hrN, hrq, hr1, -, hrt⟩ := lp2_spec hr
  refine ⟨s, p, r, hsN, hsq, hσs, hnd', ⟨j, hj⟩, by omega, hpN, hpq, hrN, hrq, hpr, hpt, hrt,
    fun heq => hpr (eq_of_sigma_prime_pow_eq hp1 hr1 hpe ?_)⟩
  rw [hpt, heq, hrt]

/-- The collision of `exists_prime_sigma_collision` with prime indices: in addition, `e_s + 1`,
`e_p + 1` and `e_r + 1` are prime. The prime indices follow from the prime full divisor sums
(`σ(x ^ e)` prime forces `e + 1` prime). The primality of all
ordinary full divisor sums is a case hypothesis, not known to hold for a hypothetical odd
perfect number. Whether this result is in the literature was not verified. -/
theorem exists_prime_sigma_collision_prime_index {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hP : ∀ p ∈ N.primeFactors, p ≠ q → (σ 1 (p ^ N.factorization p)).Prime) :
    ∃ s p r : ℕ, s ∈ N.primeFactors ∧ s ≠ q ∧ σ 1 (s ^ N.factorization s) = q ∧
      ¬ s ∣ σ 1 (q ^ N.factorization q) ∧ Even (N.factorization s) ∧
      2 ≤ N.factorization s ∧
      p ∈ N.primeFactors ∧ p ≠ q ∧ r ∈ N.primeFactors ∧ r ≠ q ∧ p ≠ r ∧
      σ 1 (p ^ N.factorization p) = s ∧ σ 1 (r ^ N.factorization r) = s ∧
      N.factorization p ≠ N.factorization r ∧
      (N.factorization s + 1).Prime ∧ (N.factorization p + 1).Prime ∧
      (N.factorization r + 1).Prime := by
  obtain ⟨s, p, r, hsN, hsq, h1, h2, h3, h4, hpN, hpq, hrN, hrq, h5, h6, h7, h8⟩ :=
    exists_prime_sigma_collision h hq hodd hP
  exact ⟨s, p, r, hsN, hsq, h1, h2, h3, h4, hpN, hpq, hrN, hrq, h5, h6, h7, h8,
    prime_succ_of_prime_sigma_prime_pow (Nat.prime_of_mem_primeFactors hsN) (hP s hsN hsq),
    prime_succ_of_prime_sigma_prime_pow (Nat.prime_of_mem_primeFactors hpN) (hP p hpN hpq),
    prime_succ_of_prime_sigma_prime_pow (Nat.prime_of_mem_primeFactors hrN) (hP r hrN hrq)⟩

/-- The eleven smallest even `e` with `e + 1` prime. -/
private def lp2Small : Finset ℕ := {2, 4, 6, 10, 12, 16, 18, 22, 28, 30, 36}

/-- A set of at least eleven even numbers `e` with `e + 1` prime has `∑ (e - 2) ≥ 162`. -/
private theorem lp2_sum_sub_two {E : Finset ℕ} (hE : ∀ e ∈ E, Even e ∧ (e + 1).Prime)
    (hc : 11 ≤ E.card) : 162 ≤ ∑ e ∈ E, (e - 2) := by
  have hA : E.filter (fun e => e < 37) ⊆ lp2Small := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨⟨j, rfl⟩, hpr⟩ := hE _ he.1
    have : j < 19 := by have := he.2; omega
    interval_cases j <;> first | decide | norm_num at hpr
  have hsplit : (∑ e ∈ E.filter (fun e => e < 37), (e - 2)) +
      ∑ e ∈ E.filter (fun e => ¬ e < 37), (e - 2) = ∑ e ∈ E, (e - 2) :=
    Finset.sum_filter_add_sum_filter_not E _ _
  have hcard : (E.filter (fun e => e < 37)).card + (E.filter (fun e => ¬ e < 37)).card =
      E.card := Finset.card_filter_add_card_filter_not _
  have hB : (E.filter (fun e => ¬ e < 37)).card * 35 ≤
      ∑ e ∈ E.filter (fun e => ¬ e < 37), (e - 2) := by
    have := Finset.card_nsmul_le_sum (E.filter (fun e => ¬ e < 37)) (fun e => e - 2) 35
      (fun e he => by rw [Finset.mem_filter] at he; omega)
    simpa [smul_eq_mul] using this
  have hsd : (∑ e ∈ lp2Small \ E.filter (fun e => e < 37), (e - 2)) +
      ∑ e ∈ E.filter (fun e => e < 37), (e - 2) = ∑ e ∈ lp2Small, (e - 2) :=
    Finset.sum_sdiff hA
  have hPsum : ∑ e ∈ lp2Small, (e - 2) = 162 := by decide
  have hD : ∑ e ∈ lp2Small \ E.filter (fun e => e < 37), (e - 2) ≤
      (lp2Small \ E.filter (fun e => e < 37)).card * 34 := by
    have := Finset.sum_le_card_nsmul (lp2Small \ E.filter (fun e => e < 37)) (fun e => e - 2) 34
      (fun e he => by
        have := (Finset.mem_sdiff.mp he).1
        simp only [lp2Small, Finset.mem_insert, Finset.mem_singleton] at this
        omega)
    simpa [smul_eq_mul] using this
  have hcd := Finset.card_sdiff_of_subset hA
  have hP11 : lp2Small.card = 11 := by decide
  have hAle := Finset.card_le_card hA
  omega

/-- **Counting consequences of eleven exponents.** Let `N` be an odd perfect number and `q` its
special prime. If the full divisor sum `σ(p ^ e_p)` is prime for every prime factor `p ≠ q`,
then `ω N ≥ 12`, `Ω N ≥ 185` and `Ω N ≥ 2 ω N + 161`. The eleven distinct ordinary exponents
all have prime index `e + 1` (an odd prime), so they are at least `2, 4, 6, 10, 12, 16, 18, 22,
28, 30, 36`. The primality of all ordinary full divisor sums is a case hypothesis, not known to
hold for a hypothetical odd perfect number. Whether this result is in the literature was not
verified. -/
theorem prime_sigma_counting {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hP : ∀ p ∈ N.primeFactors, p ≠ q → (σ 1 (p ^ N.factorization p)).Prime) :
    12 ≤ ω N ∧ 185 ≤ Ω N ∧ 2 * ω N + 161 ≤ Ω N := by
  have h11 := eleven_le_card_exponents_of_sigma_prime h hq hodd hP
  have hqN := lp2_qN hodd
  rw [cardDistinctFactors_eq_card_primeFactors, cardFactors_eq_sum_primeFactors,
    ← Finset.add_sum_erase _ _ hqN]
  have hm := Finset.card_erase_of_mem hqN
  have hpos := Finset.card_pos.mpr ⟨q, hqN⟩
  have himg := Finset.card_image_le (s := N.primeFactors.erase q) (f := N.factorization)
  have ha0 : 1 ≤ N.factorization q := by obtain ⟨j, hj⟩ := hodd; omega
  have hge2 : ∀ p ∈ N.primeFactors.erase q, 2 ≤ N.factorization p := by
    intro p hp
    obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hp
    obtain ⟨j, hj⟩ := even_factorization_of_ne h hq hodd (Nat.prime_of_mem_primeFactors hpN) hpq
    have := Finsupp.mem_support_iff.mp (Nat.support_factorization N ▸ hpN)
    omega
  have hc : ∑ p ∈ N.primeFactors.erase q, N.factorization p =
      ∑ p ∈ N.primeFactors.erase q, (N.factorization p - 2 + 2) :=
    Finset.sum_congr rfl fun p hp => (Nat.sub_add_cancel (hge2 p hp)).symm
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at hc
  have himage : ∑ e ∈ (N.primeFactors.erase q).image N.factorization, (e - 2) ≤
      ∑ p ∈ N.primeFactors.erase q, (N.factorization p - 2) :=
    Finset.sum_image_le_of_nonneg fun _ _ => Nat.zero_le _
  have h162 := lp2_sum_sub_two (E := (N.primeFactors.erase q).image N.factorization)
    (fun e he => by
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hp
      have hp1 := Nat.prime_of_mem_primeFactors hpN
      exact ⟨even_factorization_of_ne h hq hodd hp1 hpq,
        prime_succ_of_prime_sigma_prime_pow hp1 (hP p hpN hpq)⟩) h11
  omega

end OddPerfect

#print axioms OddPerfect.sigma_prime_pow_modEq_succ
#print axioms OddPerfect.modEq_one_of_sigma_prime_pow_eq
#print axioms OddPerfect.eleven_le_card_exponents_of_sigma_prime
#print axioms OddPerfect.exists_prime_sigma_collision
#print axioms OddPerfect.exists_prime_sigma_collision_prime_index
#print axioms OddPerfect.prime_sigma_counting
