import OddPerfect.Steuerwald
import OddPerfect.Valuation
import OddPerfect.McDaniel
import OddPerfect.SpecialPrime

/-!
# Odd perfect numbers with equal ordinary exponents

Results in the circle of Kanold, Hagis and McDaniel, Cohen and Williams, and Yamada on
odd perfect numbers `N = q ^ k ∏ p_i ^ (2 β)` whose ordinary exponents (those of the primes
other than the special prime `q`) all equal `2 β`, together with general forms that do not
need equal exponents.

* Residue avoidance (Yamada): a prime `r ∤ N` forbids every ordinary component `p ^ e` with
  `l ∣ e + 1` from having multiplicative order `l` modulo `r`.
* The `l`-adic counting bound (Hagis and McDaniel, Yamada): every prime factor `p ≡ 1 (mod l)`
  contributes `v_l(e_p + 1)` to `v_l(N)`.
* Kanold's divisibility `l ∣ N` when every ordinary exponent plus one is a power of `l`.
* Kanold's `l ^ 4 ∣ N` when all ordinary exponents equal `l - 1`, and `l ^ 5 ∣ N` when `l`
  is the special prime.
* The prime factors of the components `σ(p ^ (l - 1))` and a bound on the number of
  components that are not powers of the special prime.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- Residue avoidance (Yamada). If a prime `r` does not divide the odd perfect number `N`,
`1 < l` and `l ∣ v_p(N) + 1`, then `p` does not have multiplicative order `l` modulo `r`.
(Order `l` would force `r ∣ σ(p ^ v_p(N)) ∣ 2 N`.) -/
theorem orderOf_ne_of_not_dvd {N p r l : ℕ} (h : OddPerfect N) (hp : p.Prime) (hr : r.Prime)
    (hrN : ¬ r ∣ N) (hl : 1 < l) (hle : l ∣ N.factorization p + 1) :
    orderOf (p : ZMod r) ≠ l := by
  have : Fact r.Prime := ⟨hr⟩
  intro ho
  by_cases h0 : (p : ZMod r) = 0
  · rw [h0, orderOf_zero] at ho
    omega
  have hdvd := ZMod.orderOf_dvd_card_sub_one h0
  have hr2 : r ≠ 2 := by
    rintro rfl
    rw [ho] at hdvd
    have := Nat.le_of_dvd one_pos hdvd
    omega
  have hpr : p ≠ r := by
    rintro rfl
    exact h0 (ZMod.natCast_self p)
  have hd := dvd_sigma_prime_pow_of_orderOf_dvd hp hr hpr (ho ▸ hl) (ho ▸ hle)
  exact hrN (OPNStarter.force_prime h.perfect hp rfl hr hr2 hd)

/-- If `p % l = 1` for an odd prime `l`, then `v_l(σ(p ^ a)) = v_l(a + 1)`. -/
theorem padicValNat_sigma_of_mod_eq_one {p l a : ℕ} (hp : p.Prime) (hl : l.Prime) (hl2 : l ≠ 2)
    (h1 : p % l = 1) : padicValNat l (σ 1 (p ^ a)) = padicValNat l (a + 1) :=
  padicValNat_sigma_prime_pow_of_dvd_pred hp hl hl2
    ((Nat.modEq_iff_dvd' hp.one_lt.le).mp (by rw [Nat.ModEq, h1, Nat.mod_eq_of_lt hl.one_lt]))

/-- If an odd prime `l` does not divide the odd perfect number `N`, no prime factor `p` with
`l ∣ v_p(N) + 1` is `1` modulo `l`. -/
theorem mod_ne_one_of_not_dvd {N l p : ℕ} (h : OddPerfect N) (hl : l.Prime) (hl2 : l ≠ 2)
    (hlN : ¬ l ∣ N) (hp : p.Prime) (hle : l ∣ N.factorization p + 1) : p % l ≠ 1 := by
  intro h1
  have : Fact l.Prime := ⟨hl⟩
  have hσ0 : σ 1 (p ^ N.factorization p) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)).ne'
  have hv := padicValNat_sigma_of_mod_eq_one hp hl hl2 h1 (a := N.factorization p)
  have hpos : 1 ≤ padicValNat l (N.factorization p + 1) := one_le_padicValNat_of_dvd (by omega) hle
  have hd : l ∣ σ 1 (p ^ N.factorization p) := by
    have := pow_padicValNat_dvd (p := l) (n := σ 1 (p ^ N.factorization p))
    exact (dvd_pow_self l (by omega)).trans this
  exact hlN (OPNStarter.force_prime h.perfect hp rfl hl hl2 hd)

/-- The `l`-adic counting bound (Hagis and McDaniel; Yamada). For a perfect number `N` and an
odd prime `l`, the prime factors `p ≡ 1 (mod l)` together contribute
`∑ v_l(v_p(N) + 1) ≤ v_l(N)`. -/
theorem sum_padicValNat_succ_le {N l : ℕ} (hN : N.Perfect) (hl : l.Prime) (hl2 : l ≠ 2) :
    ∑ p ∈ N.primeFactors.filter (fun p => p % l = 1), padicValNat l (N.factorization p + 1) ≤
      N.factorization l := by
  rw [factorization_eq_sum_erase hN hl hl2]
  have hsub : N.primeFactors.filter (fun p => p % l = 1) ⊆ N.primeFactors.erase l := by
    intro p hp
    obtain ⟨hpN, h1⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_erase.mpr ⟨?_, hpN⟩
    rintro rfl
    rw [Nat.mod_self] at h1
    omega
  calc _ = ∑ p ∈ N.primeFactors.filter (fun p => p % l = 1),
        padicValNat l (σ 1 (p ^ N.factorization p)) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        obtain ⟨hpN, h1⟩ := Finset.mem_filter.mp hp
        exact (padicValNat_sigma_of_mod_eq_one (Nat.prime_of_mem_primeFactors hpN) hl hl2 h1).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

/-- The counting bound in the equal exponent case: if every ordinary exponent of the perfect
number `N` equals `2 β`, then for an odd prime `l` the number of ordinary prime factors
`p ≡ 1 (mod l)` times `v_l(2 β + 1)` is at most `v_l(N)`. -/
theorem card_mul_padicValNat_le {N q l β : ℕ} (hN : N.Perfect) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 2 * β) :
    (N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1)).card * padicValNat l (2 * β + 1) ≤
      N.factorization l := by
  refine le_trans ?_ (sum_padicValNat_succ_le hN hl hl2)
  rw [← smul_eq_mul, ← Finset.sum_const]
  calc _ = ∑ p ∈ N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1),
        padicValNat l (N.factorization p + 1) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        obtain ⟨hpN, hpq, -⟩ := Finset.mem_filter.mp hp
        rw [hexp p hpN hpq]
    _ ≤ _ := Finset.sum_le_sum_of_subset fun p hp => by
        obtain ⟨hpN, -, h1⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨hpN, h1⟩

/-- The counting bound with `l` ordinary: if every ordinary exponent equals `2 β` and the odd
prime `l` is an ordinary prime factor, then
`#{ordinary p ≡ 1 (mod l)} * v_l(2 β + 1) ≤ 2 β`. -/
theorem card_mul_padicValNat_le_of_ordinary {N q l β : ℕ} (hN : N.Perfect) (hl : l.Prime)
    (hl2 : l ≠ 2) (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 2 * β)
    (hlN : l ∈ N.primeFactors) (hlq : l ≠ q) :
    (N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1)).card * padicValNat l (2 * β + 1) ≤
      2 * β :=
  hexp l hlN hlq ▸ card_mul_padicValNat_le hN hl hl2 hexp

/-- Corollary for `2 β + 1 = l` prime and `l` ordinary: at most `2 β` ordinary prime factors
are `1` modulo `l`. -/
theorem card_mod_one_le {N q l β : ℕ} (hN : N.Perfect) (hl : l.Prime) (hl2 : l ≠ 2)
    (hβ : 2 * β + 1 = l) (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 2 * β)
    (hlN : l ∈ N.primeFactors) (hlq : l ≠ q) :
    (N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1)).card ≤ 2 * β := by
  have hc := card_mul_padicValNat_le_of_ordinary hN hl hl2 hexp hlN hlq
  have : Fact l.Prime := ⟨hl⟩
  rwa [hβ, padicValNat_self, mul_one] at hc

/-- If an odd prime `l` does not divide the odd perfect number `N` with special prime `q`,
and every ordinary exponent `e` has `e + 1` a power of `l`, then every ordinary component
divisor sum `σ(p ^ v_p(N))` is a power of `q`. -/
theorem sigma_eq_special_pow_of_succ_eq_pow {N q l p : ℕ} (h : OddPerfect N)
    (hl : l.Prime) (hl2 : l ≠ 2) (hlN : ¬ l ∣ N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → ∃ a, N.factorization p + 1 = l ^ a)
    (hp : p ∈ N.primeFactors) (hpq : p ≠ q) : ∃ c : ℕ, σ 1 (p ^ N.factorization p) = q ^ c := by
  have hN0 := h.ne_zero
  have hpp := Nat.prime_of_mem_primeFactors hp
  -- an ordinary exponent plus one is divisible by `l`
  have hldvd : ∀ r ∈ N.primeFactors, r ≠ q → l ∣ N.factorization r + 1 := by
    intro r hr hrq
    obtain ⟨a, ha⟩ := hexp r hr hrq
    have hpos : N.factorization r ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]; exact hr
    rcases a with _ | a
    · simp at ha; omega
    · rw [ha, pow_succ]; exact dvd_mul_left _ _
  obtain ⟨a, ha⟩ := hexp p hp hpq
  have hσ0 : σ 1 (p ^ N.factorization p) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)).ne'
  have hall : ∀ {t : ℕ}, t.Prime → t ∣ σ 1 (p ^ N.factorization p) → t = q := by
    intro t ht htd
    rcases (prime_dvd_sigma_prime_pow hpp ht htd).2 with ⟨-, h2⟩ | ⟨h1, hd, hd'⟩
    · rw [ha] at h2
      have htl : t = l := (Nat.prime_dvd_prime_iff_eq ht hl).mp (ht.dvd_of_dvd_pow h2)
      subst htl
      exact absurd (OPNStarter.force_prime h.perfect hpp rfl ht hl2 htd) hlN
    · rw [ha] at hd
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hl).mp hd
      have hj0 : j ≠ 0 := by rintro rfl; rw [hj, pow_zero] at h1; omega
      have hlt : l ∣ t - 1 := by
        rw [hj] at hd'
        exact (dvd_pow_self l hj0).trans hd'
      have ht2 : t ≠ 2 := by
        rintro rfl
        have := Nat.le_of_dvd one_pos hlt
        have := hl.two_le
        omega
      have ht1 : t % l = 1 := by
        have h := (Nat.modEq_iff_dvd' ht.one_lt.le).mpr hlt
        rw [Nat.ModEq, Nat.mod_eq_of_lt hl.one_lt] at h
        exact h.symm
      have htN := OPNStarter.force_prime h.perfect hpp rfl ht ht2 htd
      by_contra htq
      exact mod_ne_one_of_not_dvd h hl hl2 hlN ht
        (hldvd t (Nat.mem_primeFactors.mpr ⟨ht, htN, hN0⟩) htq) ht1
  exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hσ0 hall⟩

/-- Kanold's divisibility, prime power form. Let `N` be an odd perfect number with special
prime `q` and let `l` be an odd prime. If every ordinary exponent `e` has `e + 1` equal to a
power of `l` (the power may depend on the prime), then `l ∣ N`. This generalizes
`not_all_exponents_eq_pred_prime` (the case `e + 1 = l`). -/
theorem dvd_of_succ_eq_pow {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → ∃ a, N.factorization p + 1 = l ^ a) : l ∣ N := by
  by_contra hlN
  exact not_all_components_special_powers h hq hodd fun p hp hpq =>
    sigma_eq_special_pow_of_succ_eq_pow h hl hl2 hlN hexp hp hpq

/-- Kanold's divisibility in the equal exponent case: if every ordinary exponent equals `2 β`
and `2 β + 1 = l ^ a` for an odd prime `l`, then `l ∣ N`. -/
theorem dvd_of_equal_exponents_of_succ_eq_pow {N q l β a : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2) (hβ : 2 * β + 1 = l ^ a)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 2 * β) : l ∣ N :=
  dvd_of_succ_eq_pow h hq hodd hl hl2 fun p hp hpq => ⟨a, by rw [hexp p hp hpq, hβ]⟩

/-- If the prime `p` is not `1` modulo the prime `l` and `p ≠ l`, then `l ∤ σ(p ^ (l - 1))`. -/
theorem padicValNat_sigma_pred_of_mod_ne_one {p l : ℕ} (hp : p.Prime) (hl : l.Prime)
    (hpl : p ≠ l) (h1 : p % l ≠ 1) : padicValNat l (σ 1 (p ^ (l - 1))) = 0 := by
  have : Fact l.Prime := ⟨hl⟩
  refine padicValNat_sigma_prime_pow_of_not_orderOf_dvd hp hl fun hd => ?_
  rw [Nat.sub_add_cancel hl.one_lt.le] at hd
  have h0 : (p : ZMod l) ≠ 0 := fun h0 =>
    hpl ((Nat.prime_dvd_prime_iff_eq hl hp).mp ((ZMod.natCast_eq_zero_iff _ _).mp h0)).symm
  have hd' := ZMod.orderOf_dvd_card_sub_one h0
  have h1' : orderOf (p : ZMod l) ∣ 1 := by
    have := Nat.dvd_sub hd hd'
    rwa [Nat.sub_sub_self hl.one_lt.le] at this
  have hc : (p : ZMod l) = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1')
  have := (ZMod.natCast_eq_natCast_iff' p 1 l).mp (by simpa using hc)
  rw [Nat.mod_eq_of_lt hl.one_lt] at this
  exact h1 this

/-- `1 + p ≤ σ(p ^ e)` for a prime `p` and `e ≥ 1`. -/
private lemma one_add_le_sigma {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) : 1 + p ≤ σ 1 (p ^ e) := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [zero_add, pow_one, pow_zero]
  omega

/-- Equal exponents with `2 β + 1 = q` the special prime: `v_q(N)` equals the number of
ordinary prime factors `p ≡ 1 (mod q)`. -/
theorem factorization_special_eq_card {N q β : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hβ : 2 * β + 1 = q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 2 * β) :
    N.factorization q = (N.primeFactors.filter (fun p => p ≠ q ∧ p % q = 1)).card := by
  have : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by
    have := (mod_four_special h hq hodd).1
    omega
  have hset : N.primeFactors.filter (fun p => p ≠ q ∧ p % q = 1) =
      (N.primeFactors.erase q).filter (fun p => p % q = 1) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  rw [hset, Finset.card_filter, factorization_eq_sum_erase h.perfect hq hq2]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hp
  have hpp := Nat.prime_of_mem_primeFactors hpN
  rw [hexp p hpN hpq]
  split_ifs with h1
  · rw [padicValNat_sigma_of_mod_eq_one hpp hq hq2 h1, hβ, padicValNat_self]
  · rw [show 2 * β = q - 1 by omega]
    exact padicValNat_sigma_pred_of_mod_ne_one hpp hq hpq h1

/-- Kanold, special case: if all ordinary exponents equal `2 β` and `2 β + 1 = q` is the
special prime, then `v_q(N) ≥ 5`. (Exactly one ordinary prime `p ≡ 1 (mod q)` would force
`σ(p ^ (q - 1)) = q`, which is too small; and `v_q(N) ≡ 1 (mod 4)`.) -/
theorem five_le_factorization_special {N q β : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hβ : 2 * β + 1 = q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 2 * β) :
    5 ≤ N.factorization q := by
  have : Fact q.Prime := ⟨hq⟩
  have hN0 := h.ne_zero
  have h4 := (mod_four_special h hq hodd).2
  have hq5 : 5 ≤ q := by have := (mod_four_special h hq hodd).1; have := hq.two_le; omega
  have hq2 : q ≠ 2 := by omega
  have hcard := factorization_special_eq_card h hq hodd hβ hexp
  set S := N.primeFactors.filter (fun p => p ≠ q ∧ p % q = 1) with hS
  suffices hne : S.card ≠ 1 by omega
  intro h1
  obtain ⟨p, hSp⟩ := Finset.card_eq_one.mp h1
  have hpS : p ∈ S := hSp ▸ Finset.mem_singleton_self p
  obtain ⟨hpN, hpq, hp1⟩ := Finset.mem_filter.mp hpS
  have hpp := Nat.prime_of_mem_primeFactors hpN
  have hep := hexp p hpN hpq
  have hσ0 : σ 1 (p ^ (2 * β)) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)).ne'
  have hall : ∀ {t : ℕ}, t.Prime → t ∣ σ 1 (p ^ (2 * β)) → t = q := by
    intro t ht htd
    have htd' : t ∣ σ 1 (p ^ (q - 1)) := by rwa [show q - 1 = 2 * β by omega]
    rcases prime_dvd_sigma_prime_pow_of_prime_length hpp ht hq htd' with htq | ht1
    · exact htq
    · exfalso
      have ht2 : t ≠ 2 := by rintro rfl; rw [Nat.mod_eq_of_lt (by omega)] at ht1; omega
      have htN := OPNStarter.force_prime h.perfect hpp hep ht ht2 htd
      have htq : t ≠ q := by rintro rfl; rw [Nat.mod_self] at ht1; omega
      have htS : t ∈ S :=
        Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨ht, htN, hN0⟩, htq, ht1⟩
      rw [hSp, Finset.mem_singleton] at htS
      exact (prime_dvd_sigma_prime_pow hpp ht htd).1 htS
  obtain hc := Nat.eq_prime_pow_of_unique_prime_dvd hσ0 hall
  have hv := padicValNat_sigma_of_mod_eq_one hpp hq hq2 hp1 (a := 2 * β)
  rw [hc, padicValNat.prime_pow, hβ, padicValNat_self] at hv
  rw [hv, pow_one] at hc
  have hle := one_add_le_sigma hpp (show 1 ≤ 2 * β by omega)
  have hpq' : q < p := by
    have := hpp.two_le
    by_contra hlt
    rw [Nat.mod_eq_of_lt (by omega)] at hp1
    omega
  omega

/-- Kanold's `l ^ 4 ∣ N` in the equal exponent case: if every ordinary exponent of the odd
perfect number `N` equals `2 β` and `2 β + 1 = l` is prime, then `l ^ 4 ∣ N`. If `l` is
ordinary then `v_l(N) = l - 1 ≥ 4` (`l = 3` is Steuerwald's case); if `l` is the special
prime then even `l ^ 5 ∣ N`. -/
theorem pow_four_dvd_of_equal_exponents {N q l β : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hβ : 2 * β + 1 = l)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 2 * β) : l ^ 4 ∣ N := by
  have hN0 := h.ne_zero
  have hl2 : l ≠ 2 := by omega
  have hlN : l ∣ N := by
    by_contra hlN
    exact not_all_exponents_eq_pred_prime h hq hodd hl hl2 hlN fun p hp hpq => by
      rw [hexp p hp hpq]; omega
  rw [hl.pow_dvd_iff_le_factorization hN0]
  by_cases hlq : l = q
  · subst hlq
    have := five_le_factorization_special h hl hodd hβ hexp
    omega
  · rw [hexp l (Nat.mem_primeFactors.mpr ⟨hl, hlN, hN0⟩) hlq]
    by_contra hlt
    have hβ1 : β = 1 := by have := hl.two_le; omega
    exact steuerwald h hq hodd fun p hp hpq => by rw [hexp p hp hpq, hβ1]

/-- `l ^ 5 ∣ N` when `l = 2 β + 1` is the special prime of an odd perfect number with all
ordinary exponents equal to `2 β`. -/
theorem pow_five_dvd_of_special {N q β : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hβ : 2 * β + 1 = q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 2 * β) : q ^ 5 ∣ N :=
  (hq.pow_dvd_iff_le_factorization h.ne_zero).mpr (five_le_factorization_special h hq hodd hβ hexp)

/-- Prime factors of the ordinary components in the equal exponent case with `2 β + 1 = l`
prime: every prime `t ∣ σ(p ^ (2 β))`, `p` ordinary, divides `N` and is `l`, the special
prime `q`, or an ordinary prime factor `≡ 1 (mod l)`. -/
theorem prime_dvd_sigma_of_equal_exponents {N q l β p t : ℕ} (h : OddPerfect N)
    (hl : l.Prime) (hβ : 2 * β + 1 = l)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 2 * β)
    (hp : p ∈ N.primeFactors) (hpq : p ≠ q) (ht : t.Prime) (htd : t ∣ σ 1 (p ^ (2 * β))) :
    t ∣ N ∧ (t = l ∨ t = q ∨ t ∈ N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1)) := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have htd' : t ∣ σ 1 (p ^ (l - 1)) := by rwa [show l - 1 = 2 * β by omega]
  have ht2 : t ≠ 2 := by
    rintro rfl
    rcases prime_dvd_sigma_prime_pow_of_prime_length hpp ht hl htd' with h2 | h2
    · omega
    · rw [Nat.mod_eq_of_lt (by omega)] at h2; omega
  have htN := OPNStarter.force_prime h.perfect hpp (hexp p hp hpq) ht ht2 htd
  refine ⟨htN, ?_⟩
  rcases prime_dvd_sigma_prime_pow_of_prime_length hpp ht hl htd' with htl | ht1
  · exact Or.inl htl
  · by_cases htq : t = q
    · exact Or.inr (Or.inl htq)
    · exact Or.inr (Or.inr (Finset.mem_filter.mpr
        ⟨Nat.mem_primeFactors.mpr ⟨ht, htN, h.ne_zero⟩, htq, ht1⟩))

open Classical in
/-- Components that are not powers of the special prime. If every ordinary exponent of the
odd perfect number `N` equals `2 β`, `2 β + 1 = l` is prime and `l` is an ordinary prime
factor, then at most `2 β (2 β + 1)` ordinary primes `p` have `σ(p ^ (2 β))` not a power of
the special prime `q`. (They are the at most `2 β` primes `≡ 1 (mod l)`, and primes feeding
one of these, each of which receives total weight `2 β`.) -/
theorem card_not_special_pow_le {N q l β : ℕ} (h : OddPerfect N) (hl : l.Prime)
    (hβ : 2 * β + 1 = l) (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 2 * β)
    (hlN : l ∈ N.primeFactors) (hlq : l ≠ q) :
    (N.primeFactors.filter (fun p => p ≠ q ∧ ¬ ∃ c, σ 1 (p ^ (2 * β)) = q ^ c)).card ≤
      2 * β * (2 * β + 1) := by
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have hl2 : l ≠ 2 := by omega
  set S := N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1) with hS
  set A : ℕ → Finset ℕ := fun s =>
    (N.primeFactors.erase s).filter (fun p => s ∣ σ 1 (p ^ N.factorization p)) with hA
  have hSle : S.card ≤ 2 * β := card_mod_one_le h.perfect hl hl2 hβ hexp hlN hlq
  -- each `A s` with `s ∈ S` has at most `2 β` elements
  have hAle : ∀ s ∈ S, (A s).card ≤ 2 * β := by
    intro s hs
    obtain ⟨hsN, hsq, hs1⟩ := Finset.mem_filter.mp hs
    have hsp := Nat.prime_of_mem_primeFactors hsN
    have : Fact s.Prime := ⟨hsp⟩
    have hs2 : s ≠ 2 := by rintro rfl; rw [Nat.mod_eq_of_lt (by omega)] at hs1; omega
    rw [← hexp s hsN hsq, factorization_eq_sum_erase h.perfect hsp hs2, Finset.card_eq_sum_ones]
    calc ∑ p ∈ A s, 1 ≤ ∑ p ∈ A s, padicValNat s (σ 1 (p ^ N.factorization p)) := by
          refine Finset.sum_le_sum fun p hp => ?_
          obtain ⟨hp', hd⟩ := Finset.mem_filter.mp hp
          have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp')
          exact one_le_padicValNat_of_dvd (sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)).ne' hd
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  -- the set in question lies in `S ∪ ⋃_{s ∈ S} A s`
  have hsub : N.primeFactors.filter (fun p => p ≠ q ∧ ¬ ∃ c, σ 1 (p ^ (2 * β)) = q ^ c) ⊆
      S ∪ S.biUnion A := by
    intro p hp
    obtain ⟨hpN, hpq, hnot⟩ := Finset.mem_filter.mp hp
    have hpp := Nat.prime_of_mem_primeFactors hpN
    by_cases hp1 : p % l = 1
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpN, hpq, hp1⟩)
    refine Finset.mem_union_right _ ?_
    have hσ0 : σ 1 (p ^ (2 * β)) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)).ne'
    obtain ⟨t, ht, htd, htq⟩ : ∃ t, t.Prime ∧ t ∣ σ 1 (p ^ (2 * β)) ∧ t ≠ q := by
      by_contra hcon
      push Not at hcon
      exact hnot ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hσ0 fun ht htd => hcon _ ht htd⟩
    obtain ⟨-, htl | htq' | htS⟩ :=
      prime_dvd_sigma_of_equal_exponents h hl hβ hexp hpN hpq ht htd
    · exfalso
      subst htl
      by_cases hpl : p = t
      · exact (prime_dvd_sigma_prime_pow hpp ht htd).1 hpl.symm
      · have hv := padicValNat_sigma_pred_of_mod_ne_one hpp ht hpl hp1
        rw [show t - 1 = 2 * β by omega] at hv
        have : Fact t.Prime := ⟨ht⟩
        have := one_le_padicValNat_of_dvd hσ0 htd
        omega
    · exact absurd htq' htq
    · refine Finset.mem_biUnion.mpr ⟨t, htS, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_erase.mpr ⟨fun hpt => (prime_dvd_sigma_prime_pow hpp ht htd).1 hpt.symm,
          hpN⟩
      · rwa [hexp p hpN hpq]
  calc _ ≤ (S ∪ S.biUnion A).card := Finset.card_le_card hsub
    _ ≤ S.card + ∑ s ∈ S, (A s).card :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _)
    _ ≤ S.card + S.card * (2 * β) := by
        have := Finset.sum_le_card_nsmul S (fun s => (A s).card) (2 * β) hAle
        rw [smul_eq_mul] at this
        omega
    _ ≤ 2 * β * (2 * β + 1) := by nlinarith

/-- Kanold's reduction. Let `N` be an odd perfect number with special prime `q` and let `l`
be an odd prime with `l ∤ N` and `l ∣ e + 1` for every ordinary exponent `e`. Then some
ordinary prime `r` (any odd prime divisor of `(q + 1) / 2`) has `σ(r ^ (l - 1))` a perfect
square: it is `q ^ c` with `c` even since `q ≡ -1 (mod r)`. So Kanold's `l ∣ N` in full
generality follows from the statement that `Φ_l(r)` is never a square for such `r`. -/
theorem exists_isSquare_sigma_of_not_dvd {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2) (hlN : ¬ l ∣ N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1) :
    ∃ r ∈ N.primeFactors, r ≠ q ∧ r ∣ q + 1 ∧ IsSquare (σ 1 (r ^ (l - 1))) := by
  have hq4 := (mod_four_special h hq hodd).1
  have hq5 : 5 ≤ q := by have := hq.two_le; omega
  set r := ((q + 1) / 2).minFac
  have hr1 : (q + 1) / 2 ≠ 1 := by omega
  have hrp : r.Prime := Nat.minFac_prime hr1
  have hrd : r ∣ (q + 1) / 2 := Nat.minFac_dvd _
  have hr2 : r ≠ 2 := by
    intro h2
    rw [h2] at hrd
    omega
  have hrq1 : r ∣ q + 1 := hrd.trans ⟨2, by omega⟩
  obtain ⟨hrN, hrq⟩ := prime_dvd_of_dvd_succ_special h hq hodd hrp hr2 hrq1
  have hrmem : r ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hrp, hrN, h.ne_zero⟩
  obtain ⟨c, -, hc⟩ :=
    sigma_pred_prime_eq_special_pow h hq hodd hl hl2 hlN hexp hrmem hrq
  refine ⟨r, hrmem, hrq, hrq1, ?_⟩
  have : Fact r.Prime := ⟨hrp⟩
  have : Fact (2 < r) := ⟨by have := hrp.two_le; omega⟩
  have hσ : ((σ 1 (r ^ (l - 1)) : ℕ) : ZMod r) = 1 := by
    rw [sigma_one_apply_prime_pow hrp, Finset.sum_range_succ']
    push_cast
    simp
  have hqr : (q : ZMod r) = -1 := by
    have : ((q + 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hrq1
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  rw [hc] at hσ
  push_cast at hσ
  rw [hqr, neg_one_pow_eq_one_iff_even ZMod.neg_one_ne_one] at hσ
  obtain ⟨d, rfl⟩ := hσ
  exact ⟨q ^ d, by rw [hc, pow_add]⟩

/-- `1 + r + r ^ 2 + r ^ 3 + r ^ 4` is a square only for `r ≤ 3`. -/
private lemma le_three_of_sigma_four_sq {r m : ℕ}
    (hm : 1 + r + r ^ 2 + r ^ 3 + r ^ 4 = m * m) : r ≤ 3 := by
  by_contra h4
  push Not at h4
  rcases Nat.lt_or_ge (2 * m) (2 * r ^ 2 + r + 1) with hlt | hge
  · have hle : 2 * m ≤ 2 * r ^ 2 + r := by omega
    have := Nat.mul_le_mul hle hle
    nlinarith
  · have := Nat.mul_le_mul hge hge
    nlinarith

/-- Kanold's divisibility for `l = 5` with no equal exponent assumption: if `5 ∣ e + 1` for
every ordinary exponent `e` of the odd perfect number `N`, then `5 ∣ N`. (By the reduction,
`σ(r ^ 4)` would be a square, forcing `r = 3` and `q ^ (c / 2) = 11`, but `q ≡ 1 (mod 4)`.) -/
theorem five_dvd_of_five_dvd_succ {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → 5 ∣ N.factorization p + 1) : 5 ∣ N := by
  by_contra h5
  obtain ⟨r, hrN, hrq, -, m, hm⟩ :=
    exists_isSquare_sigma_of_not_dvd h hq hodd Nat.prime_five (by norm_num) h5 hexp
  have hrp := Nat.prime_of_mem_primeFactors hrN
  have hσ : σ 1 (r ^ 4) = 1 + r + r ^ 2 + r ^ 3 + r ^ 4 := by
    rw [sigma_one_apply_prime_pow hrp]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
    ring
  have hr3 : r ≤ 3 := le_three_of_sigma_four_sq (m := m) (by
    rw [show (5 : ℕ) - 1 = 4 by norm_num, hσ] at hm; linarith)
  have hr2 : r ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hrN)
  have hr : r = 3 := by have := hrp.two_le; omega
  subst hr
  obtain ⟨c, -, hc⟩ := sigma_pred_prime_eq_special_pow h hq hodd Nat.prime_five (by norm_num) h5
    hexp hrN hrq
  rw [show (5 : ℕ) - 1 = 4 by norm_num, hσ] at hc
  norm_num at hc
  have hq11 : q ∣ 11 ^ 2 := by
    rcases c with _ | c
    · norm_num at hc
    · exact ⟨q ^ c, by rw [pow_succ] at hc; norm_num; linarith⟩
  have := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hq11)
  have := (mod_four_special h hq hodd).1
  omega

/-- Kanold's divisibility for `l = 3`: by McDaniel's theorem the hypothesis `3 ∣ e + 1` for
every ordinary exponent `e` is already contradictory. -/
theorem three_dvd_of_three_dvd_succ {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → 3 ∣ N.factorization p + 1) : 3 ∣ N :=
  (mcdaniel h hq hodd fun p hp hpq => by have := hexp p hp hpq; omega).elim

end OddPerfect

#print axioms OddPerfect.orderOf_ne_of_not_dvd
#print axioms OddPerfect.padicValNat_sigma_of_mod_eq_one
#print axioms OddPerfect.mod_ne_one_of_not_dvd
#print axioms OddPerfect.sum_padicValNat_succ_le
#print axioms OddPerfect.card_mul_padicValNat_le
#print axioms OddPerfect.card_mul_padicValNat_le_of_ordinary
#print axioms OddPerfect.card_mod_one_le
#print axioms OddPerfect.sigma_eq_special_pow_of_succ_eq_pow
#print axioms OddPerfect.dvd_of_succ_eq_pow
#print axioms OddPerfect.dvd_of_equal_exponents_of_succ_eq_pow
#print axioms OddPerfect.padicValNat_sigma_pred_of_mod_ne_one
#print axioms OddPerfect.factorization_special_eq_card
#print axioms OddPerfect.five_le_factorization_special
#print axioms OddPerfect.pow_four_dvd_of_equal_exponents
#print axioms OddPerfect.pow_five_dvd_of_special
#print axioms OddPerfect.prime_dvd_sigma_of_equal_exponents
#print axioms OddPerfect.card_not_special_pow_le
#print axioms OddPerfect.exists_isSquare_sigma_of_not_dvd
#print axioms OddPerfect.five_dvd_of_five_dvd_succ
#print axioms OddPerfect.three_dvd_of_three_dvd_succ
