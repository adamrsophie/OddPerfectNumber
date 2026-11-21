import OddPerfect.Certificate
import OddPerfect.Steuerwald
import OddPerfect.Valuation
import OddPerfect.SpecialPrime
import OddPerfect.Pratt

/-!
# Equal exponents ten and twelve

McDaniel and Hagis (1975), Cohen and Williams (1985): in an odd perfect number the primes
other than the special prime cannot all have exponent exactly `10`, and cannot all have
exponent exactly `12`.

Write `l` for `11` (resp. `13`) and `e = l - 1` for the common exponent.

* `l ∤ N`: Steuerwald's prime length argument `not_all_exponents_eq_pred_prime`.
* `l` is the special prime (only possible for `l = 13`): `not_all_exponents_pred_of_special`.
  Write `N = l ^ k * R ^ (l - 1)` with `l ∤ R`. Every prime factor of
  `X = ∏ σ(p ^ (l - 1))` is `l` or `≡ 1 (mod l)`, so the part `U` of `X` prime to `l` is
  `≡ 1 (mod l)`. Removing the powers of `l` from `σ(l ^ k) * X = 2 * l ^ k * R ^ (l - 1)`
  gives `σ(l ^ k) * U = 2 * R ^ (l - 1)`, which reads `1 = 2` modulo `l` by Fermat.
* `l ∣ N` ordinary: `v_l(N) = l - 1`. Every ordinary prime `p ≡ 1 (mod l)` contributes at
  least one factor `l` to `σ N` through `σ(p ^ (l - 1)) ≡ l (mod l)`, so at most `l` primes
  `≡ 1 (mod l)` divide `N` (one of them may be special). A forcing chain exhibits `l + 1`
  such primes, after a case split on the special prime among the forcing primes
  `≡ 1 (mod 4)`; primes `≡ 3 (mod 4)` are never special.

  Exponent `10`: `σ(11 ^ 10) = 15797 · 1806113`; the cases are `q = 15797`,
  `q = 1806113`, and neither. If `q = 15797`, then `15798 = 2 · 3 · 2633` forces the
  ordinary primes `3` and `2633`.

  Exponent `12`: `σ(13 ^ 12) = 53 · 264031 · 1803647`; the cases are `q = 53`,
  `q = 8346157`, and neither.

Large primes are certified with `Pratt.prime_of_checkPrime`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## General lemmas -/

/-- If `p ≡ 1 (mod l)` then `σ(p ^ (l - 1)) ≡ 0 (mod l)`. -/
private lemma dvd_sigma_pred_of_mod_eq_one {p l : ℕ} (hp : p.Prime) (hl : 1 ≤ l)
    (h : p % l = 1) : l ∣ σ 1 (p ^ (l - 1)) := by
  rw [sigma_one_apply_prime_pow hp, Nat.sub_add_cancel hl, Nat.dvd_iff_mod_eq_zero,
    Finset.sum_nat_mod]
  have : ∀ i ∈ Finset.range l, p ^ i % l = 1 % l := fun i _ => by
    rw [Nat.pow_mod, h, one_pow]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul,
    Nat.mul_mod_right]

/-- A positive number all of whose prime factors are `≡ 1 (mod l)` is itself `≡ 1 (mod l)`. -/
private lemma mod_eq_one_of_forall_prime_dvd {l : ℕ} (hl : 1 < l) :
    ∀ n : ℕ, n ≠ 0 → (∀ t, t.Prime → t ∣ n → t % l = 1) → n % l = 1 := by
  intro n
  induction n using induction_on_primes with
  | zero => intro h; exact absurd rfl h
  | one => intro _ _; exact Nat.mod_eq_of_lt hl
  | prime_mul p a hp ih =>
    intro h0 ht
    have ha : a ≠ 0 := by rintro rfl; simp at h0
    have h1 := ht p hp (dvd_mul_right p a)
    have h2 := ih ha fun t htp htd => ht t htp (htd.mul_left p)
    rw [Nat.mul_mod, h1, h2, Nat.one_mul, Nat.mod_eq_of_lt hl]

/-- Removing the factors `l` from a number not divisible by `l` changes nothing. -/
private lemma ordCompl_of_not_dvd {n l : ℕ} (h : ¬ l ∣ n) : ordCompl[l] n = n := by
  rw [Nat.factorization_eq_zero_of_not_dvd h, pow_zero, Nat.div_one]

/-- If a prime `l` is the special prime of an odd perfect number `N`, the exponents of the
other primes cannot all equal `l - 1`. -/
theorem not_all_exponents_pred_of_special {N l : ℕ} (h : OddPerfect N) (hl : l.Prime)
    (hodd : Odd (N.factorization l))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ l → N.factorization p = l - 1) : False := by
  have : Fact l.Prime := ⟨hl⟩
  have hN0 := h.ne_zero
  have hlN : l ∈ N.primeFactors := Nat.support_factorization N ▸
    Finsupp.mem_support_iff.mpr (by rintro h0; simp [h0] at hodd)
  set k := N.factorization l with hk
  set P := N.primeFactors.erase l with hP
  have hl2 : l ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hlN)
  have hPp : ∀ p ∈ P, p.Prime ∧ p ≠ l ∧ N.factorization p = l - 1 := fun p hp => by
    obtain ⟨hpl, hpN⟩ := Finset.mem_erase.mp hp
    exact ⟨Nat.prime_of_mem_primeFactors hpN, hpl, hexp p hpN hpl⟩
  -- the two product decompositions
  set X := ∏ p ∈ P, σ 1 (p ^ (l - 1)) with hX
  set R := ∏ p ∈ P, p with hR
  have hNprod : N = l ^ k * R ^ (l - 1) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hN0]
    rw [Finsupp.prod, Nat.support_factorization, ← Finset.mul_prod_erase _ _ hlN, hR,
      ← Finset.prod_pow]
    congr 1
    exact Finset.prod_congr rfl fun p hp => by rw [(hPp p hp).2.2]
  have hσprod : σ 1 N = σ 1 (l ^ k) * X := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ hN0, Finsupp.prod,
      Nat.support_factorization, ← Finset.mul_prod_erase _ _ hlN, hX]
    congr 1
    exact Finset.prod_congr rfl fun p hp => by rw [(hPp p hp).2.2]
  have hE : σ 1 (l ^ k) * X = 2 * (l ^ k * R ^ (l - 1)) := by
    rw [← hσprod, ← hNprod, h.sigma_eq]
  -- the part of `X` prime to `l`
  have hX0 : X ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp =>
    (sigma_pos 1 _ (pow_pos (hPp p hp).1.pos _).ne').ne'
  set U := ordCompl[l] X with hU
  have hUmod : U % l = 1 := by
    refine mod_eq_one_of_forall_prime_dvd hl.one_lt U ?_ fun t ht htU => ?_
    · exact (Nat.ordCompl_pos l hX0).ne'
    · have htX : t ∣ X := htU.trans (Nat.ordCompl_dvd X l)
      obtain ⟨p, hp, htp⟩ := (Prime.dvd_finsetProd_iff ht.prime _).mp htX
      rcases prime_dvd_sigma_prime_pow_of_prime_length (hPp p hp).1 ht hl htp with rfl | h1
      · exact absurd htU (Nat.not_dvd_ordCompl hl hX0)
      · exact h1
  have hlR : ¬ l ∣ R := by
    intro hd
    obtain ⟨p, hp, hlp⟩ := (Prime.dvd_finsetProd_iff hl.prime _).mp hd
    exact (hPp p hp).2.1 ((Nat.prime_dvd_prime_iff_eq hl (hPp p hp).1).mp hlp).symm
  have hlσ : ¬ l ∣ σ 1 (l ^ k) := fun hd =>
    (Nat.coprime_comm.mp (coprime_sigma_prime_pow hl k)).eq_one_of_dvd hd |>
      fun h1 => hl.one_lt.ne' h1
  -- remove the factors `l` from both sides
  have hE' : σ 1 (l ^ k) * U = 2 * R ^ (l - 1) := by
    have := congrArg (fun n => ordCompl[l] n) hE
    rw [Nat.ordCompl_mul, Nat.ordCompl_mul, Nat.ordCompl_mul, ordCompl_of_not_dvd hlσ,
      ordCompl_of_not_dvd (fun hd => hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp hd)),
      ordCompl_of_not_dvd (fun hd => hlR (hl.dvd_of_dvd_pow hd)), Nat.ordCompl_self_pow hl,
      ] at this
    · rw [← hU] at this
      simpa using this
  -- reduce modulo `l`
  have hc := congrArg (fun n : ℕ => (n : ZMod l)) hE'
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hc
  have hσ1 : ((σ 1 (l ^ k) : ℕ) : ZMod l) = 1 := by
    rw [sigma_one_apply_prime_pow hl, Nat.cast_sum, Finset.sum_range_succ']
    simp
  have hU1 : ((U : ℕ) : ZMod l) = 1 := by
    rw [← ZMod.natCast_mod, hUmod, Nat.cast_one]
  have hR1 : ((R : ℕ) : ZMod l) ^ (l - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one fun h0 => hlR ((ZMod.natCast_eq_zero_iff R l).mp h0)
  rw [hσ1, hU1, hR1] at hc
  rw [mul_one, mul_one, ← one_add_one_eq_two] at hc
  exact one_ne_zero (left_eq_add.mp hc)

/-- If an odd prime `l` is ordinary with `v_l(N) = l - 1` and all ordinary exponents equal
`l - 1`, then at most `l - 1` ordinary primes `≡ 1 (mod l)` divide `N`. -/
theorem card_erase_special_le {N q l : ℕ} (h : OddPerfect N) (hl : l.Prime) (hl2 : l ≠ 2)
    (hlN : N.factorization l = l - 1)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ N ∧ p % l = 1) :
    (S.erase q).card ≤ l - 1 := by
  have : Fact l.Prime := ⟨hl⟩
  rw [← hlN, factorization_eq_sum_erase h.perfect hl hl2]
  have hsub : S.erase q ⊆ N.primeFactors.erase l := fun p hp => by
    obtain ⟨hpq, hpS⟩ := Finset.mem_erase.mp hp
    obtain ⟨hpp, hpN, hpl⟩ := hS p hpS
    refine Finset.mem_erase.mpr ⟨?_, Nat.mem_primeFactors.mpr ⟨hpp, hpN, h.ne_zero⟩⟩
    rintro rfl
    rw [Nat.mod_self] at hpl
    exact zero_ne_one hpl
  calc (S.erase q).card = ∑ _p ∈ S.erase q, 1 := by simp
    _ ≤ ∑ p ∈ S.erase q, padicValNat l (σ 1 (p ^ N.factorization p)) := by
      refine Finset.sum_le_sum fun p hp => ?_
      obtain ⟨hpq, hpS⟩ := Finset.mem_erase.mp hp
      obtain ⟨hpp, hpN, hpl⟩ := hS p hpS
      rw [hexp p (Nat.mem_primeFactors.mpr ⟨hpp, hpN, h.ne_zero⟩) hpq]
      exact one_le_padicValNat_of_dvd (sigma_pos 1 _ (pow_pos hpp.pos _).ne').ne'
        (dvd_sigma_pred_of_mod_eq_one hpp hl.one_lt.le hpl)
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

/-- Closing step: `l + 1` primes `≡ 1 (mod l)` dividing `N` overflow the `l`-adic ledger. -/
private lemma close {N q l : ℕ} (h : OddPerfect N) (hl : l.Prime) (hl2 : l ≠ 2)
    (hlN : N.factorization l = l - 1)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ N ∧ p % l = 1) (hcard : S.card = l + 1) :
    False := by
  have h1 := card_erase_special_le h hl hl2 hlN hexp S hS
  have h2 := Finset.pred_card_le_card_erase (s := S) (a := q)
  rw [hcard, Nat.add_sub_cancel] at h2
  have h3 : l ≤ l - 1 := h2.trans h1
  have := hl.one_lt
  omega

/-- One forcing step: a prime `r ≠ 2` dividing `σ(p ^ e)` for an ordinary prime `p ∣ N`
divides `N`. -/
private lemma force {N q e p r : ℕ} (h : OddPerfect N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = e)
    (hp : p.Prime) (hpN : p ∣ N) (hpq : p ≠ q) (hr : r.Prime) (hr2 : r ≠ 2)
    (hdiv : Cert.geom p e % r = 0) : r ∣ N :=
  OPNStarter.force_prime h.perfect hp
    (hexp p (Nat.mem_primeFactors.mpr ⟨hp, hpN, h.ne_zero⟩) hpq) hr hr2
    (by rw [Cert.sigma_eq_geom hp]; exact Nat.dvd_of_mod_eq_zero hdiv)

/-- A prime `≡ 3 (mod 4)` is not the special prime. -/
private lemma ne_of_mod_four {p q : ℕ} (hq4 : q % 4 = 1) (hp : p % 4 = 3) : p ≠ q := by
  rintro rfl
  omega

/-! ## Primality certificates -/

private theorem pr_3 : Nat.Prime 3 := by norm_num

private theorem pr_11 : Nat.Prime 11 := by norm_num

private theorem pr_13 : Nat.Prime 13 := by norm_num

private theorem pr_23 : Nat.Prime 23 := by norm_num

private theorem pr_53 : Nat.Prime 53 := by norm_num

private theorem pr_67 : Nat.Prime 67 := by norm_num

private theorem pr_79 : Nat.Prime 79 := by norm_num

private theorem pr_89 : Nat.Prime 89 := by norm_num

private theorem pr_131 : Nat.Prime 131 := by norm_num

private theorem pr_199 : Nat.Prime 199 := by norm_num

private theorem pr_463 : Nat.Prime 463 := by norm_num

private theorem pr_599 : Nat.Prime 599 := by norm_num

private theorem pr_683 : Nat.Prime 683 := by norm_num

private theorem pr_937 : Nat.Prime 937 := by norm_num

private theorem pr_1093 : Nat.Prime 1093 := by norm_num

private theorem pr_1277 : Nat.Prime 1277 := by norm_num

private theorem pr_2113 : Nat.Prime 2113 := by norm_num

private theorem pr_2633 : Nat.Prime 2633 := by norm_num

private theorem pr_2939 : Nat.Prime 2939 := by norm_num

private theorem pr_3851 : Nat.Prime 3851 := by norm_num

private theorem pr_5479 : Nat.Prime 5479 := by norm_num

private theorem pr_7459 : Nat.Prime 7459 := by norm_num

private theorem pr_15797 : Nat.Prime 15797 := by norm_num

private theorem pr_18701 : Nat.Prime 18701 := by norm_num

private theorem pr_34607 : Nat.Prime 34607 := by norm_num

private theorem pr_264031 : Nat.Prime 264031 := by norm_num

private theorem pr_1334737 : Nat.Prime 1334737 :=
  Pratt.prime_of_checkPrime (c := [(1334737, 7, [2, 2, 2, 2, 3, 3, 13, 23, 31])])
    (by decide +kernel)

private theorem pr_1803647 : Nat.Prime 1803647 :=
  Pratt.prime_of_checkPrime (c := [(69371, 2, [2, 5, 7, 991]),
    (1803647, 5, [2, 13, 69371])])
    (by decide +kernel)

private theorem pr_1806113 : Nat.Prime 1806113 :=
  Pratt.prime_of_checkPrime (c := [(1806113, 3, [2, 2, 2, 2, 2, 7, 11, 733])])
    (by decide +kernel)

private theorem pr_3297113 : Nat.Prime 3297113 :=
  Pratt.prime_of_checkPrime (c := [(3297113, 3, [2, 2, 2, 7, 7, 13, 647])])
    (by decide +kernel)

private theorem pr_8346157 : Nat.Prime 8346157 :=
  Pratt.prime_of_checkPrime (c := [(3821, 3, [2, 2, 5, 191]),
    (7643, 2, [2, 3821]),
    (8346157, 19, [2, 2, 3, 7, 13, 7643])])
    (by decide +kernel)

private theorem pr_36751837 : Nat.Prime 36751837 :=
  Pratt.prime_of_checkPrime (c := [(36751837, 5, [2, 2, 3, 11, 509, 547])])
    (by decide +kernel)

private theorem pr_58782569 : Nat.Prime 58782569 :=
  Pratt.prime_of_checkPrime (c := [(1453, 2, [2, 2, 3, 11, 11]),
    (58782569, 3, [2, 2, 2, 13, 389, 1453])])
    (by decide +kernel)

private theorem pr_116880853 : Nat.Prime 116880853 :=
  Pratt.prime_of_checkPrime (c := [(9949, 2, [2, 2, 3, 829]),
    (116880853, 13, [2, 2, 3, 11, 89, 9949])])
    (by decide +kernel)

private theorem pr_603510799 : Nat.Prime 603510799 :=
  Pratt.prime_of_checkPrime (c := [(14221, 2, [2, 2, 3, 3, 5, 79]),
    (603510799, 3, [2, 3, 11, 643, 14221])])
    (by decide +kernel)

private theorem pr_947684519 : Nat.Prime 947684519 :=
  Pratt.prime_of_checkPrime (c := [(43777, 5, [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 19]),
    (43076569, 11, [2, 2, 2, 3, 41, 43777]),
    (947684519, 11, [2, 11, 43076569])])
    (by decide +kernel)

private theorem pr_1546150189 : Nat.Prime 1546150189 :=
  Pratt.prime_of_checkPrime (c := [(2731, 3, [2, 3, 5, 7, 13]),
    (4289, 3, [2, 2, 2, 2, 2, 2, 67]),
    (1546150189, 2, [2, 2, 3, 11, 2731, 4289])])
    (by decide +kernel)

private theorem pr_2128503313 : Nat.Prime 2128503313 :=
  Pratt.prime_of_checkPrime (c := [(6113, 3, [2, 2, 2, 2, 2, 191]),
    (379007, 10, [2, 31, 6113]),
    (2128503313, 5, [2, 2, 2, 2, 3, 3, 3, 13, 379007])])
    (by decide +kernel)

private theorem pr_2497868257 : Nat.Prime 2497868257 :=
  Pratt.prime_of_checkPrime (c := [(48817, 5, [2, 2, 2, 2, 3, 3, 3, 113]),
    (2497868257, 5, [2, 2, 2, 2, 2, 3, 13, 41, 48817])])
    (by decide +kernel)

private theorem pr_2767761413 : Nat.Prime 2767761413 :=
  Pratt.prime_of_checkPrime (c := [(14081, 3, [2, 2, 2, 2, 2, 2, 2, 2, 5, 11]),
    (53226181, 18, [2, 2, 3, 3, 3, 5, 7, 14081]),
    (2767761413, 3, [2, 2, 13, 53226181])])
    (by decide +kernel)

private theorem pr_8209505981 : Nat.Prime 8209505981 :=
  Pratt.prime_of_checkPrime (c := [(8209505981, 3, [2, 2, 5, 13, 37, 47, 67, 271])])
    (by decide +kernel)

private theorem pr_9620773471 : Nat.Prime 9620773471 :=
  Pratt.prime_of_checkPrime (c := [(1063, 3, [2, 3, 3, 59]),
    (1388279, 7, [2, 653, 1063]),
    (9620773471, 7, [2, 3, 3, 5, 7, 11, 1388279])])
    (by decide +kernel)

private theorem pr_55816123897 : Nat.Prime 55816123897 :=
  Pratt.prime_of_checkPrime (c := [(1811, 6, [2, 5, 181]),
    (19877537, 3, [2, 2, 2, 2, 2, 7, 7, 7, 1811]),
    (55816123897, 10, [2, 2, 2, 3, 3, 3, 13, 19877537])])
    (by decide +kernel)

private theorem pr_75449464927 : Nat.Prime 75449464927 :=
  Pratt.prime_of_checkPrime (c := [(1877, 2, [2, 2, 7, 67]),
    (609043, 19, [2, 3, 7, 17, 853]),
    (75449464927, 3, [2, 3, 11, 1877, 609043])])
    (by decide +kernel)

private theorem pr_117942356533 : Nat.Prime 117942356533 :=
  Pratt.prime_of_checkPrime (c := [(1511, 11, [2, 5, 151]),
    (3023, 5, [2, 1511]),
    (1402673, 3, [2, 2, 2, 2, 29, 3023]),
    (117942356533, 5, [2, 2, 3, 7, 7, 11, 13, 1402673])])
    (by decide +kernel)

private theorem pr_211677855071 : Nat.Prime 211677855071 :=
  Pratt.prime_of_checkPrime (c := [(52009301, 2, [2, 2, 5, 5, 7, 191, 389]),
    (211677855071, 7, [2, 5, 11, 37, 52009301])])
    (by decide +kernel)

private theorem pr_11681692691969 : Nat.Prime 11681692691969 :=
  Pratt.prime_of_checkPrime (c := [(29251, 2, [2, 3, 3, 5, 5, 5, 13]),
    (877531, 2, [2, 3, 5, 29251]),
    (877531001, 3, [2, 2, 2, 5, 5, 5, 877531]),
    (1755062003, 2, [2, 877531001]),
    (11681692691969, 3, [2, 2, 2, 2, 2, 2, 2, 2, 2, 13, 1755062003])])
    (by decide +kernel)

private theorem pr_551604349222681 : Nat.Prime 551604349222681 :=
  Pratt.prime_of_checkPrime (c := [(2129, 3, [2, 2, 2, 2, 7, 19]),
    (406073, 3, [2, 2, 2, 193, 263]),
    (551604349222681, 7, [2, 2, 2, 3, 5, 13, 409, 2129, 406073])])
    (by decide +kernel)

private theorem pr_25061845458479893445539 : Nat.Prime 25061845458479893445539 :=
  Pratt.prime_of_checkPrime (c := [(1523, 2, [2, 761]),
    (94427, 2, [2, 31, 1523]),
    (20021, 3, [2, 2, 5, 7, 11, 13]),
    (29569, 17, [2, 2, 2, 2, 2, 2, 2, 3, 7, 11]),
    (354829, 2, [2, 2, 3, 29569]),
    (1888399939, 2, [2, 3, 887, 354829]),
    (56651998171, 2, [2, 3, 5, 1888399939]),
    (25061845458479893445539, 10, [2, 3, 3, 13, 20021, 94427, 56651998171])])
    (by decide +kernel)

/-! ## The forcing chains -/

/-- Exponent ten, `q ∉ {15797, 1806113}`. -/
private lemma ten_gen {N q : ℕ} (h : OddPerfect N) (hq4 : q % 4 = 1)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 10) (h11 : 11 ∣ N)
    (e11 : N.factorization 11 = 10) (ha : q ≠ 15797) (hb : q ≠ 1806113) : False := by
  have d15797 := force h hexp pr_11 h11
    (ne_of_mod_four hq4 (by norm_num)) pr_15797 (by norm_num) (by decide +kernel)
  have d1806113 := force h hexp pr_11 h11
    (ne_of_mod_four hq4 (by norm_num)) pr_1806113 (by norm_num) (by decide +kernel)
  have d463 := force h hexp pr_15797 d15797
    (Ne.symm ha) pr_463 (by norm_num) (by decide +kernel)
  have d199 := force h hexp pr_1806113 d1806113
    (Ne.symm hb) pr_199 (by norm_num) (by decide +kernel)
  have d23 := force h hexp pr_463 d463
    (ne_of_mod_four hq4 (by norm_num)) pr_23 (by norm_num) (by decide +kernel)
  have d5479 := force h hexp pr_463 d463
    (ne_of_mod_four hq4 (by norm_num)) pr_5479 (by norm_num) (by decide +kernel)
  have d1277 := force h hexp pr_5479 d5479
    (ne_of_mod_four hq4 (by norm_num)) pr_1277 (by norm_num) (by decide +kernel)
  have d18701 := force h hexp pr_5479 d5479
    (ne_of_mod_four hq4 (by norm_num)) pr_18701 (by norm_num) (by decide +kernel)
  have d116880853 := force h hexp pr_15797 d15797
    (Ne.symm ha) pr_116880853 (by norm_num) (by decide +kernel)
  have d1546150189 := force h hexp pr_463 d463
    (ne_of_mod_four hq4 (by norm_num)) pr_1546150189 (by norm_num) (by decide +kernel)
  have d75449464927 := force h hexp pr_199 d199
    (ne_of_mod_four hq4 (by norm_num)) pr_75449464927 (by norm_num) (by decide +kernel)
  have d211677855071 := force h hexp pr_463 d463
    (ne_of_mod_four hq4 (by norm_num)) pr_211677855071 (by norm_num) (by decide +kernel)
  refine close h (l := 11) (by norm_num) (by norm_num) e11 hexp
    {15797, 1806113, 463, 199, 23, 5479, 1277, 18701, 116880853, 1546150189, 75449464927, 211677855071} ?_ (by decide)
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨pr_15797, d15797, by norm_num⟩, ⟨pr_1806113, d1806113, by norm_num⟩, ⟨pr_463, d463, by norm_num⟩, ⟨pr_199, d199, by norm_num⟩, ⟨pr_23, d23, by norm_num⟩, ⟨pr_5479, d5479, by norm_num⟩, ⟨pr_1277, d1277, by norm_num⟩, ⟨pr_18701, d18701, by norm_num⟩, ⟨pr_116880853, d116880853, by norm_num⟩, ⟨pr_1546150189, d1546150189, by norm_num⟩, ⟨pr_75449464927, d75449464927, by norm_num⟩, ⟨pr_211677855071, d211677855071, by norm_num⟩]

/-- Exponent ten, `q = 1806113`. -/
private lemma ten_1806113 {N : ℕ} (h : OddPerfect N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ 1806113 → N.factorization p = 10) (h11 : 11 ∣ N)
    (e11 : N.factorization 11 = 10) : False := by
  have d15797 := force h hexp pr_11 h11
    (by norm_num) pr_15797 (by norm_num) (by decide +kernel)
  have d463 := force h hexp pr_15797 d15797
    (by norm_num) pr_463 (by norm_num) (by decide +kernel)
  have d23 := force h hexp pr_463 d463
    (by norm_num) pr_23 (by norm_num) (by decide +kernel)
  have d5479 := force h hexp pr_463 d463
    (by norm_num) pr_5479 (by norm_num) (by decide +kernel)
  have d1277 := force h hexp pr_5479 d5479
    (by norm_num) pr_1277 (by norm_num) (by decide +kernel)
  have d18701 := force h hexp pr_5479 d5479
    (by norm_num) pr_18701 (by norm_num) (by decide +kernel)
  have d34607 := force h hexp pr_18701 d18701
    (by norm_num) pr_34607 (by norm_num) (by decide +kernel)
  have d36751837 := force h hexp pr_1277 d1277
    (by norm_num) pr_36751837 (by norm_num) (by decide +kernel)
  have d67 := force h hexp pr_36751837 d36751837
    (by norm_num) pr_67 (by norm_num) (by decide +kernel)
  have d89 := force h hexp pr_67 d67
    (by norm_num) pr_89 (by norm_num) (by decide +kernel)
  have d116880853 := force h hexp pr_15797 d15797
    (by norm_num) pr_116880853 (by norm_num) (by decide +kernel)
  have d1546150189 := force h hexp pr_463 d463
    (by norm_num) pr_1546150189 (by norm_num) (by decide +kernel)
  refine close h (l := 11) (by norm_num) (by norm_num) e11 hexp
    {15797, 463, 23, 5479, 1277, 18701, 34607, 36751837, 67, 89, 116880853, 1546150189} ?_ (by decide)
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨pr_15797, d15797, by norm_num⟩, ⟨pr_463, d463, by norm_num⟩, ⟨pr_23, d23, by norm_num⟩, ⟨pr_5479, d5479, by norm_num⟩, ⟨pr_1277, d1277, by norm_num⟩, ⟨pr_18701, d18701, by norm_num⟩, ⟨pr_34607, d34607, by norm_num⟩, ⟨pr_36751837, d36751837, by norm_num⟩, ⟨pr_67, d67, by norm_num⟩, ⟨pr_89, d89, by norm_num⟩, ⟨pr_116880853, d116880853, by norm_num⟩, ⟨pr_1546150189, d1546150189, by norm_num⟩]

/-- Exponent ten, `q = 15797`; the primes `3` and `2633` divide `15797 + 1`. -/
private lemma ten_15797 {N : ℕ} (h : OddPerfect N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ 15797 → N.factorization p = 10) (h11 : 11 ∣ N)
    (e11 : N.factorization 11 = 10) (d3 : 3 ∣ N) (d2633 : 2633 ∣ N) : False := by
  have d1806113 := force h hexp pr_11 h11
    (by norm_num) pr_1806113 (by norm_num) (by decide +kernel)
  have d199 := force h hexp pr_1806113 d1806113
    (by norm_num) pr_199 (by norm_num) (by decide +kernel)
  have d23 := force h hexp pr_3 d3
    (by norm_num) pr_23 (by norm_num) (by decide +kernel)
  have d3851 := force h hexp pr_3 d3
    (by norm_num) pr_3851 (by norm_num) (by decide +kernel)
  have d2113 := force h hexp pr_2633 d2633
    (by norm_num) pr_2113 (by norm_num) (by decide +kernel)
  have d683 := force h hexp pr_2113 d2113
    (by norm_num) pr_683 (by norm_num) (by decide +kernel)
  have d7459 := force h hexp pr_2113 d2113
    (by norm_num) pr_7459 (by norm_num) (by decide +kernel)
  have d603510799 := force h hexp pr_3851 d3851
    (by norm_num) pr_603510799 (by norm_num) (by decide +kernel)
  have d947684519 := force h hexp pr_2633 d2633
    (by norm_num) pr_947684519 (by norm_num) (by decide +kernel)
  have d9620773471 := force h hexp pr_2633 d2633
    (by norm_num) pr_9620773471 (by norm_num) (by decide +kernel)
  have d75449464927 := force h hexp pr_199 d199
    (by norm_num) pr_75449464927 (by norm_num) (by decide +kernel)
  have d117942356533 := force h hexp pr_199 d199
    (by norm_num) pr_117942356533 (by norm_num) (by decide +kernel)
  refine close h (l := 11) (by norm_num) (by norm_num) e11 hexp
    {1806113, 199, 23, 3851, 2113, 683, 7459, 603510799, 947684519, 9620773471, 75449464927, 117942356533} ?_ (by decide)
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨pr_1806113, d1806113, by norm_num⟩, ⟨pr_199, d199, by norm_num⟩, ⟨pr_23, d23, by norm_num⟩, ⟨pr_3851, d3851, by norm_num⟩, ⟨pr_2113, d2113, by norm_num⟩, ⟨pr_683, d683, by norm_num⟩, ⟨pr_7459, d7459, by norm_num⟩, ⟨pr_603510799, d603510799, by norm_num⟩, ⟨pr_947684519, d947684519, by norm_num⟩, ⟨pr_9620773471, d9620773471, by norm_num⟩, ⟨pr_75449464927, d75449464927, by norm_num⟩, ⟨pr_117942356533, d117942356533, by norm_num⟩]

/-- Exponent twelve, `13` ordinary, `q ∉ {53, 8346157}`. -/
private lemma twelve_gen {N q : ℕ} (h : OddPerfect N) (hq4 : q % 4 = 1)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 12) (h13 : 13 ∣ N)
    (e13 : N.factorization 13 = 12) (hc : q ≠ 13) (ha : q ≠ 53) (hb : q ≠ 8346157) : False := by
  have d53 := force h hexp pr_13 h13
    (Ne.symm hc) pr_53 (by norm_num) (by decide +kernel)
  have d264031 := force h hexp pr_13 h13
    (Ne.symm hc) pr_264031 (by norm_num) (by decide +kernel)
  have d1803647 := force h hexp pr_13 h13
    (Ne.symm hc) pr_1803647 (by norm_num) (by decide +kernel)
  have d131 := force h hexp pr_1803647 d1803647
    (ne_of_mod_four hq4 (by norm_num)) pr_131 (by norm_num) (by decide +kernel)
  have d55816123897 := force h hexp pr_1803647 d1803647
    (ne_of_mod_four hq4 (by norm_num)) pr_55816123897 (by norm_num) (by decide +kernel)
  have d79 := force h hexp pr_131 d131
    (ne_of_mod_four hq4 (by norm_num)) pr_79 (by norm_num) (by decide +kernel)
  have d8346157 := force h hexp pr_79 d79
    (ne_of_mod_four hq4 (by norm_num)) pr_8346157 (by norm_num) (by decide +kernel)
  have d551604349222681 := force h hexp pr_79 d79
    (ne_of_mod_four hq4 (by norm_num)) pr_551604349222681 (by norm_num) (by decide +kernel)
  have d3297113 := force h hexp pr_53 d53
    (Ne.symm ha) pr_3297113 (by norm_num) (by decide +kernel)
  have d11681692691969 := force h hexp pr_53 d53
    (Ne.symm ha) pr_11681692691969 (by norm_num) (by decide +kernel)
  have d2128503313 := force h hexp pr_8346157 d8346157
    (Ne.symm hb) pr_2128503313 (by norm_num) (by decide +kernel)
  have d2497868257 := force h hexp pr_8346157 d8346157
    (Ne.symm hb) pr_2497868257 (by norm_num) (by decide +kernel)
  have d2767761413 := force h hexp pr_8346157 d8346157
    (Ne.symm hb) pr_2767761413 (by norm_num) (by decide +kernel)
  have d25061845458479893445539 := force h hexp pr_131 d131
    (ne_of_mod_four hq4 (by norm_num)) pr_25061845458479893445539 (by norm_num) (by decide +kernel)
  refine close h (l := 13) (by norm_num) (by norm_num) e13 hexp
    {53, 264031, 1803647, 131, 55816123897, 79, 8346157, 551604349222681, 3297113, 11681692691969, 2128503313, 2497868257, 2767761413, 25061845458479893445539} ?_ (by decide)
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨pr_53, d53, by norm_num⟩, ⟨pr_264031, d264031, by norm_num⟩, ⟨pr_1803647, d1803647, by norm_num⟩, ⟨pr_131, d131, by norm_num⟩, ⟨pr_55816123897, d55816123897, by norm_num⟩, ⟨pr_79, d79, by norm_num⟩, ⟨pr_8346157, d8346157, by norm_num⟩, ⟨pr_551604349222681, d551604349222681, by norm_num⟩, ⟨pr_3297113, d3297113, by norm_num⟩, ⟨pr_11681692691969, d11681692691969, by norm_num⟩, ⟨pr_2128503313, d2128503313, by norm_num⟩, ⟨pr_2497868257, d2497868257, by norm_num⟩, ⟨pr_2767761413, d2767761413, by norm_num⟩, ⟨pr_25061845458479893445539, d25061845458479893445539, by norm_num⟩]

/-- Exponent twelve, `13` ordinary, `q = 53`. -/
private lemma twelve_53 {N : ℕ} (h : OddPerfect N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ 53 → N.factorization p = 12) (h13 : 13 ∣ N)
    (e13 : N.factorization 13 = 12) : False := by
  have d264031 := force h hexp pr_13 h13
    (by norm_num) pr_264031 (by norm_num) (by decide +kernel)
  have d1803647 := force h hexp pr_13 h13
    (by norm_num) pr_1803647 (by norm_num) (by decide +kernel)
  have d131 := force h hexp pr_1803647 d1803647
    (by norm_num) pr_131 (by norm_num) (by decide +kernel)
  have d55816123897 := force h hexp pr_1803647 d1803647
    (by norm_num) pr_55816123897 (by norm_num) (by decide +kernel)
  have d79 := force h hexp pr_131 d131
    (by norm_num) pr_79 (by norm_num) (by decide +kernel)
  have d8346157 := force h hexp pr_79 d79
    (by norm_num) pr_8346157 (by norm_num) (by decide +kernel)
  have d551604349222681 := force h hexp pr_79 d79
    (by norm_num) pr_551604349222681 (by norm_num) (by decide +kernel)
  have d2128503313 := force h hexp pr_8346157 d8346157
    (by norm_num) pr_2128503313 (by norm_num) (by decide +kernel)
  have d2497868257 := force h hexp pr_8346157 d8346157
    (by norm_num) pr_2497868257 (by norm_num) (by decide +kernel)
  have d2767761413 := force h hexp pr_8346157 d8346157
    (by norm_num) pr_2767761413 (by norm_num) (by decide +kernel)
  have d2939 := force h hexp pr_2767761413 d2767761413
    (by norm_num) pr_2939 (by norm_num) (by decide +kernel)
  have d1334737 := force h hexp pr_2767761413 d2767761413
    (by norm_num) pr_1334737 (by norm_num) (by decide +kernel)
  have d1093 := force h hexp pr_55816123897 d55816123897
    (by norm_num) pr_1093 (by norm_num) (by decide +kernel)
  have d937 := force h hexp pr_1093 d1093
    (by norm_num) pr_937 (by norm_num) (by decide +kernel)
  refine close h (l := 13) (by norm_num) (by norm_num) e13 hexp
    {264031, 1803647, 131, 55816123897, 79, 8346157, 551604349222681, 2128503313, 2497868257, 2767761413, 2939, 1334737, 1093, 937} ?_ (by decide)
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨pr_264031, d264031, by norm_num⟩, ⟨pr_1803647, d1803647, by norm_num⟩, ⟨pr_131, d131, by norm_num⟩, ⟨pr_55816123897, d55816123897, by norm_num⟩, ⟨pr_79, d79, by norm_num⟩, ⟨pr_8346157, d8346157, by norm_num⟩, ⟨pr_551604349222681, d551604349222681, by norm_num⟩, ⟨pr_2128503313, d2128503313, by norm_num⟩, ⟨pr_2497868257, d2497868257, by norm_num⟩, ⟨pr_2767761413, d2767761413, by norm_num⟩, ⟨pr_2939, d2939, by norm_num⟩, ⟨pr_1334737, d1334737, by norm_num⟩, ⟨pr_1093, d1093, by norm_num⟩, ⟨pr_937, d937, by norm_num⟩]

/-- Exponent twelve, `13` ordinary, `q = 8346157`. -/
private lemma twelve_8346157 {N : ℕ} (h : OddPerfect N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ 8346157 → N.factorization p = 12) (h13 : 13 ∣ N)
    (e13 : N.factorization 13 = 12) : False := by
  have d53 := force h hexp pr_13 h13
    (by norm_num) pr_53 (by norm_num) (by decide +kernel)
  have d264031 := force h hexp pr_13 h13
    (by norm_num) pr_264031 (by norm_num) (by decide +kernel)
  have d1803647 := force h hexp pr_13 h13
    (by norm_num) pr_1803647 (by norm_num) (by decide +kernel)
  have d131 := force h hexp pr_1803647 d1803647
    (by norm_num) pr_131 (by norm_num) (by decide +kernel)
  have d55816123897 := force h hexp pr_1803647 d1803647
    (by norm_num) pr_55816123897 (by norm_num) (by decide +kernel)
  have d79 := force h hexp pr_131 d131
    (by norm_num) pr_79 (by norm_num) (by decide +kernel)
  have d551604349222681 := force h hexp pr_79 d79
    (by norm_num) pr_551604349222681 (by norm_num) (by decide +kernel)
  have d3297113 := force h hexp pr_53 d53
    (by norm_num) pr_3297113 (by norm_num) (by decide +kernel)
  have d11681692691969 := force h hexp pr_53 d53
    (by norm_num) pr_11681692691969 (by norm_num) (by decide +kernel)
  have d1093 := force h hexp pr_55816123897 d55816123897
    (by norm_num) pr_1093 (by norm_num) (by decide +kernel)
  have d937 := force h hexp pr_1093 d1093
    (by norm_num) pr_937 (by norm_num) (by decide +kernel)
  have d599 := force h hexp pr_937 d937
    (by norm_num) pr_599 (by norm_num) (by decide +kernel)
  have d58782569 := force h hexp pr_1093 d1093
    (by norm_num) pr_58782569 (by norm_num) (by decide +kernel)
  have d8209505981 := force h hexp pr_1093 d1093
    (by norm_num) pr_8209505981 (by norm_num) (by decide +kernel)
  refine close h (l := 13) (by norm_num) (by norm_num) e13 hexp
    {53, 264031, 1803647, 131, 55816123897, 79, 551604349222681, 3297113, 11681692691969, 1093, 937, 599, 58782569, 8209505981} ?_ (by decide)
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨pr_53, d53, by norm_num⟩, ⟨pr_264031, d264031, by norm_num⟩, ⟨pr_1803647, d1803647, by norm_num⟩, ⟨pr_131, d131, by norm_num⟩, ⟨pr_55816123897, d55816123897, by norm_num⟩, ⟨pr_79, d79, by norm_num⟩, ⟨pr_551604349222681, d551604349222681, by norm_num⟩, ⟨pr_3297113, d3297113, by norm_num⟩, ⟨pr_11681692691969, d11681692691969, by norm_num⟩, ⟨pr_1093, d1093, by norm_num⟩, ⟨pr_937, d937, by norm_num⟩, ⟨pr_599, d599, by norm_num⟩, ⟨pr_58782569, d58782569, by norm_num⟩, ⟨pr_8209505981, d8209505981, by norm_num⟩]

/-! ## Main theorems -/

/-- McDaniel and Hagis (1975): in an odd perfect number the exponents of the primes other
than the special prime cannot all equal ten. -/
theorem not_all_exponents_ten {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 10) : False := by
  by_cases h11 : 11 ∣ N
  · have hq4 := (special_mod_four h hq hodd).1
    have e11 : N.factorization 11 = 10 :=
      hexp 11 (Nat.mem_primeFactors.mpr ⟨by norm_num, h11, h.ne_zero⟩)
        (ne_of_mod_four hq4 (by norm_num))
    by_cases ha : q = 15797
    · subst ha
      obtain ⟨d3, -⟩ := prime_dvd_of_dvd_succ_special h hq hodd (r := 3) (by norm_num)
        (by norm_num) (by norm_num)
      obtain ⟨d2633, -⟩ := prime_dvd_of_dvd_succ_special h hq hodd (r := 2633) pr_2633
        (by norm_num) (by norm_num)
      exact ten_15797 h hexp h11 e11 d3 d2633
    by_cases hb : q = 1806113
    · subst hb
      exact ten_1806113 h hexp h11 e11
    exact ten_gen h hq4 hexp h11 e11 ha hb
  · exact not_all_exponents_eq_pred_prime h hq hodd (l := 11) (by norm_num) (by norm_num) h11 hexp

/-- Cohen and Williams (1985): in an odd perfect number the exponents of the primes other
than the special prime cannot all equal twelve. -/
theorem not_all_exponents_twelve {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 12) : False := by
  by_cases h13 : 13 ∣ N
  · by_cases hc : q = 13
    · subst hc
      exact not_all_exponents_pred_of_special h hq hodd hexp
    have hq4 := (special_mod_four h hq hodd).1
    have e13 : N.factorization 13 = 12 :=
      hexp 13 (Nat.mem_primeFactors.mpr ⟨by norm_num, h13, h.ne_zero⟩) (Ne.symm hc)
    by_cases ha : q = 53
    · subst ha
      exact twelve_53 h hexp h13 e13
    by_cases hb : q = 8346157
    · subst hb
      exact twelve_8346157 h hexp h13 e13
    exact twelve_gen h hq4 hexp h13 e13 hc ha hb
  · exact not_all_exponents_eq_pred_prime h hq hodd (l := 13) (by norm_num) (by norm_num) h13 hexp

end OddPerfect

#print axioms OddPerfect.not_all_exponents_pred_of_special
#print axioms OddPerfect.card_erase_special_le
#print axioms OddPerfect.not_all_exponents_ten
#print axioms OddPerfect.not_all_exponents_twelve
