import OddPerfect.EqualExponentsBound
import OddPerfect.UpperBound

/-!
# Bounded exponents with indices that are powers of one prime

Let `l` be an odd prime and `N` an odd perfect number with special prime `q` such that every
ordinary exponent `e_p` (that of a prime `p ≠ q`) has `e_p + 1 = l ^ γ_p` with `γ_p ≥ 1`, and
`e_p ≤ E`. Then `ω(N) ≤ E ^ 2 + 2 E + 3`, hence `N < 2 ^ (4 ^ (E ^ 2 + 2 E + 3))`.

The argument is Yamada's for equal exponents (Colloq. Math. 103 (2005), Theorem 1.1, see
`OddPerfect/EqualExponentsBound.lean`), run with varying exponents.

* Kanold's congruence argument (`false_of_special_of_prime_pow_index`): `l` is not the special
  prime. With `l ∣ N` (`dvd_of_succ_eq_pow`) the prime `l` is ordinary and `v_l(N) ≤ E`.
* The ordinary primes `≡ 1 (mod l)` each contribute at least one factor `l` to `σ(N)`, so there
  are at most `E` of them; each receives from at most `E` senders (`card_feeders_le`).
* Every ordinary prime `p ≠ l` with `p ≢ 1 (mod l)` such that no ordinary prime `≡ 1 (mod l)`
  divides `σ(p ^ e_p)` has `σ(p ^ e_p)` a power of `q`, the full power `p ^ e_p`
  divides `σ(q ^ α)`, and the lemma of Dandapat, Hunsucker and Pomerance with lifting the
  exponent gives `p ^ (l - 2) ∣ α + 1`. Counting divisors of `α + 1` (Bang's theorem at `q`)
  gives `2 ^ (u + 1) ≤ E ^ 2 + E + u + 3` for the number `u` of such primes, so `u ≤ E + 1`.

Whether this result is new was not verified against the literature. The sources checked,
Fletcher, Nielsen and Ochem (Math. Comp. 81 (2012), Theorem 3) and Yamada (arXiv 1609.08795,
Theorem 1), bound the smallest prime factor for the wider family where every ordinary index has
a prime factor in a fixed finite set; they do not bound the number of prime factors.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- A positive number whose prime factors are all `≡ 1 (mod l)` is `≡ 1 (mod l)`. -/
private lemma mod_eq_one_of_prime_factors' {l : ℕ} (hl : 1 < l) (n : ℕ) (hn : n ≠ 0)
    (ht : ∀ t, t.Prime → t ∣ n → t % l = 1) : n % l = 1 := by
  induction n using induction_on_primes with
  | zero => exact absurd rfl hn
  | one => exact Nat.mod_eq_of_lt hl
  | prime_mul p a hp ih =>
    have ha : a ≠ 0 := by rintro rfl; simp at hn
    rw [Nat.mul_mod, ht p hp (dvd_mul_right p a),
      ih ha fun t htp htd => ht t htp (htd.mul_left p), Nat.one_mul, Nat.mod_eq_of_lt hl]

/-- `x ^ (l ^ γ) = x` in `ZMod l` (Fermat). -/
private lemma zmod_pow_pow_card' {l : ℕ} [Fact l.Prime] (x : ZMod l) (γ : ℕ) :
    x ^ (l ^ γ) = x := by
  induction γ with
  | zero => simp
  | succ γ ih => rw [pow_succ, pow_mul, ih, ZMod.pow_card]

/-- Kanold, prime power indices. If every exponent `e_p` of the odd perfect number `N` at a
prime `p ≠ l` has `e_p + 1` a power of the prime `l`, then `l` is not the special prime. Write
`N = l ^ k Y` with `Y = ∏ p ^ e_p`. Every prime factor of `X = ∏ σ(p ^ e_p)` is `l` or
`≡ 1 (mod l)`, so the part `U` of `X` prime to `l` is `≡ 1 (mod l)`; removing the powers of `l`
from `σ(l ^ k) X = 2 l ^ k Y` gives `σ(l ^ k) U = 2 Y`, which reads `1 = 2` modulo `l` since
`p ^ (l ^ γ) ≡ p`. -/
theorem false_of_special_of_prime_pow_index {N l : ℕ} (h : OddPerfect N) (hl : l.Prime)
    (hodd : Odd (N.factorization l))
    (hidx : ∀ p ∈ N.primeFactors, p ≠ l → ∃ γ, N.factorization p + 1 = l ^ γ) : False := by
  have : Fact l.Prime := ⟨hl⟩
  have hN0 := h.ne_zero
  have hlN : l ∈ N.primeFactors := Nat.support_factorization N ▸
    Finsupp.mem_support_iff.mpr (by rintro h0; simp [h0] at hodd)
  set k := N.factorization l with hk
  set P := N.primeFactors.erase l with hP
  have hPp : ∀ p ∈ P, p.Prime ∧ p ≠ l ∧ ∃ γ, N.factorization p + 1 = l ^ γ := fun p hp => by
    obtain ⟨hpl, hpN⟩ := Finset.mem_erase.mp hp
    exact ⟨Nat.prime_of_mem_primeFactors hpN, hpl, hidx p hpN hpl⟩
  set X := ∏ p ∈ P, σ 1 (p ^ N.factorization p) with hX
  set Y := ∏ p ∈ P, p ^ N.factorization p with hY
  have hNprod : N = l ^ k * Y := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hN0]
    rw [Finsupp.prod, Nat.support_factorization, ← Finset.mul_prod_erase _ _ hlN]
  have hσprod : σ 1 N = σ 1 (l ^ k) * X := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ hN0, Finsupp.prod,
      Nat.support_factorization, ← Finset.mul_prod_erase _ _ hlN]
  have hE : σ 1 (l ^ k) * X = 2 * (l ^ k * Y) := by
    rw [← hσprod, ← hNprod, h.sigma_eq]
  have hX0 : X ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp =>
    (sigma_pos 1 _ (pow_pos (hPp p hp).1.pos _).ne').ne'
  set U := ordCompl[l] X with hU
  have hUmod : U % l = 1 := by
    refine mod_eq_one_of_prime_factors' hl.one_lt U (Nat.ordCompl_pos l hX0).ne'
      fun t ht htU => ?_
    have htX : t ∣ X := htU.trans (Nat.ordCompl_dvd X l)
    obtain ⟨p, hp, htp⟩ := (Prime.dvd_finsetProd_iff ht.prime _).mp htX
    obtain ⟨γ, hγ⟩ := (hPp p hp).2.2
    rcases prime_dvd_sigma_of_succ_eq_pow (hPp p hp).1 ht hl hγ htp with rfl | h1
    · exact absurd htU (Nat.not_dvd_ordCompl ht hX0)
    · exact h1
  have hlY : ¬ l ∣ Y := by
    intro hd
    obtain ⟨p, hp, hlp⟩ := (Prime.dvd_finsetProd_iff hl.prime _).mp hd
    exact (hPp p hp).2.1
      ((Nat.prime_dvd_prime_iff_eq hl (hPp p hp).1).mp (hl.dvd_of_dvd_pow hlp)).symm
  have hlσ : ¬ l ∣ σ 1 (l ^ k) := fun hd =>
    hl.one_lt.ne' ((Nat.coprime_comm.mp (coprime_sigma_prime_pow hl k)).eq_one_of_dvd hd)
  have hl2 : ¬ l ∣ 2 := fun hd => by
    have h2 : l = 2 := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp hd
    exact h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hlN)
  have hcompl : ∀ {n : ℕ}, ¬ l ∣ n → ordCompl[l] n = n := fun hn => by
    rw [Nat.factorization_eq_zero_of_not_dvd hn, pow_zero, Nat.div_one]
  have hE' : σ 1 (l ^ k) * U = 2 * Y := by
    have := congrArg (fun n => ordCompl[l] n) hE
    simp only [Nat.ordCompl_mul, hcompl hlσ, hcompl hl2, hcompl hlY,
      Nat.ordCompl_self_pow hl, one_mul] at this
    rw [← hU] at this
    exact this
  have hc := congrArg (fun n : ℕ => (n : ZMod l)) hE'
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hc
  have hσ1 : ((σ 1 (l ^ k) : ℕ) : ZMod l) = 1 := by
    rw [sigma_one_apply_prime_pow hl, Nat.cast_sum, Finset.sum_range_succ']
    simp
  have hU1 : ((U : ℕ) : ZMod l) = 1 := by
    rw [← ZMod.natCast_mod, hUmod, Nat.cast_one]
  have hY1 : ((Y : ℕ) : ZMod l) = 1 := by
    rw [hY, Nat.cast_prod]
    refine Finset.prod_eq_one fun p hp => ?_
    obtain ⟨hpp, hpl, γ, hγ⟩ := hPp p hp
    have hp0 : ((p : ℕ) : ZMod l) ≠ 0 := fun h0 =>
      hpl ((Nat.prime_dvd_prime_iff_eq hl hpp).mp ((ZMod.natCast_eq_zero_iff p l).mp h0)).symm
    have h1 : ((p : ℕ) : ZMod l) ^ N.factorization p * (p : ZMod l) = 1 * (p : ZMod l) := by
      rw [← pow_succ, hγ, zmod_pow_pow_card', one_mul]
    rw [Nat.cast_pow]
    exact mul_right_cancel₀ hp0 h1
  rw [hσ1, hU1, hY1] at hc
  rw [mul_one, mul_one, ← one_add_one_eq_two] at hc
  exact one_ne_zero (left_eq_add.mp hc)

/-- The ledger at a prime fed only by the special prime, prime power indices. If every
ordinary exponent `e_r` has `e_r + 1` a power of the prime `l`, and the ordinary prime factor
`p ≠ l` is `≢ 1 (mod l)`, then no ordinary component feeds `p`, so `v_p(σ(q ^ α)) = e_p`. -/
theorem padicValNat_sigma_special_eq_of_prime_pow_index {N q l p : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, N.factorization p + 1 = l ^ γ)
    (hp : p ∈ N.primeFactors) (hpq : p ≠ q) (hpl : p ≠ l) (hp1 : p % l ≠ 1) :
    padicValNat p (σ 1 (q ^ N.factorization q)) = N.factorization p := by
  have hqN : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq,
    Nat.dvd_of_factorization_pos (by obtain ⟨k, hk⟩ := hodd; omega), h.ne_zero⟩
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hp)
  rw [factorization_eq_sum_erase h.perfect hpp hp2 (N := N), Finset.sum_eq_single q]
  · intro r hr hrq
    obtain ⟨-, hrN⟩ := Finset.mem_erase.mp hr
    rw [Nat.padicValNat_def]
    refine padicValNat.eq_zero_of_not_dvd fun hd => ?_
    obtain ⟨γ, hγ⟩ := hidx r hrN hrq
    rcases prime_dvd_sigma_of_succ_eq_pow (Nat.prime_of_mem_primeFactors hrN) hpp hl hγ hd with
      h1 | h1
    · exact hpl h1
    · exact hp1 h1
  · intro hqn
    exact absurd (Finset.mem_erase.mpr ⟨hpq.symm, hqN⟩) hqn

/-- `n ^ 2 + 2 n + 5 < 2 ^ (n + 3)`. -/
private lemma sq_add_lt_two_pow (n : ℕ) : n ^ 2 + 2 * n + 5 < 2 ^ (n + 3) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h1 : n < 2 ^ n := Nat.lt_two_pow_self
    have h2 : 2 ^ (n + 1 + 3) = 2 * 2 ^ (n + 3) := by ring
    have h3 : 2 ^ (n + 3) = 8 * 2 ^ n := by ring
    rw [h2]
    nlinarith

/-- Bounded exponents with indices that are powers of one odd prime `l`. If every ordinary
exponent `e_p` of the odd perfect number `N` (special prime `q`) satisfies
`e_p + 1 = l ^ γ_p` with `γ_p ≥ 1` and `e_p ≤ E`, then `N` has at most `E ^ 2 + 2 E + 3`
distinct prime factors. The proof is Yamada's for equal exponents (Colloq. Math. 103 (2005),
Theorem 1.1) with varying exponents; see the module docstring. Whether this result is new was
not verified against the literature. -/
theorem card_primeFactors_le_of_prime_pow_index {N q l E : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, 1 ≤ γ ∧ N.factorization p + 1 = l ^ γ)
    (hE : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p ≤ E) :
    N.primeFactors.card ≤ E ^ 2 + 2 * E + 3 := by
  classical
  have hN0 := h.ne_zero
  have hqN : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq,
    Nat.dvd_of_factorization_pos (by obtain ⟨k, hk⟩ := hodd; omega), hN0⟩
  have hpf2 : ∀ p ∈ N.primeFactors, p ≠ 2 := fun p hp h2 =>
    h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hp)
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have hidx' : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, N.factorization p + 1 = l ^ γ :=
    fun p hp hpq => by obtain ⟨γ, -, hγ⟩ := hidx p hp hpq; exact ⟨γ, hγ⟩
  -- `l` is an ordinary prime factor
  have hlN : l ∣ N := dvd_of_succ_eq_pow h hq hodd hl hl2 hidx'
  have hlmem : l ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hl, hlN, hN0⟩
  have hlq : l ≠ q := by
    rintro rfl
    exact false_of_special_of_prime_pow_index h hl hodd hidx'
  have hlE := hE l hlmem hlq
  -- the ordinary primes `≡ 1 (mod l)`
  set S := N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1) with hS
  have hSle : S.card ≤ E := by
    have hsum := sum_padicValNat_succ_le h.perfect hl hl2
    have : Fact l.Prime := ⟨hl⟩
    rw [Finset.card_eq_sum_ones]
    calc ∑ p ∈ S, 1 ≤ ∑ p ∈ S, padicValNat l (N.factorization p + 1) := by
          refine Finset.sum_le_sum fun p hp => ?_
          obtain ⟨hpN, hpq, -⟩ := Finset.mem_filter.mp hp
          obtain ⟨γ, hγ1, hγ⟩ := hidx p hpN hpq
          rw [Nat.padicValNat_def]
          exact one_le_padicValNat_of_dvd (by omega)
            (hγ ▸ dvd_pow_self l (by omega : γ ≠ 0))
      _ ≤ ∑ p ∈ N.primeFactors.filter (fun p => p % l = 1),
            padicValNat l (N.factorization p + 1) :=
          Finset.sum_le_sum_of_subset fun p hp => by
            obtain ⟨hpN, -, h1⟩ := Finset.mem_filter.mp hp
            exact Finset.mem_filter.mpr ⟨hpN, h1⟩
      _ ≤ E := hsum.trans hlE
  -- feeders
  set A : ℕ → Finset ℕ := fun s =>
    (N.primeFactors.erase s).filter (fun p => s ∣ σ 1 (p ^ N.factorization p)) with hA
  have hAle : ∀ s ∈ S, (A s).card ≤ E := fun s hs => by
    obtain ⟨hsN, hsq, -⟩ := Finset.mem_filter.mp hs
    exact (card_feeders_le h.perfect (Nat.prime_of_mem_primeFactors hsN) (hpf2 s hsN)).trans
      (hE s hsN hsq)
  -- the rest
  set O := N.primeFactors.erase q with hO
  have hcardN : N.primeFactors.card = O.card + 1 := (Finset.card_erase_add_one hqN).symm
  set U := O.filter (fun p => p ≠ l ∧ p % l ≠ 1 ∧
    ∀ s ∈ S, ¬ s ∣ σ 1 (p ^ N.factorization p)) with hU
  have hcover : O ⊆ S ∪ S.biUnion A ∪ insert l U := by
    intro p hp
    obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hp
    by_cases h1 : p % l = 1
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hpN, hpq, h1⟩))
    by_cases hfed : ∃ s ∈ S, s ∣ σ 1 (p ^ N.factorization p)
    · obtain ⟨s, hs, hsd⟩ := hfed
      have hps : p ≠ s := by
        rintro rfl
        exact h1 (Finset.mem_filter.mp hs).2.2
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨s, hs, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hps, hpN⟩, hsd⟩⟩))
    push Not at hfed
    refine Finset.mem_union_right _ ?_
    by_cases hpl : p = l
    · exact hpl ▸ Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hp, hpl, h1, hfed⟩)
  have hOle : O.card ≤ E + E * E + (U.card + 1) := by
    calc O.card ≤ _ := Finset.card_le_card hcover
      _ ≤ (S ∪ S.biUnion A).card + (insert l U).card := Finset.card_union_le _ _
      _ ≤ (S.card + (S.biUnion A).card) + (U.card + 1) :=
          Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_insert_le _ _)
      _ ≤ E + E * E + (U.card + 1) := by
          have := Finset.card_biUnion_le_card_mul S A E hAle
          have : S.card * E ≤ E * E := Nat.mul_le_mul_right E hSle
          omega
  -- each element of `U` gives `p ^ (l - 2) ∣ α + 1`
  have hUprop : ∀ p ∈ U, p.Prime ∧ p ≠ 2 ∧ p ^ (l - 2) ∣ N.factorization q + 1 := by
    intro p hp
    obtain ⟨hpO, hpl, hp1, hfed⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hpO
    have hpp := Nat.prime_of_mem_primeFactors hpN
    have hp2 := hpf2 p hpN
    obtain ⟨γ, hγ1, hγ⟩ := hidx p hpN hpq
    have hσ0 : σ 1 (p ^ N.factorization p) ≠ 0 :=
      (sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)).ne'
    -- `σ(p ^ e_p)` is a power of `q`
    have hall : ∀ {t : ℕ}, t.Prime → t ∣ σ 1 (p ^ N.factorization p) → t = q := by
      intro t ht htd
      rcases prime_dvd_sigma_of_succ_eq_pow hpp ht hl hγ htd with rfl | ht1
      · exfalso
        rcases (prime_dvd_sigma_prime_pow hpp ht htd).2 with ⟨h1, -⟩ | ⟨ho1, hod, hot⟩
        · exact hp1 h1
        · rw [hγ] at hod
          obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow ht).mp hod
          have hj0 : j ≠ 0 := by rintro rfl; rw [hj, pow_zero] at ho1; omega
          rw [hj] at hot
          have := Nat.le_of_dvd (by omega) ((dvd_pow_self t hj0).trans hot)
          omega
      · by_contra htq
        have ht2 : t ≠ 2 := by
          rintro rfl
          rw [Nat.mod_eq_of_lt (by omega)] at ht1
          omega
        have htN := OPNStarter.force_prime h.perfect hpp rfl ht ht2 htd
        exact hfed t (Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨ht, htN, hN0⟩, htq, ht1⟩)
          htd
    have hc := Nat.eq_prime_pow_of_unique_prime_dvd hσ0 hall
    -- `e_p = 2 β` with `l - 1 ≤ 2 β`
    have hle : l ≤ l ^ γ := Nat.le_self_pow (by omega) l
    obtain ⟨β, hβ⟩ : ∃ β, N.factorization p = 2 * β := by
      have hodd' : Odd (l ^ γ) := (hl.odd_of_ne_two hl2).pow
      obtain ⟨m, hm⟩ := hodd'
      exact ⟨m, by omega⟩
    have hv := padicValNat_sigma_special_eq_of_prime_pow_index h hq hodd hl hidx' hpN hpq hpl hp1
    rw [hβ] at hc hv
    have hdvd := pow_dvd_succ_of_sigma_eq_pow hpp hp2 hq hpq (by omega) hc hv
    exact ⟨hpp, hp2, (pow_dvd_pow p (by omega)).trans hdvd⟩
  have hτ := two_mul_pow_le_card_divisors U (n := N.factorization q + 1) (b := l - 2)
    (by omega) (by obtain ⟨k, hk⟩ := hodd; exact ⟨k + 1, by omega⟩) (by omega) hUprop
  have hτ' := card_divisors_succ_le h hq hodd
  rw [← hO] at hτ'
  have h2u : 2 ^ U.card ≤ (l - 2 + 1) ^ U.card := Nat.pow_le_pow_left (by omega) _
  have hu : U.card ≤ E + 1 := by
    by_contra hu
    obtain ⟨n, hn⟩ : ∃ n, U.card = n + 2 := ⟨U.card - 2, by omega⟩
    have hEn : E ≤ n := by omega
    have hEE : E * E ≤ n * n := Nat.mul_le_mul hEn hEn
    have key := sq_add_lt_two_pow n
    have h22 : 2 * 2 ^ (n + 2) = 2 ^ (n + 3) := by ring
    rw [hn] at h2u hτ hOle
    have : n ^ 2 = n * n := by ring
    omega
  have : E ^ 2 = E * E := by ring
  omega

/-- The size bound: under the hypotheses of `card_primeFactors_le_of_prime_pow_index`,
`N < 2 ^ (4 ^ (E ^ 2 + 2 E + 3))` (Nielsen's bound `N < 2 ^ (4 ^ ω(N))`). -/
theorem lt_two_pow_four_pow_of_prime_pow_index {N q l E : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, 1 ≤ γ ∧ N.factorization p + 1 = l ^ γ)
    (hE : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p ≤ E) :
    N < 2 ^ (4 ^ (E ^ 2 + 2 * E + 3)) :=
  lt_of_lt_of_le (lt_two_pow_four_pow h)
    (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num)
      (card_primeFactors_le_of_prime_pow_index h hq hodd hl hl2 hidx hE)))

end OddPerfect

#print axioms OddPerfect.false_of_special_of_prime_pow_index
#print axioms OddPerfect.padicValNat_sigma_special_eq_of_prime_pow_index
#print axioms OddPerfect.card_primeFactors_le_of_prime_pow_index
#print axioms OddPerfect.lt_two_pow_four_pow_of_prime_pow_index
