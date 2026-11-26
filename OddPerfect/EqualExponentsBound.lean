import OddPerfect.KanoldGeneral

/-!
# Yamada's bound on the number of prime factors in the equal exponent case

T. Yamada, "Odd perfect numbers of a special form", Colloq. Math. 103 (2005), 303 to 307,
Theorem 1.1: if `N = q ^ α ∏ p_i ^ (2 β)` is an odd perfect number (all ordinary exponents
equal to `2 β`), then `ω(N) ≤ 4 β ^ 2 + 2 β + 3`. This file proves that statement. The
argument follows the paper; it needs no Diophantine input.

* `2 β + 1 = l` prime. Kanold: `l ∣ N` and `l` is not the special prime
  (`false_of_special_succ_eq_pow`). The ordinary primes `p` with `σ(p ^ (2 β))` not a power of
  `q` number at most `2 β (2 β + 1)` (`card_not_special_pow_le`). For the others, `p ≠ l`,
  the full power `p ^ (2 β)` divides `σ(q ^ α)`; since `σ(p ^ (2 β)) = q ^ c` forces
  `v_p(q ^ c - 1) = 1` (Dandapat, Hunsucker and Pomerance), lifting the exponent gives
  `p ^ (2 β - 1) ∣ α + 1`. So `α + 1` has at least `2 (2 β) ^ u` divisors, `u` the number of
  such `p`, and Bang's theorem turns each divisor `d ≥ 3` into its own ordinary prime. This
  forces `u ≤ 1` when `β ≥ 2`; `β = 1` is Steuerwald's theorem.
* `2 β + 1` not prime. If every prime factor of `2 β + 1` is `q`, Kanold's congruence argument
  gives a contradiction. Otherwise pick a prime `l ∣ 2 β + 1`, `l ≠ q`. Bang's theorem for the
  two orders `l` and `2 β + 1` gives every ordinary `σ(p ^ (2 β))` a prime factor `≡ 1 (mod l)`
  other than `q`; there are at most `2 β` such primes, each receiving weight at most `2 β`.
  So there are at most `4 β ^ 2` ordinary primes.

This is known mathematics; the file only formalizes it.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## Prime factors of `σ(p ^ e)` when `e + 1` is a prime power -/

/-- If `e + 1 = l ^ γ` for a prime `l`, every prime factor `t` of `σ(p ^ e)` is `l` or
`≡ 1 (mod l)`. -/
theorem prime_dvd_sigma_of_succ_eq_pow {p t l e γ : ℕ} (hp : p.Prime) (ht : t.Prime)
    (hl : l.Prime) (he : e + 1 = l ^ γ) (htd : t ∣ σ 1 (p ^ e)) : t = l ∨ t % l = 1 := by
  rcases (prime_dvd_sigma_prime_pow hp ht htd).2 with ⟨-, h2⟩ | ⟨h1, hd, hd'⟩
  · rw [he] at h2
    exact Or.inl ((Nat.prime_dvd_prime_iff_eq ht hl).mp (ht.dvd_of_dvd_pow h2))
  · rw [he] at hd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hl).mp hd
    have hj0 : j ≠ 0 := by rintro rfl; rw [hj, pow_zero] at h1; omega
    rw [hj] at hd'
    have hlt : l ∣ t - 1 := (dvd_pow_self l hj0).trans hd'
    right
    have h := (Nat.modEq_iff_dvd' ht.one_lt.le).mpr hlt
    rw [Nat.ModEq, Nat.mod_eq_of_lt hl.one_lt] at h
    exact h.symm

/-- A positive number whose prime factors are all `≡ 1 (mod l)` is `≡ 1 (mod l)`. -/
private lemma mod_eq_one_of_prime_factors {l : ℕ} (hl : 1 < l) (n : ℕ) (hn : n ≠ 0)
    (ht : ∀ t, t.Prime → t ∣ n → t % l = 1) : n % l = 1 := by
  induction n using induction_on_primes with
  | zero => exact absurd rfl hn
  | one => exact Nat.mod_eq_of_lt hl
  | prime_mul p a hp ih =>
    have ha : a ≠ 0 := by rintro rfl; simp at hn
    rw [Nat.mul_mod, ht p hp (dvd_mul_right p a),
      ih ha fun t htp htd => ht t htp (htd.mul_left p), Nat.one_mul, Nat.mod_eq_of_lt hl]

/-- `x ^ (l ^ γ) = x` in `ZMod l` (Fermat). -/
private lemma zmod_pow_pow_card {l : ℕ} [Fact l.Prime] (x : ZMod l) (γ : ℕ) :
    x ^ (l ^ γ) = x := by
  induction γ with
  | zero => simp
  | succ γ ih => rw [pow_succ, pow_mul, ih, ZMod.pow_card]

/-- Kanold. If all ordinary exponents of the odd perfect number `N` equal `2 β` and
`2 β + 1 = l ^ γ` for a prime `l`, then `l` is not the special prime. Write
`N = l ^ k R ^ (2 β)`. Every prime factor of `X = ∏ σ(p ^ (2 β))` is `l` or `≡ 1 (mod l)`, so
the part `U` of `X` prime to `l` is `≡ 1 (mod l)`; removing the powers of `l` from
`σ(l ^ k) X = 2 l ^ k R ^ (2 β)` gives `σ(l ^ k) U = 2 R ^ (2 β)`, which reads `1 = 2`
modulo `l` since `R ^ (l ^ γ) ≡ R`. -/
theorem false_of_special_succ_eq_pow {N l β γ : ℕ} (h : OddPerfect N) (hl : l.Prime)
    (hodd : Odd (N.factorization l)) (hβ : 2 * β + 1 = l ^ γ)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ l → N.factorization p = 2 * β) : False := by
  have : Fact l.Prime := ⟨hl⟩
  have hN0 := h.ne_zero
  have hlN : l ∈ N.primeFactors := Nat.support_factorization N ▸
    Finsupp.mem_support_iff.mpr (by rintro h0; simp [h0] at hodd)
  set k := N.factorization l with hk
  set P := N.primeFactors.erase l with hP
  have hPp : ∀ p ∈ P, p.Prime ∧ p ≠ l ∧ N.factorization p = 2 * β := fun p hp => by
    obtain ⟨hpl, hpN⟩ := Finset.mem_erase.mp hp
    exact ⟨Nat.prime_of_mem_primeFactors hpN, hpl, hexp p hpN hpl⟩
  set X := ∏ p ∈ P, σ 1 (p ^ (2 * β)) with hX
  set R := ∏ p ∈ P, p with hR
  have hNprod : N = l ^ k * R ^ (2 * β) := by
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
  have hE : σ 1 (l ^ k) * X = 2 * (l ^ k * R ^ (2 * β)) := by
    rw [← hσprod, ← hNprod, h.sigma_eq]
  have hX0 : X ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp =>
    (sigma_pos 1 _ (pow_pos (hPp p hp).1.pos _).ne').ne'
  set U := ordCompl[l] X with hU
  have hUmod : U % l = 1 := by
    refine mod_eq_one_of_prime_factors hl.one_lt U (Nat.ordCompl_pos l hX0).ne' fun t ht htU => ?_
    have htX : t ∣ X := htU.trans (Nat.ordCompl_dvd X l)
    obtain ⟨p, hp, htp⟩ := (Prime.dvd_finsetProd_iff ht.prime _).mp htX
    rcases prime_dvd_sigma_of_succ_eq_pow (hPp p hp).1 ht hl hβ htp with rfl | h1
    · exact absurd htU (Nat.not_dvd_ordCompl ht hX0)
    · exact h1
  have hlR : ¬ l ∣ R := by
    intro hd
    obtain ⟨p, hp, hlp⟩ := (Prime.dvd_finsetProd_iff hl.prime _).mp hd
    exact (hPp p hp).2.1 ((Nat.prime_dvd_prime_iff_eq hl (hPp p hp).1).mp hlp).symm
  have hlσ : ¬ l ∣ σ 1 (l ^ k) := fun hd =>
    hl.one_lt.ne' ((Nat.coprime_comm.mp (coprime_sigma_prime_pow hl k)).eq_one_of_dvd hd)
  have hl2 : ¬ l ∣ 2 := fun hd => by
    have h2 : l = 2 := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp hd
    exact h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hlN)
  have hcompl : ∀ {n : ℕ}, ¬ l ∣ n → ordCompl[l] n = n := fun hn => by
    rw [Nat.factorization_eq_zero_of_not_dvd hn, pow_zero, Nat.div_one]
  have hE' : σ 1 (l ^ k) * U = 2 * R ^ (2 * β) := by
    have := congrArg (fun n => ordCompl[l] n) hE
    simp only [Nat.ordCompl_mul, hcompl hlσ, hcompl hl2,
      hcompl (fun hd => hlR (hl.dvd_of_dvd_pow hd)), Nat.ordCompl_self_pow hl, one_mul] at this
    rw [← hU] at this
    exact this
  have hc := congrArg (fun n : ℕ => (n : ZMod l)) hE'
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hc
  have hσ1 : ((σ 1 (l ^ k) : ℕ) : ZMod l) = 1 := by
    rw [sigma_one_apply_prime_pow hl, Nat.cast_sum, Finset.sum_range_succ']
    simp
  have hU1 : ((U : ℕ) : ZMod l) = 1 := by
    rw [← ZMod.natCast_mod, hUmod, Nat.cast_one]
  have hR0 : ((R : ℕ) : ZMod l) ≠ 0 := fun h0 => hlR ((ZMod.natCast_eq_zero_iff R l).mp h0)
  have hR1 : ((R : ℕ) : ZMod l) ^ (2 * β) = 1 := by
    have h1 : ((R : ℕ) : ZMod l) ^ (2 * β) * (R : ZMod l) = 1 * (R : ZMod l) := by
      rw [← pow_succ, hβ, zmod_pow_pow_card, one_mul]
    exact mul_right_cancel₀ hR0 h1
  rw [hσ1, hU1, hR1] at hc
  rw [mul_one, mul_one, ← one_add_one_eq_two] at hc
  exact one_ne_zero (left_eq_add.mp hc)

/-! ## Counting lemmas -/

/-- At most `v_s(N)` prime factors `p ≠ s` of the perfect number `N` have
`s ∣ σ(p ^ v_p(N))`, for an odd prime `s`. -/
theorem card_feeders_le {N s : ℕ} (hN : N.Perfect) (hs : s.Prime) (hs2 : s ≠ 2) :
    ((N.primeFactors.erase s).filter (fun p => s ∣ σ 1 (p ^ N.factorization p))).card ≤
      N.factorization s := by
  have : Fact s.Prime := ⟨hs⟩
  rw [factorization_eq_sum_erase hN hs hs2, Finset.card_eq_sum_ones]
  calc ∑ p ∈ (N.primeFactors.erase s).filter (fun p => s ∣ σ 1 (p ^ N.factorization p)), 1
      ≤ ∑ p ∈ (N.primeFactors.erase s).filter (fun p => s ∣ σ 1 (p ^ N.factorization p)),
          padicValNat s (σ 1 (p ^ N.factorization p)) := by
        refine Finset.sum_le_sum fun p hp => ?_
        obtain ⟨hp', hd⟩ := Finset.mem_filter.mp hp
        have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp')
        rw [Nat.padicValNat_def]
        exact one_le_multiplicity_of_dvd (sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)).ne' hd
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- `σ(p ^ (k + 1)) = 1 + p σ(p ^ k)`. -/
private lemma sigma_pow_succ_eq {p : ℕ} (hp : p.Prime) (k : ℕ) :
    σ 1 (p ^ (k + 1)) = 1 + p * σ 1 (p ^ k) := by
  rw [sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hp, Finset.sum_range_succ',
    Finset.mul_sum, pow_zero, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Dandapat, Hunsucker and Pomerance: `p ^ 2 ∤ σ(p ^ (k + 1)) - 1`. -/
theorem not_sq_dvd_sigma_sub_one {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ¬ p ^ 2 ∣ σ 1 (p ^ (k + 1)) - 1 := by
  rw [sigma_pow_succ_eq hp, Nat.add_sub_cancel_left, pow_two]
  intro hd
  exact (prime_dvd_sigma_prime_pow hp hp (Nat.dvd_of_mul_dvd_mul_left hp.pos hd)).1 rfl

/-- Lemma 2.6 of Yamada (2005). Let `p` be an odd prime with `σ(p ^ (2 β)) = q ^ c`, `q` prime,
`β ≥ 1`, and `v_p(σ(q ^ a)) = 2 β`. Then `p ^ (2 β - 1) ∣ a + 1`. -/
theorem pow_dvd_succ_of_sigma_eq_pow {p q β c a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : q.Prime) (hpq : p ≠ q) (hβ1 : 1 ≤ β) (hc : σ 1 (p ^ (2 * β)) = q ^ c)
    (hv : padicValNat p (σ 1 (q ^ a)) = 2 * β) : p ^ (2 * β - 1) ∣ a + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ : ∃ k, 2 * β = k + 1 := ⟨2 * β - 1, by omega⟩
  have hk' : 2 * β - 1 = k := by omega
  rw [hk']
  rw [hk] at hc hv
  have hpd : p ∣ σ 1 (q ^ a) :=
    dvd_of_one_le_multiplicity (by rw [← Nat.padicValNat_def]; omega)
  rcases (prime_dvd_sigma_prime_pow hq hp hpd).2 with ⟨h1, -⟩ | ⟨ho1, hod, -⟩
  · rw [padicValNat_sigma_of_mod_eq_one hq hp hp2 h1] at hv
    have : p ^ padicValNat p (a + 1) ∣ a + 1 := by
      rw [Nat.padicValNat_def]; exact pow_multiplicity_dvd _ _
    rw [hv] at this
    exact (pow_dvd_pow p (by omega)).trans this
  · rw [padicValNat_sigma_prime_pow_of_orderOf_dvd hq hp hp2 (Ne.symm hpq) ho1 hod] at hv
    set o := orderOf (q : ZMod p) with ho
    have hqc : 1 ≤ q ^ c := Nat.one_le_pow _ _ hq.pos
    have hpc : p ∣ q ^ c - 1 := by
      rw [← hc, sigma_pow_succ_eq hp, Nat.add_sub_cancel_left]
      exact dvd_mul_right p _
    have hqc1 : (q : ZMod p) ^ c = 1 := by
      have := (ZMod.natCast_eq_zero_iff (q ^ c - 1) p).mpr hpc
      rw [Nat.cast_sub hqc, Nat.cast_pow, Nat.cast_one, sub_eq_zero] at this
      exact this
    have hoc : o ∣ c := orderOf_dvd_of_pow_eq_one hqc1
    have hdvd : q ^ o - 1 ∣ q ^ c - 1 := Nat.pow_sub_one_dvd_pow_sub_one q hoc
    have hqo : 1 < q ^ o := Nat.one_lt_pow (by omega) hq.one_lt
    have hle : padicValNat p (q ^ o - 1) ≤ 1 := by
      by_contra hlt
      have h2 : p ^ 2 ∣ q ^ o - 1 :=
        (multiplicity_dvd_iff_le (by omega)).mpr (by rw [← Nat.padicValNat_def]; omega)
      exact not_sq_dvd_sigma_sub_one hp k (hc ▸ h2.trans hdvd)
    obtain ⟨m, hm⟩ := hod
    have ho0 : 0 < o := by omega
    rw [hm, Nat.mul_div_cancel_left _ ho0] at hv
    have hm0 : m ≠ 0 := by rintro rfl; omega
    have : p ^ k ∣ m := (multiplicity_dvd_iff_le hm0).mpr (by rw [← Nat.padicValNat_def]; omega)
    rw [hm]
    exact this.trans (dvd_mul_left m o)

/-- `2 (b + 1) ^ #U ≤ τ(n)` when `2 ∣ n` and `p ^ b ∣ n`, `b ≥ 1`, for every `p` in a set `U`
of odd primes. -/
theorem two_mul_pow_le_card_divisors {n b : ℕ} (U : Finset ℕ) (hn : n ≠ 0) (h2 : 2 ∣ n)
    (hb : 1 ≤ b) (hU : ∀ p ∈ U, p.Prime ∧ p ≠ 2 ∧ p ^ b ∣ n) :
    2 * (b + 1) ^ U.card ≤ n.divisors.card := by
  rw [Nat.card_divisors hn]
  have h2U : 2 ∉ U := fun h => (hU 2 h).2.1 rfl
  have hsub : insert 2 U ⊆ n.primeFactors := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, hn⟩
    · obtain ⟨hpp, -, hpb⟩ := hU p hp
      exact Nat.mem_primeFactors.mpr ⟨hpp, (dvd_pow_self p (by omega)).trans hpb, hn⟩
  have h2f : 1 ≤ n.factorization 2 := (Nat.prime_two.dvd_iff_one_le_factorization hn).mp h2
  have hprod : (b + 1) ^ U.card ≤ ∏ x ∈ U, (n.factorization x + 1) := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) fun p hp => ?_
    have := ((hU p hp).1.pow_dvd_iff_le_factorization hn).mp (hU p hp).2.2
    omega
  calc 2 * (b + 1) ^ U.card ≤ ∏ x ∈ insert 2 U, (n.factorization x + 1) := by
        rw [Finset.prod_insert h2U]
        exact Nat.mul_le_mul (by omega) hprod
    _ ≤ _ := Nat.le_of_dvd (Finset.prod_pos fun _ _ => by omega)
        (Finset.prod_dvd_prod_of_subset _ _ _ hsub)

/-- Bang's theorem at the special prime: `τ(α + 1) ≤ #(ordinary primes) + 2`, since every
divisor `d ≥ 3` of `α + 1` is the order of `q` modulo its own prime factor of `N`. -/
theorem card_divisors_succ_le {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    (N.factorization q + 1).divisors.card ≤ (N.primeFactors.erase q).card + 2 := by
  have : Fact q.Prime := ⟨hq⟩
  have hqN : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq,
    Nat.dvd_of_factorization_pos (by obtain ⟨k, hk⟩ := hodd; omega), h.ne_zero⟩
  set n := N.factorization q + 1 with hn
  have key : (n.divisors.filter (fun d => 3 ≤ d)).card ≤ (N.primeFactors.erase q).card := by
    have hex : ∀ d ∈ n.divisors.filter (fun d => 3 ≤ d),
        ∃ t ∈ N.primeFactors.erase q, orderOf (q : ZMod t) = d := by
      intro d hd
      obtain ⟨hdn, hd3⟩ := Finset.mem_filter.mp hd
      obtain ⟨t, htN, ho, -⟩ := exists_primeFactor_modEq_one h hqN hd3 (Nat.dvd_of_mem_divisors hdn)
      refine ⟨t, Finset.mem_erase.mpr ⟨?_, htN⟩, ho⟩
      rintro rfl
      rw [ZMod.natCast_self, orderOf_zero] at ho
      omega
    choose! f hf hfo using hex
    exact Finset.card_le_card_of_injOn f (fun a ha => hf a ha)
      (fun a ha b hb hab => by rw [← hfo a ha, ← hfo b hb, hab])
  have hsmall : (n.divisors.filter (fun d => ¬ 3 ≤ d)).card ≤ 2 := by
    calc _ ≤ ({1, 2} : Finset ℕ).card := Finset.card_le_card (fun d hd => by
            obtain ⟨hdn, hd3⟩ := Finset.mem_filter.mp hd
            have := Nat.pos_of_mem_divisors hdn
            simp only [Finset.mem_insert, Finset.mem_singleton]
            omega)
      _ ≤ 2 := Finset.card_le_two
  have := Finset.card_filter_add_card_filter_not (s := n.divisors) (fun d => 3 ≤ d)
  omega

/-- The ledger at a prime fed only by the special prime. Let all ordinary exponents equal
`2 β` with `2 β + 1 = l` prime. If an ordinary prime `p ≠ l` with `p ≢ 1 (mod l)` divides `N`,
then no ordinary component feeds `p`, so `v_p(σ(q ^ α)) = 2 β`. -/
theorem padicValNat_sigma_special_eq {N q l β p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hβ : 2 * β + 1 = l)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 2 * β)
    (hp : p ∈ N.primeFactors) (hpq : p ≠ q) (hpl : p ≠ l) (hp1 : p % l ≠ 1) :
    padicValNat p (σ 1 (q ^ N.factorization q)) = 2 * β := by
  have hqN : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq,
    Nat.dvd_of_factorization_pos (by obtain ⟨k, hk⟩ := hodd; omega), h.ne_zero⟩
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hp)
  rw [← hexp p hp hpq, factorization_eq_sum_erase h.perfect hpp hp2]
  rw [Finset.sum_eq_single q]
  · intro r hr hrq
    obtain ⟨-, hrN⟩ := Finset.mem_erase.mp hr
    rw [Nat.padicValNat_def]
    refine multiplicity_eq_zero_of_not_dvd fun hd => ?_
    rw [hexp r hrN hrq] at hd
    obtain ⟨-, h1 | h2 | h3⟩ := prime_dvd_sigma_of_equal_exponents h hl hβ hexp hrN hrq hpp hd
    · exact hpl h1
    · exact hpq h2
    · exact hp1 (Finset.mem_filter.mp h3).2.2
  · intro hqn
    exact absurd (Finset.mem_erase.mpr ⟨hpq.symm, hqN⟩) hqn

/-! ## The main theorem -/

open Classical in
/-- Yamada's bound (Colloq. Math. 103 (2005), Theorem 1.1). If `N` is an odd perfect number
with special prime `q` and every other prime factor of `N` has exponent exactly `2 β`, then
`N` has at most `4 β ^ 2 + 2 β + 3` distinct prime factors. This is known mathematics; the
proof follows Yamada's (see the module docstring), with Steuerwald's theorem for `β = 1` in
place of the paper's reduction to `β ≥ 8`. -/
theorem card_primeFactors_le_of_equal_exponents {N q β : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 2 * β) :
    N.primeFactors.card ≤ 4 * β ^ 2 + 2 * β + 3 := by
  have hN0 := h.ne_zero
  have hqN : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq,
    Nat.dvd_of_factorization_pos (by obtain ⟨k, hk⟩ := hodd; omega), hN0⟩
  have hq4 := (mod_four_special h hq hodd).1
  have hq5 : 5 ≤ q := by have := hq.two_le; omega
  have hpf2 : ∀ p ∈ N.primeFactors, p ≠ 2 := fun p hp h2 =>
    h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hp)
  obtain ⟨p₀, hp₀, hp₀q⟩ := exists_ordinary_prime h hq hodd
  have hβ1 : 1 ≤ β := by
    have h1 := hexp p₀ hp₀ hp₀q
    have h2 : N.factorization p₀ ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]; exact hp₀
    omega
  set O := N.primeFactors.erase q with hO
  have hcardN : N.primeFactors.card = O.card + 1 := (Finset.card_erase_add_one hqN).symm
  suffices hOle : O.card ≤ 4 * β ^ 2 + 2 * β + 2 by omega
  by_cases hβeq : β = 1
  · exact (steuerwald h hq hodd fun p hp hpq => by rw [hexp p hp hpq, hβeq]).elim
  have hβ2 : 2 ≤ β := by omega
  set A : ℕ → Finset ℕ := fun s =>
    (N.primeFactors.erase s).filter (fun p => s ∣ σ 1 (p ^ N.factorization p)) with hA
  by_cases hprime : (2 * β + 1).Prime
  · -- `2 β + 1 = l` prime
    obtain ⟨l, hβl⟩ : ∃ l, 2 * β + 1 = l := ⟨_, rfl⟩
    have hlp : l.Prime := hβl ▸ hprime
    have hl2 : l ≠ 2 := by omega
    have hlN : l ∣ N :=
      dvd_of_equal_exponents_of_succ_eq_pow h hq hodd hlp hl2 (a := 1) (by rw [pow_one, hβl]) hexp
    have hlq : l ≠ q := by
      rintro rfl
      exact false_of_special_succ_eq_pow h hlp hodd (γ := 1) (by rw [pow_one, hβl]) hexp
    have hlmem : l ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hlp, hlN, hN0⟩
    have hNP := card_not_special_pow_le h hlp hβl hexp hlmem hlq
    set U := O.filter (fun p => p ≠ l ∧ ∃ c, σ 1 (p ^ (2 * β)) = q ^ c) with hU
    have hcover : O ⊆ N.primeFactors.filter
        (fun p => p ≠ q ∧ ¬ ∃ c, σ 1 (p ^ (2 * β)) = q ^ c) ∪ insert l U := by
      intro p hp
      obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hp
      by_cases hc : ∃ c, σ 1 (p ^ (2 * β)) = q ^ c
      · refine Finset.mem_union_right _ ?_
        by_cases hpl : p = l
        · exact hpl ▸ Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hp, hpl, hc⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpN, hpq, hc⟩)
    have hOU : O.card ≤ 4 * β ^ 2 + 2 * β + (U.card + 1) := by
      calc O.card ≤ _ := Finset.card_le_card hcover
        _ ≤ _ := Finset.card_union_le _ _
        _ ≤ 2 * β * (2 * β + 1) + (U.card + 1) :=
            Nat.add_le_add hNP (Finset.card_insert_le _ _)
        _ = _ := by ring
    have hUprop : ∀ p ∈ U, p.Prime ∧ p ≠ 2 ∧ p ^ (2 * β - 1) ∣ N.factorization q + 1 := by
      intro p hp
      obtain ⟨hpO, hpl, c, hc⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hpO
      have hpp := Nat.prime_of_mem_primeFactors hpN
      have hp2 := hpf2 p hpN
      have hp1 : p % l ≠ 1 := by
        intro h1
        have : Fact l.Prime := ⟨hlp⟩
        have hv := padicValNat_sigma_of_mod_eq_one hpp hlp hl2 h1 (a := 2 * β)
        rw [hβl, Nat.padicValNat_def (p := l) (n := l), Nat.Prime.multiplicity_self, hc] at hv
        have hld : l ∣ q ^ c :=
          dvd_of_one_le_multiplicity (by rw [← Nat.padicValNat_def]; omega)
        exact hlq ((Nat.prime_dvd_prime_iff_eq hlp hq).mp (hlp.dvd_of_dvd_pow hld))
      exact ⟨hpp, hp2, pow_dvd_succ_of_sigma_eq_pow hpp hp2 hq hpq hβ1 hc
        (padicValNat_sigma_special_eq h hq hodd hlp hβl hexp hpN hpq hpl hp1)⟩
    have hτ := two_mul_pow_le_card_divisors U (n := N.factorization q + 1) (by omega)
      (by obtain ⟨k, hk⟩ := hodd; exact ⟨k + 1, by omega⟩) (by omega) hUprop
    have hτ' := card_divisors_succ_le h hq hodd
    rw [show 2 * β - 1 + 1 = 2 * β by omega] at hτ
    have hu : U.card ≤ 1 := by
      by_contra hu
      obtain ⟨k, hk⟩ : ∃ k, U.card = k + 2 := ⟨U.card - 2, by omega⟩
      rw [hk, pow_add] at hτ
      have hk1 : k + 1 ≤ (2 * β) ^ k := by
        have h1 : k < 2 ^ k := Nat.lt_two_pow_self
        have h2 : 2 ^ k ≤ (2 * β) ^ k := Nat.pow_le_pow_left (by omega) k
        omega
      have h3 : (k + 1) * (2 * β) ^ 2 ≤ (2 * β) ^ k * (2 * β) ^ 2 :=
        Nat.mul_le_mul_right _ hk1
      have h4 : 2 * ((k + 1) * (2 * β) ^ 2) ≤ 4 * β ^ 2 + 2 * β + (k + 2 + 1) + 2 := by
        linarith
      have h5 : (2 * β) ^ 2 = 4 * β ^ 2 := by ring
      rw [h5] at h4
      have h6 : 4 ≤ β ^ 2 := by nlinarith
      have h7 : 4 * k ≤ β ^ 2 * k := Nat.mul_le_mul_right k h6
      nlinarith
    omega
  · -- `2 β + 1` not prime
    by_cases hex : ∃ l, l.Prime ∧ l ∣ 2 * β + 1 ∧ l ≠ q
    · obtain ⟨l, hlp, hld, hlq⟩ := hex
      have hl2 : l ≠ 2 := by rintro rfl; omega
      have hl3 : 3 ≤ l := by have := hlp.two_le; omega
      have hlN : l ∣ N := dvd_of_dvd_succ h hq hodd hlp hl2 fun p hp hpq => by
        rw [hexp p hp hpq]; exact hld
      have hlmem : l ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hlp, hlN, hN0⟩
      have hne : l ≠ 2 * β + 1 := fun e => hprime (e ▸ hlp)
      set S := N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1) with hS
      have hSle : S.card ≤ 2 * β := by
        have h1 : S.card * padicValNat l (2 * β + 1) ≤ 2 * β := by
          convert card_mul_padicValNat_le_of_ordinary h.perfect hlp hl2 hexp hlmem hlq
        have : Fact l.Prime := ⟨hlp⟩
        have h2 : 1 ≤ padicValNat l (2 * β + 1) := by
          rw [Nat.padicValNat_def]; exact one_le_multiplicity_of_dvd (by omega) hld
        nlinarith
      have hAle : ∀ s ∈ S, (A s).card ≤ 2 * β := fun s hs => by
        obtain ⟨hsN, hsq, -⟩ := Finset.mem_filter.mp hs
        rw [← hexp s hsN hsq]
        exact card_feeders_le h.perfect (Nat.prime_of_mem_primeFactors hsN) (hpf2 s hsN)
      have hcover : O ⊆ S.biUnion A := by
        intro p hp
        obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hp
        have hpp := Nat.prime_of_mem_primeFactors hpN
        have hp3 : 3 ≤ p := by have := hpp.two_le; have := hpf2 p hpN; omega
        have hd1 : l ∣ N.factorization p + 1 := by rw [hexp p hpN hpq]; exact hld
        have hd2 : 2 * β + 1 ∣ N.factorization p + 1 := by rw [hexp p hpN hpq]
        obtain ⟨t₁, ht₁, ht₁d, ht₁o, ht₁m⟩ := exists_prime_dvd_sigma_orderOf_eq hpp hp3 hl3 hd1
        obtain ⟨t₂, ht₂, ht₂d, ht₂o, ht₂m⟩ :=
          exists_prime_dvd_sigma_orderOf_eq hpp hp3 (by omega : 3 ≤ 2 * β + 1) hd2
        have ht₂l : t₂ % l = 1 := by
          have := Nat.mod_mod_of_dvd t₂ hld
          rw [ht₂m, Nat.mod_eq_of_lt hlp.one_lt] at this
          exact this.symm
        have ht12 : t₁ ≠ t₂ := by
          rintro rfl
          rw [ht₁o] at ht₂o
          exact hne ht₂o
        obtain ⟨t, ht, htd, htm, htq⟩ : ∃ t, t.Prime ∧ t ∣ σ 1 (p ^ N.factorization p) ∧
            t % l = 1 ∧ t ≠ q := by
          by_cases h1 : t₁ = q
          · exact ⟨t₂, ht₂, ht₂d, ht₂l, fun h2 => ht12 (h1.trans h2.symm)⟩
          · exact ⟨t₁, ht₁, ht₁d, ht₁m, h1⟩
        have ht2 : t ≠ 2 := by rintro rfl; rw [Nat.mod_eq_of_lt (by omega)] at htm; omega
        have htN := OPNStarter.force_prime h.perfect hpp rfl ht ht2 htd
        refine Finset.mem_biUnion.mpr ⟨t, Finset.mem_filter.mpr
          ⟨Nat.mem_primeFactors.mpr ⟨ht, htN, hN0⟩, htq, htm⟩, Finset.mem_filter.mpr
          ⟨Finset.mem_erase.mpr ⟨(prime_dvd_sigma_prime_pow hpp ht htd).1.symm, hpN⟩, htd⟩⟩
      calc O.card ≤ (S.biUnion A).card := Finset.card_le_card hcover
        _ ≤ S.card * (2 * β) := Finset.card_biUnion_le_card_mul _ _ _ hAle
        _ ≤ 4 * β ^ 2 + 2 * β + 2 := by nlinarith
    · push Not at hex
      have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (n := 2 * β + 1) (p := q) (by omega)
        fun hd ht => hex _ hd ht
      exact (false_of_special_succ_eq_pow h hq hodd hpow hexp).elim

end OddPerfect

#print axioms OddPerfect.prime_dvd_sigma_of_succ_eq_pow
#print axioms OddPerfect.false_of_special_succ_eq_pow
#print axioms OddPerfect.card_feeders_le
#print axioms OddPerfect.not_sq_dvd_sigma_sub_one
#print axioms OddPerfect.pow_dvd_succ_of_sigma_eq_pow
#print axioms OddPerfect.two_mul_pow_le_card_divisors
#print axioms OddPerfect.card_divisors_succ_le
#print axioms OddPerfect.padicValNat_sigma_special_eq
#print axioms OddPerfect.card_primeFactors_le_of_equal_exponents
