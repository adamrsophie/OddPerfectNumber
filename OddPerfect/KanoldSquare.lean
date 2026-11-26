import OddPerfect.KanoldFive

/-!
# The square case of Kanold's fifth power theorem: a normal form

Let `N` be an odd perfect number with special prime `q`, and suppose `q ^ 2` divides
`e_p + 1` for every ordinary prime `p` (with `e_p = v_p(N)`). Then `v_q(N) ≥ 6` and
`v_q(N) ≡ 1 (mod 4)`, so the fifth power `q ^ 10 ∣ N` fails only if `v_q(N) = 9`.
`OddPerfect/KanoldFive.lean` excludes this only for `q = 5`.

This file proves the normal form that precedes the last step of the known proof of the
fifth power theorem in this case. With `S` the set of prime factors `≡ 1 (mod q)`:

* every ordinary prime whose component divisor sum is divisible by `q` lies in `S`;
* `|S| = 4`;
* three members `s` of `S` have `e_s + 1 = q ^ 2` and one has `e_s + 1 = q ^ 3`.

The last step (a Diophantine argument excluding this configuration) is not formalized here.

* `card_le_card_erase_of_dvd_succ`: distinct orders `d ≥ 3`, each a multiple of `q` and a
  divisor of `e_s + 1`, give as many members of `S` other than `s` (their primitive receivers).
* `kanold_square_normal_form`: the normal form above, given `v_q(N) = 9`.
* `pow_ten_dvd_or_normal_form`: `q ^ 10 ∣ N`, or `v_q(N) = 9` and the normal form holds.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- Primitive receivers. Let `s` be a prime factor of the odd perfect number `N`, `2 ≤ q`, and
`D` a finite set of numbers `d ≥ 3`, each divisible by `q` and dividing `v_s(N) + 1`. Then the
prime factors of `N` that are `≡ 1 (mod q)`, other than `s`, number at least `|D|`. -/
theorem card_le_card_erase_of_dvd_succ {N q s : ℕ} (h : OddPerfect N) (hq2 : 2 ≤ q)
    (hs : s ∈ N.primeFactors) (D : Finset ℕ) (hD3 : ∀ d ∈ D, 3 ≤ d) (hDq : ∀ d ∈ D, q ∣ d)
    (hDe : ∀ d ∈ D, d ∣ N.factorization s + 1) :
    D.card ≤ ((N.primeFactors.filter (fun p => p % q = 1)).erase s).card := by
  have hj : ∀ d ∈ D, ∃ t ∈ N.primeFactors, orderOf (s : ZMod t) = d ∧ t % d = 1 :=
    fun d hd => exists_primeFactor_modEq_one h hs (hD3 d hd) (hDe d hd)
  choose! f hfN hfo hfm using hj
  have hsub : D.image f ⊆ (N.primeFactors.filter (fun p => p % q = 1)).erase s := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨hfN d hd, ?_⟩⟩
    · intro hfs
      have : Fact s.Prime := ⟨Nat.prime_of_mem_primeFactors hs⟩
      have := hfo d hd
      rw [hfs, ZMod.natCast_self, orderOf_zero] at this
      have := hD3 d hd
      omega
    · have := Nat.mod_mod_of_dvd (f d) (hDq d hd)
      rw [hfm d hd, Nat.mod_eq_of_lt (by omega)] at this
      exact this.symm
  have hinj : Set.InjOn f (D : Set ℕ) := by
    intro i hi j hj hij
    have := hfo i hi
    rw [hij, hfo j hj] at this
    exact this.symm
  have := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injOn hinj] at this

/-- Four pairwise distinct numbers form a set of size `4`. -/
private theorem card_four {a b c d : ℕ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : ({a, b, c, d} : Finset ℕ).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
    Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]

/-- The normal form of the square case with exponent `9`. Let `N` be an odd perfect number with
special prime `q`, suppose `q ^ 2 ∣ e_p + 1` for every ordinary prime `p`, and `v_q(N) = 9`.
Let `S` be the set of prime factors `≡ 1 (mod q)`. Then (a) every ordinary prime `p` with
`q ∣ σ(p ^ e_p)` lies in `S`; (b) `|S| = 4`; (c) one member `r` of `S` has `e_r + 1 = q ^ 3`
and every other member `s` has `e_s + 1 = q ^ 2`. This is the normal form preceding the last
step of the known proof of the fifth power theorem `q ^ 10 ∣ N`; that last step is not
formalized here. -/
theorem kanold_square_normal_form {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → q ^ 2 ∣ N.factorization p + 1)
    (h9 : N.factorization q = 9) :
    (∀ p ∈ N.primeFactors, p ≠ q → q ∣ σ 1 (p ^ N.factorization p) →
        p ∈ N.primeFactors.filter (fun p => p % q = 1)) ∧
      (N.primeFactors.filter (fun p => p % q = 1)).card = 4 ∧
      ∃ r ∈ N.primeFactors.filter (fun p => p % q = 1), N.factorization r + 1 = q ^ 3 ∧
        ∀ s ∈ N.primeFactors.filter (fun p => p % q = 1), s ≠ r →
          N.factorization s + 1 = q ^ 2 := by
  have : Fact q.Prime := ⟨hq⟩
  have hq4 := (mod_four_special h hq hodd).1
  have hq5 : 5 ≤ q := by have := hq.two_le; omega
  have hq2 : q ≠ 2 := by omega
  set S := N.primeFactors.filter (fun p => p % q = 1) with hS
  have hSq : ∀ p ∈ S, p ≠ q := by
    intro p hp hpq
    have := (Finset.mem_filter.mp hp).2
    rw [hpq, Nat.mod_self] at this
    omega
  have hSN : ∀ p ∈ S, p ∈ N.primeFactors := fun p hp => (Finset.mem_filter.mp hp).1
  -- `S` has at least three members
  obtain ⟨p₀, hp₀, hp₀q⟩ := exists_ordinary_prime h hq hodd
  obtain ⟨r₀, hr₀N, -, hr₀⟩ := exists_primeFactor_modEq_one h hp₀ (d := q) (by omega)
    ((dvd_pow_self q (by omega)).trans (hexp p₀ hp₀ hp₀q))
  have hr₀S : r₀ ∈ S := Finset.mem_filter.mpr ⟨hr₀N, hr₀⟩
  have hcard3 : 3 ≤ S.card :=
    succ_le_card_filter_mod_eq_one h (by omega) hr₀N hr₀ (hexp r₀ hr₀N (hSq r₀ hr₀S))
  -- contributions of the members of `S`
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, ∀ p, f p = padicValNat q (σ 1 (p ^ N.factorization p)) :=
    ⟨_, fun _ => rfl⟩
  have hfS : ∀ p ∈ S, f p = padicValNat q (N.factorization p + 1) := by
    intro p hp
    have hp1 := (Finset.mem_filter.mp hp).2
    rw [hf]
    refine padicValNat_sigma_prime_pow_of_dvd_pred (Nat.prime_of_mem_primeFactors (hSN p hp))
      hq hq2 ?_
    have := Nat.dvd_sub_mod (n := q) p
    rwa [hp1] at this
  have hlo : ∀ p ∈ S, 2 ≤ f p := by
    intro p hp
    rw [hfS p hp, Nat.padicValNat_def]
    exact (padicValNat_dvd_iff_le (by omega)).mp (hexp p (hSN p hp) (hSq p hp))
  have hhi : ∀ p ∈ S, f p + 1 ≤ S.card := by
    intro p hp
    rw [hfS p hp]
    exact succ_le_card_filter_mod_eq_one h (by omega) (hSN p hp)
      (Finset.mem_filter.mp hp).2 (by rw [Nat.padicValNat_def]; exact pow_multiplicity_dvd _ _)
  -- the exact ledger, split along `S`
  have hSsub : S ⊆ N.primeFactors.erase q := fun p hp =>
    Finset.mem_erase.mpr ⟨hSq p hp, hSN p hp⟩
  set T := N.primeFactors.erase q \ S with hT
  have hledger : N.factorization q = ∑ p ∈ T, f p + ∑ p ∈ S, f p := by
    rw [hT, Finset.sum_sdiff hSsub]
    simp only [hf]
    exact factorization_eq_sum_erase h.perfect hq hq2
  have hsumS : S.card * 2 ≤ ∑ p ∈ S, f p := by
    have := Finset.card_nsmul_le_sum S f 2 hlo
    rwa [smul_eq_mul] at this
  -- (a): no contributor outside `S`
  have hA : ∀ p ∈ N.primeFactors, p ≠ q → q ∣ σ 1 (p ^ N.factorization p) → p ∈ S := by
    intro p hpN hpq hdvd
    by_contra hpS
    have hp1 : p % q ≠ 1 := fun h1 => hpS (Finset.mem_filter.mpr ⟨hpN, h1⟩)
    have hpp := Nat.prime_of_mem_primeFactors hpN
    have hq2e := hexp p hpN hpq
    have hbig := succ_le_padicValNat_sigma_of_not_mod_eq_one hpp hq hq2 hpq hp1 hq2e hdvd
    rcases (prime_dvd_sigma_prime_pow hpp hq hdvd).2 with ⟨h1, -⟩ | ⟨hd1, hd, hdq⟩
    · exact hp1 h1
    set d := orderOf (p : ZMod q) with hdd
    have hdle : d ≤ q - 1 := Nat.le_of_dvd (by omega) hdq
    have hcop : Nat.Coprime d (q ^ 2) := by
      refine Nat.Coprime.pow_right 2 (Nat.Coprime.symm
        ((Nat.Prime.coprime_iff_not_dvd hq).mpr fun hqd => ?_))
      have := Nat.le_of_dvd (by omega) hqd
      omega
    have hdq2 : d * q ^ 2 ∣ N.factorization p + 1 := hcop.mul_dvd_of_dvd_of_dvd hd hq2e
    have hdq1 : d * q ∣ N.factorization p + 1 :=
      (Nat.mul_dvd_mul_left d (dvd_pow_self q two_ne_zero)).trans hdq2
    have hqq : q ∣ q ^ 2 := dvd_pow_self q two_ne_zero
    have e1 : q < d * q := by nlinarith
    have e2 : d * q < q ^ 2 := by rw [sq]; exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    have e3 : q ^ 2 < d * q ^ 2 := by nlinarith
    have h4 := card_le_card_erase_of_dvd_succ (q := q) h (by omega) hpN {q, q ^ 2, d * q, d * q ^ 2}
      (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> omega)
      (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact dvd_rfl
        · exact hqq
        · exact dvd_mul_left q d
        · exact hqq.mul_left d)
      (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact hqq.trans hq2e
        · exact hq2e
        · exact hdq1
        · exact hdq2)
    rw [card_four (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)] at h4
    change 4 ≤ (S.erase p).card at h4
    rw [Finset.erase_eq_of_notMem hpS] at h4
    have hpT : p ∈ T := Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hpq, hpN⟩, hpS⟩
    have := Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) hpT
    rw [← hf] at hbig
    omega
  have hT0 : ∑ p ∈ T, f p = 0 := Finset.sum_eq_zero fun p hp => by
    obtain ⟨hpE, hpS⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hpE
    by_contra hne
    rw [hf] at hne
    exact hpS (hA p hpN hpq (dvd_of_one_le_padicValNat
      (Nat.one_le_iff_ne_zero.mpr (by rwa [← Nat.padicValNat_def]))))
  have hsum9 : S.sum f = 9 := by
    have : ∑ p ∈ S, f p = 9 := by omega
    exact this
  -- (b): `|S| = 4`
  have hS4 : S.card = 4 := by
    rcases (by omega : S.card = 3 ∨ S.card = 4) with h3 | h4
    · exfalso
      have := Finset.sum_le_card_nsmul S f 2 fun p hp => by have := hhi p hp; omega
      rw [smul_eq_mul, h3] at this
      omega
    · exact h4
  -- the valuations are `3, 2, 2, 2`
  obtain ⟨r, hrS, hr3⟩ : ∃ r ∈ S, f r = 3 := by
    by_contra hno
    push Not at hno
    have := Finset.sum_le_card_nsmul S f 2 fun p hp => by
      have := hhi p hp; have := hno p hp; omega
    rw [smul_eq_mul, hS4] at this
    omega
  have hrest : ∀ s ∈ S, s ≠ r → f s = 2 := by
    intro s hs hsr
    have hsr' : s ∈ S.erase r := Finset.mem_erase.mpr ⟨hsr, hs⟩
    have e1 : f r + (S.erase r).sum f = S.sum f := Finset.add_sum_erase S f hrS
    have e2 : f s + ((S.erase r).erase s).sum f = (S.erase r).sum f :=
      Finset.add_sum_erase (S.erase r) f hsr'
    have hc : ((S.erase r).erase s).card = 2 := by
      rw [Finset.card_erase_of_mem hsr', Finset.card_erase_of_mem hrS, hS4]
    have e3 := Finset.card_nsmul_le_sum ((S.erase r).erase s) f 2 fun x hx =>
      hlo x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
    rw [smul_eq_mul, hc] at e3
    have := hlo s hs
    have := hhi s hs
    omega
  -- (c): the lengths are pure powers of `q`
  have hpure : ∀ s ∈ S, N.factorization s + 1 = q ^ padicValNat q (N.factorization s + 1) := by
    intro s hs
    have hv2 : 2 ≤ padicValNat q (N.factorization s + 1) := hfS s hs ▸ hlo s hs
    obtain ⟨k, hk⟩ := (show q ^ padicValNat q (N.factorization s + 1) ∣ N.factorization s + 1 by
      rw [Nat.padicValNat_def]; exact pow_multiplicity_dvd _ _)
    set v := padicValNat q (N.factorization s + 1) with hv
    by_contra hne
    have hk1 : k ≠ 1 := by rintro rfl; rw [mul_one] at hk; exact hne hk
    have hu := Nat.minFac_prime hk1
    set u := k.minFac with hud
    have huk : u ∣ k := Nat.minFac_dvd k
    have hu2 := hu.two_le
    have huq : u ≠ q := by
      intro huq
      apply pow_succ_padicValNat_not_dvd (p := q) (n := N.factorization s + 1) (by omega)
      rw [← Nat.padicValNat_def, ← hv, hk, pow_succ]
      exact Nat.mul_dvd_mul_left _ (huq ▸ huk)
    have hvd : q ^ 2 ∣ q ^ v := pow_dvd_pow q hv2
    have huq2 : u * q ^ 2 ∣ N.factorization s + 1 := by
      rw [hk, mul_comm (q ^ v)]
      exact Nat.mul_dvd_mul huk hvd
    have hqq : q ∣ q ^ 2 := dvd_pow_self q two_ne_zero
    have huq1 : u * q ∣ N.factorization s + 1 :=
      (Nat.mul_dvd_mul_left u hqq).trans huq2
    have e1 : q < q ^ 2 := by nlinarith
    have e2 : q < u * q := by nlinarith
    have e3 : q ^ 2 < u * q ^ 2 := by nlinarith
    have e4 : u * q < u * q ^ 2 := by nlinarith
    have e5 : q ^ 2 ≠ u * q := by
      intro he
      rw [sq] at he
      exact huq (Nat.eq_of_mul_eq_mul_right (by omega) he).symm
    have h4 := card_le_card_erase_of_dvd_succ (q := q) h (by omega) (hSN s hs)
      {q, q ^ 2, u * q, u * q ^ 2}
      (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> omega)
      (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact dvd_rfl
        · exact hqq
        · exact dvd_mul_left q u
        · exact hqq.mul_left u)
      (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact hqq.trans (hvd.trans ⟨k, hk⟩)
        · exact hvd.trans ⟨k, hk⟩
        · exact huq1
        · exact huq2)
    rw [card_four (by omega) (by omega) (by omega) e5 (by omega) (by omega)] at h4
    change 4 ≤ (S.erase s).card at h4
    rw [Finset.card_erase_of_mem hs, hS4] at h4
    omega
  refine ⟨hA, hS4, r, hrS, ?_, fun s hs hsr => ?_⟩
  · rw [hpure r hrS, ← hfS r hrS, hr3]
  · rw [hpure s hs, ← hfS s hs, hrest s hs hsr]

/-- The remaining gap in the square case of the fifth power theorem. Let `N` be an odd perfect
number with special prime `q` and `q ^ 2 ∣ e_p + 1` for every ordinary prime `p`. Then either
`q ^ 10 ∣ N`, or `v_q(N) = 9` and the normal form of `kanold_square_normal_form` holds. The
known proof excludes the second alternative by a further Diophantine step that is not
formalized here. -/
theorem pow_ten_dvd_or_normal_form {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → q ^ 2 ∣ N.factorization p + 1) :
    q ^ 10 ∣ N ∨
      (N.factorization q = 9 ∧
        (∀ p ∈ N.primeFactors, p ≠ q → q ∣ σ 1 (p ^ N.factorization p) →
            p ∈ N.primeFactors.filter (fun p => p % q = 1)) ∧
          (N.primeFactors.filter (fun p => p % q = 1)).card = 4 ∧
          ∃ r ∈ N.primeFactors.filter (fun p => p % q = 1), N.factorization r + 1 = q ^ 3 ∧
            ∀ s ∈ N.primeFactors.filter (fun p => p % q = 1), s ≠ r →
              N.factorization s + 1 = q ^ 2) := by
  by_cases h9 : N.factorization q = 9
  · exact Or.inr ⟨h9, kanold_square_normal_form h hq hodd hexp h9⟩
  · left
    have h1 := mul_succ_le_factorization_special h hq hodd hexp
    have h4 := (mod_four_special h hq hodd).2
    rw [hq.pow_dvd_iff_le_factorization h.ne_zero]
    norm_num at h1
    omega

end OddPerfect

#print axioms OddPerfect.card_le_card_erase_of_dvd_succ
#print axioms OddPerfect.kanold_square_normal_form
#print axioms OddPerfect.pow_ten_dvd_or_normal_form
