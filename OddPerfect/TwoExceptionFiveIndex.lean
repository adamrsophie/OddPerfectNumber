import OddPerfect.TwoExceptionThreeB
import OddPerfect.MixedIndexThree
import OddPerfect.Network
import OddPerfect.SpecialPrime
import OddPerfect.Phi3

/-!
# Special prime 5 with at most two ordinary exceptions: the index at 3

Let `N` be an odd perfect number with special prime `5` in which every prime factor other than
`5`, `r₁` and `r₂` has exponent exactly `2` (a restricted family). Write `β = v_3(N)`.

* Normal form (`two_exceptions_five_normal_form`): the exceptions are `3` and a prime
  `s ≡ 1 (mod 5)` whose index `v_s(N) + 1` is divisible by `5`, and `β + 1` is prime to `105`.
  The sender `s` comes from a sigma edge into `5`; the coprimality comes from the mixed index
  theorem `MixedIndexThree.exists_index_coprime_105`, since every other row has index `3` or an
  index divisible by `5`.
* Index exclusions (`two_exceptions_five_index_three_exclusions`): no prime `l ≤ 31` divides
  `β + 1`. For `l` from `11` to `31` a prime factor of `σ(3^(l-1))` starts a short chain of
  forced primes (rows of exponent `2`, and the row `Φ₅(s)` of `s`) that ends at `7`, which does
  not divide `N` because `3` and `5` do.
* Corollary (`two_exceptions_five_thirtysix_le_three`): `β ≥ 36`.

The exponent of `3` remains unbounded: nothing here gives an upper bound for `β`. Whether these
statements are new has not been verified against the literature.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace TwoExceptionFiveIndex

/-- `2 · (1 + 3 + ⋯ + 3^(n-1)) + 1 = 3^n`. -/
private theorem geom_three (n : ℕ) : 2 * (∑ i ∈ Finset.range n, 3 ^ i) + 1 = 3 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- The context of the index exclusions: the normal form together with `7 ∤ N`. -/
structure Ctx (N s : ℕ) : Prop where
  h : OddPerfect N
  hs : s.Prime
  hmod : s % 5 = 1
  hidx : 5 ∣ N.factorization s + 1
  hsq : ∀ p ∈ N.primeFactors, p ≠ 5 → p ≠ 3 → p ≠ s → N.factorization p = 2
  h7 : ¬ 7 ∣ N

namespace Ctx

variable {N s : ℕ}

/-- A square row forces the odd prime factors of `p^2 + p + 1`. -/
theorem sq (C : Ctx N s) {p t : ℕ} (hp : p.Prime) (hpN : p ∣ N) (hp3 : p ≠ 3) (hp5 : p ≠ 5)
    (hps : p ≠ s) (ht : t.Prime) (ht2 : t ≠ 2) (hd : t ∣ p ^ 2 + p + 1) : t ∣ N :=
  OPNStarter.force_prime C.h.perfect hp
    (C.hsq p (Nat.mem_primeFactors.mpr ⟨hp, hpN, C.h.perfect.2.ne'⟩) hp5 hp3 hps) ht ht2
    (by rw [sigma_prime_sq hp]; exact hd)

/-- The row of `s` forces the odd prime factors of `Φ₅(s)`. -/
theorem five (C : Ctx N s) {t : ℕ} (ht : t.Prime) (ht2 : t ≠ 2)
    (hd : t ∣ s ^ 4 + s ^ 3 + s ^ 2 + s + 1) : t ∣ N := by
  have e : σ 1 (s ^ 4) = s ^ 4 + s ^ 3 + s ^ 2 + s + 1 := by
    rw [sigma_one_apply_prime_pow C.hs]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  exact OPNStarter.force_prime C.h.perfect C.hs rfl ht ht2
    ((e ▸ hd).trans (OPNExample.sigma_prime_pow_dvd C.hs (show 4 + 1 ∣ _ from C.hidx)))

/-- If `a + 1` divides the index of `3`, the odd prime factors of `σ(3^a)` divide `N`. -/
theorem three (C : Ctx N s) {a t : ℕ} (ha : a + 1 ∣ N.factorization 3 + 1) (ht : t.Prime)
    (ht2 : t ≠ 2) (hd : t ∣ (3 ^ (a + 1) - 1) / 2) : t ∣ N := by
  have e : σ 1 (3 ^ a) = (3 ^ (a + 1) - 1) / 2 := by
    rw [sigma_one_apply_prime_pow Nat.prime_three]
    have := geom_three (a + 1)
    omega
  exact OPNStarter.force_prime C.h.perfect Nat.prime_three rfl ht ht2
    ((e ▸ hd).trans (OPNExample.sigma_prime_pow_dvd Nat.prime_three ha))

/-- A prime not congruent to `1` modulo `5` is not `s`. -/
theorem ne_s (C : Ctx N s) {p : ℕ} (hp : p % 5 ≠ 1) : p ≠ s := fun e => hp (e ▸ C.hmod)

/-- A prime factor `p ∉ {3, 5}` with `7 ∣ p^2 + p + 1` is `s`. -/
theorem eq_s (C : Ctx N s) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (hp3 : p ≠ 3) (hp5 : p ≠ 5)
    (hd : 7 ∣ p ^ 2 + p + 1) : p = s := by
  by_contra hps
  exact C.h7 (C.sq hp hpN hp3 hp5 hps (by norm_num) (by norm_num) hd)

end Ctx

variable {N s : ℕ}

/-- `l = 11`: `23 ∣ σ(3^10)`, `23 ≢ 1 (mod 5)` is a square row, and `7 ∣ Φ₃(23)`. -/
theorem not_eleven (C : Ctx N s) (hl : 11 ∣ N.factorization 3 + 1) : False := by
  have p23 : Nat.Prime 23 := by norm_num
  have d23 : 23 ∣ N := C.three (a := 10) hl p23 (by norm_num) (by decide +kernel)
  exact C.h7 (C.sq p23 d23 (by norm_num) (by norm_num) (C.ne_s (by norm_num)) (by norm_num)
    (by norm_num) (by decide +kernel))

/-- `l = 13`: `σ(3^12) = 797161`. If `s = 797161` then `2671 ∣ Φ₅(s)` and `7 ∣ Φ₃(2671)`; otherwise
`151 ∣ Φ₃(797161)` forces `s = 151`, then `104670301 ∣ Φ₅(151)`, `1549 ∣ Φ₃(104670301)` and
`7 ∣ Φ₃(1549)`. -/
theorem not_thirteen (C : Ctx N s) (hl : 13 ∣ N.factorization 3 + 1) : False := by
  have pQ : Nat.Prime 797161 := by norm_num
  have p2671 : Nat.Prime 2671 := by norm_num
  have p151 : Nat.Prime 151 := by norm_num
  have pR : Nat.Prime 104670301 := by norm_num
  have p1549 : Nat.Prime 1549 := by norm_num
  have dQ : 797161 ∣ N := C.three (a := 12) hl pQ (by norm_num) (by decide +kernel)
  by_cases hQ : 797161 = s
  · subst hQ
    have d := C.five p2671 (by norm_num) (by decide +kernel)
    exact C.h7 (C.sq p2671 d (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel))
  · have d151 := C.sq pQ dQ (by norm_num) (by norm_num) hQ p151 (by norm_num)
      (by decide +kernel)
    have e : 151 = s := C.eq_s p151 d151 (by norm_num) (by norm_num) (by decide +kernel)
    subst e
    have dR := C.five pR (by norm_num) (by decide +kernel)
    have d1549 := C.sq pR dR (by norm_num) (by norm_num) (by norm_num) p1549 (by norm_num)
      (by decide +kernel)
    exact C.h7 (C.sq p1549 d1549 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel))

/-- `l = 17`: `1871 ∣ σ(3^16)` forces `s = 1871`, then `151 ∣ Φ₅(1871)` and `7 ∣ Φ₃(151)`. -/
theorem not_seventeen (C : Ctx N s) (hl : 17 ∣ N.factorization 3 + 1) : False := by
  have p1871 : Nat.Prime 1871 := by norm_num
  have p151 : Nat.Prime 151 := by norm_num
  have d1871 : 1871 ∣ N := C.three (a := 16) hl p1871 (by norm_num) (by decide +kernel)
  have e : 1871 = s := C.eq_s p1871 d1871 (by norm_num) (by norm_num) (by decide +kernel)
  subst e
  have d151 := C.five p151 (by norm_num) (by decide +kernel)
  exact C.h7 (C.sq p151 d151 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel))

/-- `l = 19`: `1597 ∣ σ(3^18)`, then `73`, `1801`; this forces `s = 1801`, then `101 ∣ Φ₅(1801)`,
`10303`, `6073` and `7`. -/
theorem not_nineteen (C : Ctx N s) (hl : 19 ∣ N.factorization 3 + 1) : False := by
  have p1597 : Nat.Prime 1597 := by norm_num
  have p73 : Nat.Prime 73 := by norm_num
  have p1801 : Nat.Prime 1801 := by norm_num
  have p101 : Nat.Prime 101 := by norm_num
  have p10303 : Nat.Prime 10303 := by norm_num
  have p6073 : Nat.Prime 6073 := by norm_num
  have d1597 : 1597 ∣ N := C.three (a := 18) hl p1597 (by norm_num) (by decide +kernel)
  have d73 := C.sq p1597 d1597 (by norm_num) (by norm_num) (C.ne_s (by norm_num)) p73
    (by norm_num) (by decide +kernel)
  have d1801 := C.sq p73 d73 (by norm_num) (by norm_num) (C.ne_s (by norm_num)) p1801
    (by norm_num) (by decide +kernel)
  have e : 1801 = s := C.eq_s p1801 d1801 (by norm_num) (by norm_num) (by decide +kernel)
  subst e
  have d101 := C.five p101 (by norm_num) (by decide +kernel)
  have d10303 := C.sq p101 d101 (by norm_num) (by norm_num) (by norm_num) p10303 (by norm_num)
    (by decide +kernel)
  have d6073 := C.sq p10303 d10303 (by norm_num) (by norm_num) (by norm_num) p6073
    (by norm_num) (by decide +kernel)
  exact C.h7 (C.sq p6073 d6073 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel))

/-- `l = 23`: `47 ∣ σ(3^22)`, `37 ∣ Φ₃(47)` and `7 ∣ Φ₃(37)`. -/
theorem not_twentythree (C : Ctx N s) (hl : 23 ∣ N.factorization 3 + 1) : False := by
  have p47 : Nat.Prime 47 := by norm_num
  have p37 : Nat.Prime 37 := by norm_num
  have d47 : 47 ∣ N := C.three (a := 22) hl p47 (by norm_num) (by decide +kernel)
  have d37 := C.sq p47 d47 (by norm_num) (by norm_num) (C.ne_s (by norm_num)) p37
    (by norm_num) (by decide +kernel)
  exact C.h7 (C.sq p37 d37 (by norm_num) (by norm_num) (C.ne_s (by norm_num)) (by norm_num)
    (by norm_num) (by decide +kernel))

/-- `l = 29`: `28537 ∣ σ(3^28)`, `37 ∣ Φ₃(28537)` and `7 ∣ Φ₃(37)`. -/
theorem not_twentynine (C : Ctx N s) (hl : 29 ∣ N.factorization 3 + 1) : False := by
  have p28537 : Nat.Prime 28537 := by norm_num
  have p37 : Nat.Prime 37 := by norm_num
  have d28537 : 28537 ∣ N := C.three (a := 28) hl p28537 (by norm_num) (by decide +kernel)
  have d37 := C.sq p28537 d28537 (by norm_num) (by norm_num) (C.ne_s (by norm_num)) p37
    (by norm_num) (by decide +kernel)
  exact C.h7 (C.sq p37 d37 (by norm_num) (by norm_num) (C.ne_s (by norm_num)) (by norm_num)
    (by norm_num) (by decide +kernel))

/-- `l = 31`: `683 ∣ σ(3^30)` and `7 ∣ Φ₃(683)`. -/
theorem not_thirtyone (C : Ctx N s) (hl : 31 ∣ N.factorization 3 + 1) : False := by
  have p683 : Nat.Prime 683 := by norm_num
  have d683 : 683 ∣ N := C.three (a := 30) hl p683 (by norm_num) (by decide +kernel)
  exact C.h7 (C.sq p683 d683 (by norm_num) (by norm_num) (C.ne_s (by norm_num)) (by norm_num)
    (by norm_num) (by decide +kernel))

end TwoExceptionFiveIndex

/-- Normal form for the restricted family with special prime `5` and at most two ordinary
exceptions `r₁, r₂` (not assumed prime or distinct): the exceptions are `3` and a prime
`s ≡ 1 (mod 5)` whose index `v_s(N) + 1` is divisible by `5`, and the index `v_3(N) + 1` is prime
to `105`. The exponent of `3` remains unbounded. Whether this statement is new has not been
verified. -/
theorem two_exceptions_five_normal_form {N r₁ r₂ : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization 5))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ 5 → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2) :
    ∃ s, s.Prime ∧ s ∈ N.primeFactors ∧ s % 5 = 1 ∧ 5 ∣ N.factorization s + 1 ∧
      (∀ p ∈ N.primeFactors, p ≠ 5 → p ≠ 3 → p ≠ s → N.factorization p = 2) ∧
      Nat.Coprime (N.factorization 3 + 1) 105 := by
  have hN0 : N ≠ 0 := h.perfect.2.ne'
  have h6 := two_exceptions_five_six_le_three h hodd hsq
  have h3m : 3 ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_three, Nat.dvd_of_factorization_pos (by omega), hN0⟩
  have h3r : 3 = r₁ ∨ 3 = r₂ := by
    by_contra hc
    push Not at hc
    have := hsq 3 h3m (by norm_num) hc.1 hc.2
    omega
  have h5m : 5 ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_five, Nat.dvd_of_factorization_pos hodd.pos.ne', hN0⟩
  obtain ⟨s, hs5, hsm, -, hd⟩ := exists_sigmaEdge_into h.perfect h5m (by norm_num)
  have hsp := Nat.prime_of_mem_primeFactors hsm
  have hev := even_factorization_of_ne h Nat.prime_five hodd hsp hs5
  obtain ⟨hmod, hidx⟩ := TwoExceptionThree.five_sender_mod hsp hs5 hev hd
  have hs3 : s ≠ 3 := by
    rintro rfl
    norm_num at hmod
  have hsr : s = r₁ ∨ s = r₂ := by
    by_contra hc
    push Not at hc
    have := hsq s hsm hs5 hc.1 hc.2
    rw [this] at hidx
    norm_num at hidx
  have hsq' : ∀ p ∈ N.primeFactors, p ≠ 5 → p ≠ 3 → p ≠ s → N.factorization p = 2 := by
    intro p hp hp5 hp3 hps
    refine hsq p hp hp5 ?_ ?_ <;> intro he <;> omega
  obtain ⟨p, hpm, hp5, hcop⟩ := MixedIndexThree.exists_index_coprime_105 h hodd
  have hp3 : p = 3 := by
    by_contra hp3
    by_cases hps : p = s
    · subst hps
      exact absurd (Nat.Coprime.coprime_dvd_left hidx hcop) (by decide)
    · rw [hsq' p hpm hp5 hp3 hps] at hcop
      exact absurd hcop (by decide)
  subst hp3
  exact ⟨s, hsp, hsm, hmod, hidx, hsq', hcop⟩

/-- In the restricted family with special prime `5` and at most two ordinary exceptions, no prime
`l ≤ 31` divides the index `v_3(N) + 1`. The exponent of `3` remains unbounded. Whether this
statement is new has not been verified. -/
theorem two_exceptions_five_index_three_exclusions {N r₁ r₂ : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization 5))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ 5 → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2) :
    ∀ l, l.Prime → l ≤ 31 → ¬ l ∣ N.factorization 3 + 1 := by
  obtain ⟨s, hsp, hsm, hmod, hidx, hsq', hcop⟩ := two_exceptions_five_normal_form h hodd hsq
  have h6 := two_exceptions_five_six_le_three h hodd hsq
  have h3 : 3 ∣ N := Nat.dvd_of_factorization_pos (by omega)
  have h5 : 5 ∣ N := Nat.dvd_of_factorization_pos hodd.pos.ne'
  have C : TwoExceptionFiveIndex.Ctx N s :=
    ⟨h, hsp, hmod, hidx, hsq', not_seven_dvd_of_three_five h h3 h5⟩
  obtain ⟨k, hk⟩ := even_factorization_of_ne h Nat.prime_five hodd Nat.prime_three (by norm_num)
  have g : Nat.gcd (N.factorization 3 + 1) 105 = 1 := hcop
  have hc : ∀ d, d ∣ N.factorization 3 + 1 → d ∣ 105 → d = 1 := fun d h1 h2 =>
    Nat.dvd_one.mp (g ▸ Nat.dvd_gcd h1 h2)
  intro l hl hl31 hd
  interval_cases l <;> try norm_num at hl
  · omega
  · exact absurd (hc _ hd (by norm_num)) (by norm_num)
  · exact absurd (hc _ hd (by norm_num)) (by norm_num)
  · exact absurd (hc _ hd (by norm_num)) (by norm_num)
  · exact TwoExceptionFiveIndex.not_eleven C hd
  · exact TwoExceptionFiveIndex.not_thirteen C hd
  · exact TwoExceptionFiveIndex.not_seventeen C hd
  · exact TwoExceptionFiveIndex.not_nineteen C hd
  · exact TwoExceptionFiveIndex.not_twentythree C hd
  · exact TwoExceptionFiveIndex.not_twentynine C hd
  · exact TwoExceptionFiveIndex.not_thirtyone C hd

/-- In the restricted family with special prime `5` and at most two ordinary exceptions,
`v_3(N) ≥ 36`. The exponent of `3` remains unbounded above. Whether this statement is new has
not been verified. -/
theorem two_exceptions_five_thirtysix_le_three {N r₁ r₂ : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization 5))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ 5 → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2) :
    36 ≤ N.factorization 3 := by
  have E := two_exceptions_five_index_three_exclusions h hodd hsq
  have h6 := two_exceptions_five_six_le_three h hodd hsq
  obtain ⟨k, hk⟩ := even_factorization_of_ne h Nat.prime_five hodd Nat.prime_three (by norm_num)
  have e3 := E 3 (by norm_num) (by norm_num)
  have e5 := E 5 (by norm_num) (by norm_num)
  have e7 := E 7 (by norm_num) (by norm_num)
  have e11 := E 11 (by norm_num) (by norm_num)
  have e13 := E 13 (by norm_num) (by norm_num)
  have e17 := E 17 (by norm_num) (by norm_num)
  have e19 := E 19 (by norm_num) (by norm_num)
  have e23 := E 23 (by norm_num) (by norm_num)
  have e29 := E 29 (by norm_num) (by norm_num)
  have e31 := E 31 (by norm_num) (by norm_num)
  by_contra hlt
  have hk18 : k < 18 := by omega
  interval_cases k <;> omega

end OddPerfect

#print axioms OddPerfect.TwoExceptionFiveIndex.Ctx.sq
#print axioms OddPerfect.TwoExceptionFiveIndex.Ctx.five
#print axioms OddPerfect.TwoExceptionFiveIndex.Ctx.three
#print axioms OddPerfect.TwoExceptionFiveIndex.Ctx.ne_s
#print axioms OddPerfect.TwoExceptionFiveIndex.Ctx.eq_s
#print axioms OddPerfect.TwoExceptionFiveIndex.not_eleven
#print axioms OddPerfect.TwoExceptionFiveIndex.not_thirteen
#print axioms OddPerfect.TwoExceptionFiveIndex.not_seventeen
#print axioms OddPerfect.TwoExceptionFiveIndex.not_nineteen
#print axioms OddPerfect.TwoExceptionFiveIndex.not_twentythree
#print axioms OddPerfect.TwoExceptionFiveIndex.not_twentynine
#print axioms OddPerfect.TwoExceptionFiveIndex.not_thirtyone
#print axioms OddPerfect.two_exceptions_five_normal_form
#print axioms OddPerfect.two_exceptions_five_index_three_exclusions
#print axioms OddPerfect.two_exceptions_five_thirtysix_le_three
