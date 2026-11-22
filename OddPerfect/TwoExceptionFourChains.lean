import OddPerfect.TwoExceptionFourMod
import OddPerfect.Phi3

/-!
# Two exceptional exponents, exponent 4 at 3: no prime below 79 besides 3 and 11

Let `N` be an odd perfect number with special prime `q`, `v_3(N) = 4`, and every prime factor
other than `q`, `r₁` and `r₂` of exponent exactly 2 (a restricted family). By the landed modules
the exceptions are `3` and `11`, and `q ≡ 1 (mod 12)`. Call a prime factor other than `q`, `3`
and `11` a square prime; it has exponent 2.

* A square row forces the prime factors of `p^2 + p + 1`; those other than 3 are `1` modulo 3,
  so each is `q` or a square prime `≡ 1 (mod 3)`.
* The row of `q` forces the odd prime factors of `q + 1`, since `q + 1 ∣ σ(q^α)` for odd `α`.
* At most four square primes are `≡ 1 (mod 3)`, because each sends a factor 3 and `v_3(N) = 4`
  (`card_exact_sq_modEq_one_le`).

From these three facts a short forcing chain excludes each prime `5 ≤ x ≤ 73` other than 11, in
increasing order, each step using the earlier exclusions. A prime `≢ 1 (mod 12)` is never `q`;
a forced prime `≡ 1 (mod 12)` is split into the cases `= q` and `≠ q`.

The family is restricted; nothing about odd perfect numbers in general is claimed. Whether these
statements are new was not verified against the literature.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace TwoExceptionFourChains

/-- The normal form of the family: special prime `q ≡ 1 (mod 12)`, `v_3(N) = 4`, and every prime
factor other than `q`, `3` and `11` of exponent 2. -/
structure Ctx (N q : ℕ) : Prop where
  h : OddPerfect N
  hq : q.Prime
  hq12 : q % 12 = 1
  hodd : Odd (N.factorization q)
  h34 : N.factorization 3 = 4
  hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ 3 → p ≠ 11 → N.factorization p = 2

namespace Ctx

variable {N q : ℕ}

/-- A prime not `1` modulo `12` is not `q`. -/
theorem ne_q (C : Ctx N q) {p : ℕ} (hp : p % 12 ≠ 1) : p ≠ q := fun e => hp (e ▸ C.hq12)

/-- A square row forces the prime factors of `p^2 + p + 1`. -/
theorem sq (C : Ctx N q) {p t : ℕ} (hp : p.Prime) (hpN : p ∣ N) (hpq : p ≠ q) (hp3 : p ≠ 3)
    (hp11 : p ≠ 11) (ht : t.Prime) (hd : t ∣ p ^ 2 + p + 1) : t ∣ N :=
  OPNStarter.force_prime C.h.perfect hp
    (C.hsq p (Nat.mem_primeFactors.mpr ⟨hp, hpN, C.h.ne_zero⟩) hpq hp3 hp11) ht
    (fun e => by
      subst e
      exact (Nat.not_even_iff_odd.mpr (phi3_odd p)) (even_iff_two_dvd.mpr hd))
    (by rw [sigma_prime_sq hp]; exact hd)

/-- The row of `q` forces the odd prime factors of `q + 1`. -/
theorem qrow (C : Ctx N q) {t : ℕ} (ht : t.Prime) (ht2 : t ≠ 2) (hd : t ∣ q + 1) : t ∣ N := by
  have h2 : 1 + 1 ∣ N.factorization q + 1 := by
    obtain ⟨k, hk⟩ := C.hodd
    exact ⟨k + 1, by omega⟩
  have e : σ 1 (q ^ 1) = q + 1 := by
    rw [sigma_one_apply_prime_pow C.hq, Finset.sum_range_succ, Finset.sum_range_one]
    ring
  exact OPNStarter.force_prime C.h.perfect C.hq rfl ht ht2
    ((e ▸ hd).trans (OPNExample.sigma_prime_pow_dvd C.hq h2))

/-- Five distinct square primes `≡ 1 (mod 3)` are impossible, since `v_3(N) = 4`. -/
theorem fifth (C : Ctx N q) {a b c d e : ℕ}
    (ha : a.Prime ∧ a ∣ N ∧ a % 3 = 1 ∧ a ≠ q) (hb : b.Prime ∧ b ∣ N ∧ b % 3 = 1 ∧ b ≠ q)
    (hc : c.Prime ∧ c ∣ N ∧ c % 3 = 1 ∧ c ≠ q) (hd : d.Prime ∧ d ∣ N ∧ d % 3 = 1 ∧ d ≠ q)
    (he : e.Prime ∧ e ∣ N ∧ e % 3 = 1 ∧ e ≠ q) (hnd : [a, b, c, d, e].Nodup) : False := by
  have key : [a, b, c, d, e].toFinset ⊆
      N.primeFactors.filter (fun p => N.factorization p = 2 ∧ p % 3 = 1) := by
    intro p hp
    have H : p.Prime ∧ p ∣ N ∧ p % 3 = 1 ∧ p ≠ q := by
      simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨hp, hpN, h3, hpq⟩ := H
    have hm := Nat.mem_primeFactors.mpr ⟨hp, hpN, C.h.ne_zero⟩
    exact Finset.mem_filter.mpr ⟨hm, C.hsq p hm hpq (by omega) (by omega), h3⟩
  have h1 := Finset.card_le_card key
  rw [List.toFinset_card_of_nodup hnd] at h1
  have h2 := card_exact_sq_modEq_one_le C.h
  rw [C.h34] at h2
  simp only [List.length_cons, List.length_nil] at h1
  omega

/-- Membership data for a square prime that is `7` modulo `12`. -/
theorem mem7 (C : Ctx N q) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (h : p % 12 = 7) :
    p.Prime ∧ p ∣ N ∧ p % 3 = 1 ∧ p ≠ q :=
  ⟨hp, hpN, by omega, C.ne_q (by omega)⟩

/-- Membership data for a square prime that is `1` modulo `3` and not `q`. -/
theorem memA {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (h : p % 3 = 1) (hpq : p ≠ q) :
    p.Prime ∧ p ∣ N ∧ p % 3 = 1 ∧ p ≠ q :=
  ⟨hp, hpN, h, hpq⟩

end Ctx

variable {N q : ℕ}

/-- `x = 5`: `5 → 31 → 331 → 7 → 19 → 127` gives five square primes `≡ 7 (mod 12)`. -/
theorem not5 (C : Ctx N q) : ¬ 5 ∣ N := by
  intro d5
  have p31 : Nat.Prime 31 := by norm_num
  have p331 : Nat.Prime 331 := by norm_num
  have p7 : Nat.Prime 7 := by norm_num
  have p19 : Nat.Prime 19 := by norm_num
  have p127 : Nat.Prime 127 := by norm_num
  have d31 := C.sq Nat.prime_five d5 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p31
    (by norm_num)
  have d331 := C.sq p31 d31 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p331
    (by norm_num)
  have d7 := C.sq p331 d331 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p7
    (by norm_num)
  have d19 := C.sq p7 d7 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p19 (by norm_num)
  have d127 := C.sq p19 d19 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p127
    (by norm_num)
  exact C.fifth (C.mem7 p31 d31 (by norm_num)) (C.mem7 p331 d331 (by norm_num))
    (C.mem7 p7 d7 (by norm_num)) (C.mem7 p19 d19 (by norm_num))
    (C.mem7 p127 d127 (by norm_num)) (by decide)

/-- `x = 7`: `7 → 19 → 127 → 5419 → 31` gives five square primes `≡ 7 (mod 12)`. -/
theorem not7 (C : Ctx N q) : ¬ 7 ∣ N := by
  intro d7
  have p7 : Nat.Prime 7 := by norm_num
  have p19 : Nat.Prime 19 := by norm_num
  have p127 : Nat.Prime 127 := by norm_num
  have p5419 : Nat.Prime 5419 := by norm_num
  have p31 : Nat.Prime 31 := by norm_num
  have d19 := C.sq p7 d7 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p19 (by norm_num)
  have d127 := C.sq p19 d19 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p127
    (by norm_num)
  have d5419 := C.sq p127 d127 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p5419
    (by norm_num)
  have d31 := C.sq p5419 d5419 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p31
    (by norm_num)
  exact C.fifth (C.mem7 p7 d7 (by norm_num)) (C.mem7 p19 d19 (by norm_num))
    (C.mem7 p127 d127 (by norm_num)) (C.mem7 p5419 d5419 (by norm_num))
    (C.mem7 p31 d31 (by norm_num)) (by decide)

/-- `x = 13`: if `13 = q` then `7 ∣ q + 1`. Otherwise `13 → 61 → 97 → 3169 → 3348577`, each of
these `≡ 1 (mod 12)`; the cases `61 = q`, `97 = q`, `3169 = q` force `31` (then `331` and `7`),
`7` and `5`; the case `3348577 = q` forces `1674289 ∣ q + 1`; in the remaining cases five square
primes `≡ 1 (mod 3)` appear. -/
theorem not13 (C : Ctx N q) (h5 : ¬ 5 ∣ N) (h7 : ¬ 7 ∣ N) : ¬ 13 ∣ N := by
  intro d13
  have p13 : Nat.Prime 13 := by norm_num
  have p7 : Nat.Prime 7 := by norm_num
  have p31 : Nat.Prime 31 := by norm_num
  have p331 : Nat.Prime 331 := by norm_num
  have p61 : Nat.Prime 61 := by norm_num
  have p97 : Nat.Prime 97 := by norm_num
  have p3169 : Nat.Prime 3169 := by norm_num
  have pB : Nat.Prime 3348577 := by norm_num
  have pC : Nat.Prime 1674289 := by norm_num
  by_cases e13 : 13 = q
  · subst e13
    exact h7 (C.qrow p7 (by norm_num) (by norm_num))
  have d61 := C.sq p13 d13 e13 (by norm_num) (by norm_num) p61 (by norm_num)
  by_cases e61 : 61 = q
  · subst e61
    have d31 := C.qrow p31 (by norm_num) (by norm_num)
    have d331 := C.sq p31 d31 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p331
      (by norm_num)
    exact h7 (C.sq p331 d331 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p7
      (by norm_num))
  have d97 := C.sq p61 d61 e61 (by norm_num) (by norm_num) p97 (by norm_num)
  by_cases e97 : 97 = q
  · subst e97
    exact h7 (C.qrow p7 (by norm_num) (by norm_num))
  have d3169 := C.sq p97 d97 e97 (by norm_num) (by norm_num) p3169 (by norm_num)
  by_cases e3169 : 3169 = q
  · subst e3169
    exact h5 (C.qrow Nat.prime_five (by norm_num) (by norm_num))
  have dB := C.sq p3169 d3169 e3169 (by norm_num) (by norm_num) pB (by norm_num)
  by_cases eB : 3348577 = q
  · subst eB
    have dC := C.qrow pC (by norm_num) (by norm_num)
    exact C.fifth (Ctx.memA p13 d13 (by norm_num) e13) (Ctx.memA p61 d61 (by norm_num) e61)
      (Ctx.memA p97 d97 (by norm_num) e97) (Ctx.memA p3169 d3169 (by norm_num) e3169)
      (Ctx.memA pC dC (by norm_num) (by norm_num)) (by decide)
  exact C.fifth (Ctx.memA p13 d13 (by norm_num) e13) (Ctx.memA p61 d61 (by norm_num) e61)
    (Ctx.memA p97 d97 (by norm_num) e97) (Ctx.memA p3169 d3169 (by norm_num) e3169)
    (Ctx.memA pB dB (by norm_num) eB) (by decide)

/-- `x = 17`: `17 → 307 → 43 → 631` and `307 → 733`. If `733 = q` then `367 ∣ q + 1` and
`631 → 433`; otherwise `733 → 19`. Either way five square primes `≡ 1 (mod 3)` appear. -/
theorem not17 (C : Ctx N q) : ¬ 17 ∣ N := by
  intro d17
  have p17 : Nat.Prime 17 := by norm_num
  have p307 : Nat.Prime 307 := by norm_num
  have p43 : Nat.Prime 43 := by norm_num
  have p631 : Nat.Prime 631 := by norm_num
  have p733 : Nat.Prime 733 := by norm_num
  have p367 : Nat.Prime 367 := by norm_num
  have p433 : Nat.Prime 433 := by norm_num
  have p19 : Nat.Prime 19 := by norm_num
  have d307 := C.sq p17 d17 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p307
    (by norm_num)
  have d43 := C.sq p307 d307 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p43
    (by norm_num)
  have d631 := C.sq p43 d43 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p631
    (by norm_num)
  have d733 := C.sq p307 d307 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p733
    (by norm_num)
  by_cases e733 : 733 = q
  · subst e733
    have d367 := C.qrow p367 (by norm_num) (by norm_num)
    have d433 := C.sq p631 d631 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p433
      (by norm_num)
    exact C.fifth (C.mem7 p307 d307 (by norm_num)) (C.mem7 p43 d43 (by norm_num))
      (C.mem7 p631 d631 (by norm_num)) (Ctx.memA p367 d367 (by norm_num) (by norm_num))
      (Ctx.memA p433 d433 (by norm_num) (by norm_num)) (by decide)
  have d19 := C.sq p733 d733 e733 (by norm_num) (by norm_num) p19 (by norm_num)
  exact C.fifth (C.mem7 p307 d307 (by norm_num)) (C.mem7 p43 d43 (by norm_num))
    (C.mem7 p631 d631 (by norm_num)) (Ctx.memA p733 d733 (by norm_num) e733)
    (C.mem7 p19 d19 (by norm_num)) (by decide)

/-- `x = 19`: `19 → 127 → 5419 → 31, 313, 1009`; `313` and `1009` are `1` modulo 12 and at most
one of them is `q`, so five square primes `≡ 1 (mod 3)` appear. -/
theorem not19 (C : Ctx N q) : ¬ 19 ∣ N := by
  intro d19
  have p19 : Nat.Prime 19 := by norm_num
  have p127 : Nat.Prime 127 := by norm_num
  have p5419 : Nat.Prime 5419 := by norm_num
  have p31 : Nat.Prime 31 := by norm_num
  have p313 : Nat.Prime 313 := by norm_num
  have p1009 : Nat.Prime 1009 := by norm_num
  have d127 := C.sq p19 d19 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p127
    (by norm_num)
  have d5419 := C.sq p127 d127 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p5419
    (by norm_num)
  have d31 := C.sq p5419 d5419 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p31
    (by norm_num)
  have d313 := C.sq p5419 d5419 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p313
    (by norm_num)
  have d1009 := C.sq p5419 d5419 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p1009
    (by norm_num)
  by_cases e313 : 313 = q
  · subst e313
    exact C.fifth (C.mem7 p19 d19 (by norm_num)) (C.mem7 p127 d127 (by norm_num))
      (C.mem7 p5419 d5419 (by norm_num)) (C.mem7 p31 d31 (by norm_num))
      (Ctx.memA p1009 d1009 (by norm_num) (by norm_num)) (by decide)
  exact C.fifth (C.mem7 p19 d19 (by norm_num)) (C.mem7 p127 d127 (by norm_num))
    (C.mem7 p5419 d5419 (by norm_num)) (C.mem7 p31 d31 (by norm_num))
    (Ctx.memA p313 d313 (by norm_num) e313) (by decide)

/-- `x = 23`: `7 ∣ 23^2 + 23 + 1`. -/
theorem not23 (C : Ctx N q) (h7 : ¬ 7 ∣ N) : ¬ 23 ∣ N := fun d =>
  h7 (C.sq (by norm_num) d (C.ne_q (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num))

/-- `x = 29`: `13 ∣ 29^2 + 29 + 1`. -/
theorem not29 (C : Ctx N q) (h13 : ¬ 13 ∣ N) : ¬ 29 ∣ N := fun d =>
  h13 (C.sq (by norm_num) d (C.ne_q (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num))

/-- `x = 31`: `31 → 331 → 7`. -/
theorem not31 (C : Ctx N q) (h7 : ¬ 7 ∣ N) : ¬ 31 ∣ N := by
  intro d31
  have p31 : Nat.Prime 31 := by norm_num
  have p331 : Nat.Prime 331 := by norm_num
  have d331 := C.sq p31 d31 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p331
    (by norm_num)
  exact h7 (C.sq p331 d331 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num))

/-- `x = 37`: if `37 = q` then `19 ∣ q + 1`; otherwise `7 ∣ 37^2 + 37 + 1`. -/
theorem not37 (C : Ctx N q) (h7 : ¬ 7 ∣ N) (h19 : ¬ 19 ∣ N) : ¬ 37 ∣ N := by
  intro d37
  by_cases e : 37 = q
  · subst e
    exact h19 (C.qrow (by norm_num) (by norm_num) (by norm_num))
  exact h7 (C.sq (by norm_num) d37 e (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- `x = 41`: `41 → 1723 → 990151 → 147739 → 7`, all `≢ 1 (mod 12)`. -/
theorem not41 (C : Ctx N q) (h7 : ¬ 7 ∣ N) : ¬ 41 ∣ N := by
  intro d41
  have p41 : Nat.Prime 41 := by norm_num
  have p1723 : Nat.Prime 1723 := by norm_num
  have pX : Nat.Prime 990151 := by norm_num
  have pY : Nat.Prime 147739 := by norm_num
  have d1723 := C.sq p41 d41 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p1723
    (by norm_num)
  have dX := C.sq p1723 d1723 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) pX
    (by norm_num)
  have dY := C.sq pX dX (C.ne_q (by norm_num)) (by norm_num) (by norm_num) pY (by norm_num)
  exact h7 (C.sq pY dY (C.ne_q (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num))

/-- `x = 43`: `43 → 631 → 433`; if `433 = q` then `7 ∣ q + 1`, otherwise `37 ∣ 433^2 + 433 + 1`. -/
theorem not43 (C : Ctx N q) (h7 : ¬ 7 ∣ N) (h37 : ¬ 37 ∣ N) : ¬ 43 ∣ N := by
  intro d43
  have p43 : Nat.Prime 43 := by norm_num
  have p631 : Nat.Prime 631 := by norm_num
  have p433 : Nat.Prime 433 := by norm_num
  have d631 := C.sq p43 d43 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p631
    (by norm_num)
  have d433 := C.sq p631 d631 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p433
    (by norm_num)
  by_cases e : 433 = q
  · subst e
    exact h7 (C.qrow (by norm_num) (by norm_num) (by norm_num))
  exact h37 (C.sq p433 d433 e (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- `x = 47`: `37 ∣ 47^2 + 47 + 1`. -/
theorem not47 (C : Ctx N q) (h37 : ¬ 37 ∣ N) : ¬ 47 ∣ N := fun d =>
  h37 (C.sq (by norm_num) d (C.ne_q (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num))

/-- `x = 53`: `7 ∣ 53^2 + 53 + 1`. -/
theorem not53 (C : Ctx N q) (h7 : ¬ 7 ∣ N) : ¬ 53 ∣ N := fun d =>
  h7 (C.sq (by norm_num) d (C.ne_q (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num))

/-- `x = 59`: `59 → 3541`; if `3541 = q` then `7 ∣ q + 1`, otherwise `19 ∣ 3541^2 + 3541 + 1`. -/
theorem not59 (C : Ctx N q) (h7 : ¬ 7 ∣ N) (h19 : ¬ 19 ∣ N) : ¬ 59 ∣ N := by
  intro d59
  have p59 : Nat.Prime 59 := by norm_num
  have p3541 : Nat.Prime 3541 := by norm_num
  have d3541 := C.sq p59 d59 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p3541
    (by norm_num)
  by_cases e : 3541 = q
  · subst e
    exact h7 (C.qrow (by norm_num) (by norm_num) (by norm_num))
  exact h19 (C.sq p3541 d3541 e (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- `x = 61`: if `61 = q` then `31 ∣ q + 1`; otherwise `13 ∣ 61^2 + 61 + 1`. -/
theorem not61 (C : Ctx N q) (h13 : ¬ 13 ∣ N) (h31 : ¬ 31 ∣ N) : ¬ 61 ∣ N := by
  intro d61
  by_cases e : 61 = q
  · subst e
    exact h31 (C.qrow (by norm_num) (by norm_num) (by norm_num))
  exact h13 (C.sq (by norm_num) d61 e (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- `x = 67`: `7 ∣ 67^2 + 67 + 1`. -/
theorem not67 (C : Ctx N q) (h7 : ¬ 7 ∣ N) : ¬ 67 ∣ N := fun d =>
  h7 (C.sq (by norm_num) d (C.ne_q (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num))

/-- `x = 71`: `71 → 5113`. If `5113 = q` then `2557 ∣ q + 1` and `7 ∣ 2557^2 + 2557 + 1`.
Otherwise `5113 → 8715961`; if `8715961 = q` then `47 ∣ q + 1`, otherwise
`7 ∣ 8715961^2 + 8715961 + 1`. -/
theorem not71 (C : Ctx N q) (h7 : ¬ 7 ∣ N) (h47 : ¬ 47 ∣ N) : ¬ 71 ∣ N := by
  intro d71
  have p71 : Nat.Prime 71 := by norm_num
  have p5113 : Nat.Prime 5113 := by norm_num
  have p2557 : Nat.Prime 2557 := by norm_num
  have pZ : Nat.Prime 8715961 := by norm_num
  have d5113 := C.sq p71 d71 (C.ne_q (by norm_num)) (by norm_num) (by norm_num) p5113
    (by norm_num)
  by_cases e : 5113 = q
  · subst e
    have d2557 := C.qrow p2557 (by norm_num) (by norm_num)
    exact h7 (C.sq p2557 d2557 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
  have dZ := C.sq p5113 d5113 e (by norm_num) (by norm_num) pZ (by norm_num)
  by_cases e' : 8715961 = q
  · subst e'
    exact h47 (C.qrow (by norm_num) (by norm_num) (by norm_num))
  exact h7 (C.sq pZ dZ e' (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- `x = 73`: if `73 = q` then `37 ∣ q + 1`. Otherwise `73 → 1801`; if `1801 = q` then
`17 ∣ q + 1`, otherwise `7 ∣ 1801^2 + 1801 + 1`. -/
theorem not73 (C : Ctx N q) (h7 : ¬ 7 ∣ N) (h17 : ¬ 17 ∣ N) (h37 : ¬ 37 ∣ N) : ¬ 73 ∣ N := by
  intro d73
  have p73 : Nat.Prime 73 := by norm_num
  have p1801 : Nat.Prime 1801 := by norm_num
  by_cases e : 73 = q
  · subst e
    exact h37 (C.qrow (by norm_num) (by norm_num) (by norm_num))
  have d1801 := C.sq p73 d73 e (by norm_num) (by norm_num) p1801 (by norm_num)
  by_cases e' : 1801 = q
  · subst e'
    exact h17 (C.qrow (by norm_num) (by norm_num) (by norm_num))
  exact h7 (C.sq p1801 d1801 e' (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- In the context, every prime factor of `N` is `3`, `11`, or at least `79`. -/
theorem small (C : Ctx N q) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) : p = 3 ∨ p = 11 ∨ 79 ≤ p := by
  have h5 := not5 C
  have h7 := not7 C
  have h13 := not13 C h5 h7
  have h17 := not17 C
  have h19 := not19 C
  have h23 := not23 C h7
  have h29 := not29 C h13
  have h31 := not31 C h7
  have h37 := not37 C h7 h19
  have h41 := not41 C h7
  have h43 := not43 C h7 h37
  have h47 := not47 C h37
  have h53 := not53 C h7
  have h59 := not59 C h7 h19
  have h61 := not61 C h13 h31
  have h67 := not67 C h7
  have h71 := not71 C h7 h47
  have h73 := not73 C h7 h17 h37
  have h2 : p ≠ 2 := by
    rintro rfl
    exact C.h.not_two_dvd hpN
  by_contra hc
  push Not at hc
  obtain ⟨n3, n11, hlt⟩ := hc
  interval_cases p <;> contradiction

/-- Build the context from the hypotheses of the family. -/
theorem Ctx.of {N q r₁ r₂ : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (h34 : N.factorization 3 = 4)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2) :
    Ctx N q := by
  have hq12 := two_exceptions_three_pow_four_special_mod_twelve h hq hodd h34 hsq
  obtain ⟨hr, -⟩ := two_exceptions_three_pow_four h hq hodd (by omega) h34 hsq
  refine ⟨h, hq, hq12, hodd, h34, fun p hp h1 h2 h3 => ?_⟩
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hsq p hp h1 h2 h3
  · exact hsq p hp h1 h3 h2

end TwoExceptionFourChains

/-- Let `N` be an odd perfect number with special prime `q` and `v_3(N) = 4` in which every prime
factor other than `q`, `r₁` and `r₂` has exponent exactly 2. Then every prime factor of `N` is
`3`, `11`, or at least `79`. This concerns only this restricted family, not odd perfect numbers
in general. Whether this statement is new was not verified against the literature. -/
theorem two_exceptions_three_pow_four_small_primes {N q r₁ r₂ : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (h34 : N.factorization 3 = 4)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2) :
    ∀ p, p.Prime → p ∣ N → p = 3 ∨ p = 11 ∨ 79 ≤ p := fun _ hp hpN =>
  TwoExceptionFourChains.small (TwoExceptionFourChains.Ctx.of h hq hodd h34 hsq) hp hpN

end OddPerfect

#print axioms OddPerfect.TwoExceptionFourChains.Ctx.ne_q
#print axioms OddPerfect.TwoExceptionFourChains.Ctx.sq
#print axioms OddPerfect.TwoExceptionFourChains.Ctx.qrow
#print axioms OddPerfect.TwoExceptionFourChains.Ctx.fifth
#print axioms OddPerfect.TwoExceptionFourChains.Ctx.mem7
#print axioms OddPerfect.TwoExceptionFourChains.Ctx.memA
#print axioms OddPerfect.TwoExceptionFourChains.not5
#print axioms OddPerfect.TwoExceptionFourChains.not7
#print axioms OddPerfect.TwoExceptionFourChains.not13
#print axioms OddPerfect.TwoExceptionFourChains.not17
#print axioms OddPerfect.TwoExceptionFourChains.not19
#print axioms OddPerfect.TwoExceptionFourChains.not23
#print axioms OddPerfect.TwoExceptionFourChains.not29
#print axioms OddPerfect.TwoExceptionFourChains.not31
#print axioms OddPerfect.TwoExceptionFourChains.not37
#print axioms OddPerfect.TwoExceptionFourChains.not41
#print axioms OddPerfect.TwoExceptionFourChains.not43
#print axioms OddPerfect.TwoExceptionFourChains.not47
#print axioms OddPerfect.TwoExceptionFourChains.not53
#print axioms OddPerfect.TwoExceptionFourChains.not59
#print axioms OddPerfect.TwoExceptionFourChains.not61
#print axioms OddPerfect.TwoExceptionFourChains.not67
#print axioms OddPerfect.TwoExceptionFourChains.not71
#print axioms OddPerfect.TwoExceptionFourChains.not73
#print axioms OddPerfect.TwoExceptionFourChains.small
#print axioms OddPerfect.TwoExceptionFourChains.Ctx.of
#print axioms OddPerfect.two_exceptions_three_pow_four_small_primes
