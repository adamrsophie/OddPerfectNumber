import OddPerfect.Euler
import OddPerfect.Seed.Example
import Mathlib

/-!
# Verified factor chain certificates

A small checker for factor chain certificates about an unknown odd perfect number `N`.
An untrusted program produces a `Cert`; `check` is a computable Boolean function that the
kernel evaluates with `decide +kernel`; `check_sound` says that a certificate accepted for a
state rules out every odd perfect number satisfying all facts of that state.

Scope: an accepted certificate excludes exactly the odd perfect numbers matching the supplied
root facts, and nothing more. No family of root states is proved exhaustive over all odd
perfect numbers in this file; any claim that a family of accepted certificates covers every
odd perfect number has to come from a separate theorem proving that coverage.

Step rules: `force` and `split`. Closing rules: `abundant`, `notDvd`, `exactPow`,
`parityTwo`, `paritySpecial`, `overflow`.
-/

namespace OddPerfect.Cert

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-! ## Facts and states -/

/-- A statement about the unknown number `N`. -/
inductive Fact where
  /-- `N.factorization p = e`. -/
  | exact (p e : ℕ)
  /-- `p ^ e ∣ N`. -/
  | powDvd (p e : ℕ)
  /-- `¬ p ∣ N`. -/
  | notDvd (p : ℕ)
  deriving DecidableEq

/-- The meaning of a fact. -/
def Fact.Holds : Fact → ℕ → Prop
  | .exact p e, N => N.factorization p = e
  | .powDvd p e, N => p ^ e ∣ N
  | .notDvd p, N => ¬ p ∣ N

/-- A state holds for `N` when each of its facts does. -/
def State.Holds (s : List Fact) (N : ℕ) : Prop := ∀ f ∈ s, f.Holds N

/-! ## Computable helpers -/

/-- Trial division primality test; it reduces in the kernel.
ponytail: linear trial division, switch to a square root bound if certificates need large primes. -/
def isPrimeB (n : ℕ) : Bool :=
  2 ≤ n && (List.range n).all fun d => d < 2 || n % d != 0

/-- `geom p e = 1 + p + ⋯ + p ^ e`, the divisor sum of `p ^ e` for prime `p`. -/
def geom (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | e + 1 => geom p e + p ^ (e + 1)

/-- The state records `p ^ e ∣ N`, directly or through an exact exponent. -/
def hasPow (s : List Fact) (p e : ℕ) : Bool :=
  s.contains (.powDvd p e) || s.contains (.exact p e)

/-- Conditions for the abundant divisor `∏ p ^ e` over a list of pairs `(p, e)`:
each `p ^ e ∣ N` is recorded, each `p` is prime, and the primes are distinct. -/
def abundantOK (s : List Fact) : List (ℕ × ℕ) → Bool
  | [] => true
  | (p, e) :: l => hasPow s p e && isPrimeB p && l.all (fun x => x.1 != p) && abundantOK s l

/-- `∏ p ^ e` over a list of pairs. -/
def dprod : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (p, e) :: l => p ^ e * dprod l

/-- `∏ geom p e` over a list of pairs. -/
def sprod : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (p, e) :: l => geom p e * sprod l

/-- Conditions for the overflow rule at the prime `q`, over triples `(p, f, k)`:
`N.factorization p = f` is recorded with `f ≥ 1` and `p` prime, `q ^ k` divides
`geom p f`, and the primes `p` are distinct. -/
def overflowOK (s : List Fact) (q : ℕ) : List (ℕ × ℕ × ℕ) → Bool
  | [] => true
  | (p, f, k) :: l => s.contains (.exact p f) && isPrimeB p && 1 ≤ f &&
      geom p f % q ^ k == 0 && l.all (fun x => x.1 != p) && overflowOK s q l

/-- The sum of the claimed valuations `k`. -/
def ksum : List (ℕ × ℕ × ℕ) → ℕ
  | [] => 0
  | (_, _, k) :: l => k + ksum l

/-! ## Certificates and the checker -/

set_option linter.dupNamespace false in
/-- A certificate tree: closing rules at the leaves, step rules at the nodes. -/
inductive Cert where
  /-- From `exact p e` with `a + 1 ∣ e + 1` and an odd prime `q ∣ geom p a`,
  continue with `q ∣ N` added. With `a = e` this is the plain forcing step. -/
  | force (p e a q : ℕ) (next : Cert)
  /-- From `p ^ e ∣ N` with `p` prime, branch on `exact p e` versus `p ^ (e + 1) ∣ N`. -/
  | split (p e : ℕ) (atExact atMore : Cert)
  /-- The recorded divisor `∏ p ^ e` is abundant. -/
  | abundant (ps : List (ℕ × ℕ))
  /-- `p ^ e ∣ N` with `e ≥ 1` contradicts `¬ p ∣ N`. -/
  | notDvd (p e : ℕ)
  /-- `exact p e` contradicts `p ^ e' ∣ N` for prime `p` and `e < e'`. -/
  | exactPow (p e e' : ℕ)
  /-- Two distinct primes with odd exact exponents contradict Euler. -/
  | parityTwo (p e q f : ℕ)
  /-- An odd exact exponent `e` at `p` with `p % 4 ≠ 1` or `e % 4 ≠ 1` contradicts Euler. -/
  | paritySpecial (p e : ℕ)
  /-- The prime `q ≠ 2` has exact exponent `e`, but the listed components contribute
  more than `e` factors of `q` to `σ N`. -/
  | overflow (q e : ℕ) (ps : List (ℕ × ℕ × ℕ))

/-- The certificate checker. -/
def check : List Fact → Cert → Bool
  | s, .force p e a q c =>
      s.contains (.exact p e) && isPrimeB p && isPrimeB q && q != 2 &&
        (e + 1) % (a + 1) == 0 && geom p a % q == 0 && check (.powDvd q 1 :: s) c
  | s, .split p e c₁ c₂ =>
      hasPow s p e && isPrimeB p && check (.exact p e :: s) c₁ && check (.powDvd p (e + 1) :: s) c₂
  | s, .abundant ps => abundantOK s ps && 2 * dprod ps < sprod ps
  | s, .notDvd p e => hasPow s p e && 1 ≤ e && s.contains (.notDvd p)
  | s, .exactPow p e e' => s.contains (.exact p e) && hasPow s p e' && isPrimeB p && e < e'
  | s, .parityTwo p e q f =>
      s.contains (.exact p e) && s.contains (.exact q f) && isPrimeB p && isPrimeB q &&
        p != q && e % 2 == 1 && f % 2 == 1
  | s, .paritySpecial p e =>
      s.contains (.exact p e) && isPrimeB p && e % 2 == 1 && (p % 4 != 1 || e % 4 != 1)
  | s, .overflow q e ps =>
      s.contains (.exact q e) && isPrimeB q && q != 2 && overflowOK s q ps && e < ksum ps

/-! ## Soundness of the helpers -/

/-- The trial division test is sound. -/
theorem isPrimeB_sound {n : ℕ} (h : isPrimeB n = true) : n.Prime := by
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  refine Nat.prime_def_lt.mpr ⟨h.1, fun m hm hd => ?_⟩
  rcases h.2 m hm with h1 | h1
  · interval_cases m
    · rw [zero_dvd_iff] at hd; omega
    · rfl
  · exact absurd (Nat.mod_eq_zero_of_dvd hd) h1

/-- `geom` is the geometric sum. -/
theorem geom_eq (p e : ℕ) : geom p e = ∑ i ∈ Finset.range (e + 1), p ^ i := by
  induction e with
  | zero => simp [geom]
  | succ e ih => rw [geom, ih, Finset.sum_range_succ _ (e + 1)]

/-- For prime `p`, `σ (p ^ e) = geom p e`. -/
theorem sigma_eq_geom {p : ℕ} (hp : p.Prime) (e : ℕ) : σ 1 (p ^ e) = geom p e := by
  rw [sigma_one_apply_prime_pow hp, geom_eq]

/-- A fact found in a valid state holds. -/
theorem holds_of_contains {s : List Fact} {N : ℕ} (hs : State.Holds s N) {f : Fact}
    (h : s.contains f = true) : f.Holds N :=
  hs f (List.contains_iff_mem.mp h)

/-- `hasPow` certifies `p ^ e ∣ N`. -/
theorem hasPow_sound {s : List Fact} {N p e : ℕ} (hs : State.Holds s N)
    (h : hasPow s p e = true) : p ^ e ∣ N := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact holds_of_contains hs h
  · have he : N.factorization p = e := holds_of_contains hs h
    exact he ▸ Nat.ordProj_dvd N p

/-- Unpacks the distinctness test used by the checker. -/
theorem not_mem_of_all {α : Type*} {l : List (ℕ × α)} {p : ℕ}
    (h : (l.all fun x => x.1 != p) = true) : ∀ x ∈ l, x.1 ≠ p := by
  intro x hx
  simpa using List.all_eq_true.mp h x hx

/-- A prime outside the list is coprime to its recorded divisor. -/
theorem coprime_dprod {s : List Fact} {p : ℕ} (hp : p.Prime) :
    ∀ {l : List (ℕ × ℕ)}, abundantOK s l = true → (∀ x ∈ l, x.1 ≠ p) →
      Nat.Coprime p (dprod l)
  | [], _, _ => by simp [dprod]
  | (q, f) :: l, h, hne => by
    simp only [abundantOK, Bool.and_eq_true] at h
    have hq := isPrimeB_sound h.1.1.2
    have hqp : q ≠ p := hne (q, f) (by simp)
    rw [dprod]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right f ((Nat.coprime_primes hp hq).mpr hqp.symm))
      (coprime_dprod hp h.2 fun x hx => hne x (by simp [hx]))

/-- The recorded divisor divides `N`, and its divisor sum is `sprod`. -/
theorem dprod_sound {s : List Fact} {N : ℕ} (hs : State.Holds s N) :
    ∀ {l : List (ℕ × ℕ)}, abundantOK s l = true → dprod l ∣ N ∧ σ 1 (dprod l) = sprod l
  | [], _ => by simp [dprod, sprod]
  | (p, e) :: l, h => by
    simp only [abundantOK, Bool.and_eq_true] at h
    have hp := isPrimeB_sound h.1.1.2
    have hcop : Nat.Coprime (p ^ e) (dprod l) :=
      (coprime_dprod hp h.2 (not_mem_of_all h.1.2)).pow_left _
    obtain ⟨hd, hσ⟩ := dprod_sound hs h.2
    rw [dprod, sprod, isMultiplicative_sigma.map_mul_of_coprime hcop, hσ, sigma_eq_geom hp]
    exact ⟨hcop.mul_dvd_of_dvd_of_dvd (hasPow_sound hs h.1.1.1) hd, rfl⟩

/-- The `q`-adic contribution of the component of `N` at `p`. -/
abbrev incoming (N q p : ℕ) : ℕ := (σ 1 (p ^ N.factorization p)).factorization q

/-- The listed primes divide `N`, and the claimed valuations are bounded by
the true `q`-adic contributions of their components. -/
theorem overflow_sum {s : List Fact} {N q : ℕ} (hs : State.Holds s N) (hN : N ≠ 0)
    (hq : q.Prime) :
    ∀ {l : List (ℕ × ℕ × ℕ)}, overflowOK s q l = true →
      (l.map (·.1)).toFinset ⊆ N.primeFactors ∧
        ksum l ≤ ∑ p ∈ (l.map (·.1)).toFinset, incoming N q p
  | [], _ => by simp [ksum]
  | (p, f, k) :: l, h => by
    simp only [overflowOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨hex, hpB⟩, hf⟩, hmod⟩, hall⟩, hrest⟩ := h
    have hp := isPrimeB_sound hpB
    have he : N.factorization p = f := holds_of_contains hs hex
    obtain ⟨hsub, hle⟩ := overflow_sum hs hN hq hrest
    have hnot : p ∉ (l.map (·.1)).toFinset := by
      simp only [List.mem_toFinset, List.mem_map]
      rintro ⟨x, hx, rfl⟩
      exact not_mem_of_all hall x hx rfl
    have hpN : p ∈ N.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, Nat.dvd_of_factorization_pos (by omega), hN⟩
    have hk : k ≤ incoming N q p := by
      have hdvd : q ^ k ∣ σ 1 (p ^ f) := by
        rw [sigma_eq_geom hp]; exact Nat.dvd_of_mod_eq_zero hmod
      unfold incoming
      rw [he]
      exact (hq.pow_dvd_iff_le_factorization (sigma_pos 1 _ (pow_pos hp.pos _).ne').ne').mp hdvd
    simp only [List.map_cons, List.toFinset_cons, Finset.sum_insert hnot, ksum]
    exact ⟨Finset.insert_subset hpN hsub, by omega⟩

/-! ## Soundness -/

/-- Soundness: a certificate accepted for the state `s` excludes every odd perfect number
satisfying all facts of `s`. That is its whole scope: it says nothing about odd perfect
numbers that fail some fact of `s`. This file proves no family of root states exhaustive
over all odd perfect numbers; coverage has to come from a separate theorem. -/
theorem check_sound {s : List Fact} {c : Cert} (hc : check s c = true) :
    ∀ N : ℕ, OddPerfect N → State.Holds s N → False := by
  intro N h hs
  have hN := h.ne_zero
  induction c generalizing s with
  | force p e a q c ih =>
    simp only [check, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨hex, hpB⟩, hqB⟩, hq2⟩, hlen⟩, hmod⟩, hnext⟩ := hc
    have hp := isPrimeB_sound hpB
    have hqN : q ∣ N := by
      refine OPNStarter.force_prime h.perfect hp (holds_of_contains hs hex) (isPrimeB_sound hqB)
        hq2 ?_
      refine Dvd.dvd.trans ?_ (OPNExample.sigma_prime_pow_dvd hp (Nat.dvd_of_mod_eq_zero hlen))
      rw [sigma_eq_geom hp]
      exact Nat.dvd_of_mod_eq_zero hmod
    refine ih hnext ?_
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · simpa [Fact.Holds] using hqN
    · exact hs f hf
  | split p e c₁ c₂ ih₁ ih₂ =>
    simp only [check, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨hpow, hpB⟩, h₁⟩, h₂⟩ := hc
    have hp := isPrimeB_sound hpB
    have hle := (hp.pow_dvd_iff_le_factorization hN).mp (hasPow_sound hs hpow)
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · refine ih₁ h₁ ?_
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact heq.symm
      · exact hs f hf
    · refine ih₂ h₂ ?_
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact (hp.pow_dvd_iff_le_factorization hN).mpr hlt
      · exact hs f hf
  | abundant ps =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hd, hσ⟩ := dprod_sound hs hc.1
    have hlt : 2 * dprod ps < σ 1 (dprod ps) := hσ ▸ hc.2
    rw [sigma_one_apply] at hlt
    have hab := (Nat.abundant_iff_sum_divisors.mpr hlt).of_dvd hd hN
    exact ((Nat.perfect_iff_not_abundant_and_not_deficient h.pos.ne).mp h.perfect).1 hab
  | notDvd p e =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hnd : ¬ p ∣ N := holds_of_contains hs hc.2
    exact hnd ((dvd_pow_self p (by omega)).trans (hasPow_sound hs hc.1.1))
  | exactPow p e e' =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hex, hpow⟩, hpB⟩, hlt⟩ := hc
    have he : N.factorization p = e := holds_of_contains hs hex
    have := ((isPrimeB_sound hpB).pow_dvd_iff_le_factorization hN).mp (hasPow_sound hs hpow)
    omega
  | parityTwo p e q f =>
    simp only [check, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨hep, heq⟩, hpB⟩, hqB⟩, hpq⟩, he⟩, hf⟩ := hc
    have hpe : N.factorization p = e := holds_of_contains hs hep
    have hqf : N.factorization q = f := holds_of_contains hs heq
    obtain ⟨r, -, -, -, -, hev⟩ := exists_special_prime h
    by_cases hpr : p = r
    · have := Nat.even_iff.mp (hev q (isPrimeB_sound hqB) (hpr ▸ Ne.symm hpq))
      omega
    · have := Nat.even_iff.mp (hev p (isPrimeB_sound hpB) hpr)
      omega
  | paritySpecial p e =>
    simp only [check, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Bool.or_eq_true] at hc
    obtain ⟨⟨⟨hex, hpB⟩, he⟩, h4⟩ := hc
    have hpe : N.factorization p = e := holds_of_contains hs hex
    obtain ⟨r, -, -, hr4, hre, hev⟩ := exists_special_prime h
    by_cases hpr : p = r
    · subst hpr
      omega
    · have := Nat.even_iff.mp (hev p (isPrimeB_sound hpB) hpr)
      omega
  | overflow q e ps =>
    simp only [check, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨hex, hqB⟩, hq2⟩, hok⟩, hlt⟩ := hc
    have hq := isPrimeB_sound hqB
    have hqe : N.factorization q = e := holds_of_contains hs hex
    obtain ⟨hsub, hle⟩ := overflow_sum hs hN hq hok
    have hbal : Nat.factorization 2 q + N.factorization q =
        ∑ p ∈ N.primeFactors, incoming N q p := OPNStarter.valuation_balance h.perfect q
    have h2 : Nat.factorization 2 q = 0 := by
      rw [Nat.prime_two.factorization, Finsupp.single_apply, if_neg (Ne.symm hq2)]
    have := Finset.sum_le_sum_of_subset (f := incoming N q) hsub
    omega

/-! ## Demonstrations -/

/-- Replay of `OPNStarter.exclude_four_exact_squares` through the checker: the components
`7 ^ 2`, `13 ^ 2`, `19 ^ 2` each contribute a factor 3, overflowing the exponent 2 at 3. -/
theorem exclude_four_exact_squares {N : ℕ} (h : OddPerfect N)
    (h3 : N.factorization 3 = 2) (h7 : N.factorization 7 = 2)
    (h13 : N.factorization 13 = 2) (h19 : N.factorization 19 = 2) : False :=
  check_sound (s := [.exact 3 2, .exact 7 2, .exact 13 2, .exact 19 2])
    (c := .overflow 3 2 [(7, 2, 1), (13, 2, 1), (19, 2, 1)]) (by decide +kernel) N h
    (by simp [State.Holds, Fact.Holds, h3, h7, h13, h19])

/-- No odd perfect number has exponent exactly 2 at both 3 and 5. The certificate forces
`13 ∣ N` and `31 ∣ N`, then splits the exponent of 13: exponent 1 forces `7 ∣ N` and
`3 ^ 2 * 5 ^ 2 * 13 * 7` is abundant; otherwise `3 ^ 2 * 5 ^ 2 * 13 ^ 2 * 31` is abundant. -/
theorem exclude_three_sq_five_sq {N : ℕ} (h : OddPerfect N)
    (h3 : N.factorization 3 = 2) (h5 : N.factorization 5 = 2) : False :=
  check_sound (s := [.exact 3 2, .exact 5 2])
    (c := .force 3 2 2 13 <| .force 5 2 2 31 <|
      .split 13 1
        (.force 13 1 1 7 <| .abundant [(3, 2), (5, 2), (13, 1), (7, 1)])
        (.abundant [(3, 2), (5, 2), (13, 2), (31, 1)]))
    (by decide +kernel) N h (by simp [State.Holds, Fact.Holds, h3, h5])

end OddPerfect.Cert

#print axioms OddPerfect.Cert.check_sound
#print axioms OddPerfect.Cert.exclude_four_exact_squares
#print axioms OddPerfect.Cert.exclude_three_sq_five_sq
#print axioms OddPerfect.Cert.isPrimeB_sound
#print axioms OddPerfect.Cert.geom_eq
#print axioms OddPerfect.Cert.sigma_eq_geom
#print axioms OddPerfect.Cert.holds_of_contains
#print axioms OddPerfect.Cert.hasPow_sound
#print axioms OddPerfect.Cert.not_mem_of_all
#print axioms OddPerfect.Cert.coprime_dprod
#print axioms OddPerfect.Cert.dprod_sound
#print axioms OddPerfect.Cert.overflow_sum
