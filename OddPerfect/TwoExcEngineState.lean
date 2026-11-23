import OddPerfect.TwoExcEngineCode
import OddPerfect.SpecialPrime

/-!
# The family "at most E exceptional primes, exponent 2 at 3" and the meaning of a state

This module gives the family predicate `Fam`, the meaning `Holds` of a checker state of
`OddPerfect.TwoExcEngine`, the root lemma `holds_root`, and the statement `DefSound` of the
deficient leaf theorem (proved in its own module). The engine is a tool; this module makes no
claim about odd perfect numbers beyond the root lemma.

## Choices

* The special prime `q` is an argument of `Holds`, not bound inside it. The family fixes `q`
  (a prime with odd exponent), and it stays the same through the whole certificate tree, so
  each rule lemma can speak about the same `q` without proving uniqueness of the special prime.
* The number `E` of allowed exceptions enters through the checker parameters: `Holds P N q`
  contains `Fam P.E N q`. So every rule lemma has the family at hand.
* `x` means: every prime below `x` that divides `N` is a key. `x` need not be prime.
* A contribution `(c, w)` on the key `p` means `p ^ w ∣ σ(c ^ v_c(N))` with `c` a prime factor
  of `N` that is a key; the components of one key are distinct.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace TwoExcEngine

/-- The family with parameter `E`: `N` is an odd perfect number, `q` is a prime with odd
exponent, the exponent of 3 is 2, and at most `E` prime factors `p ≠ q` of `N` have exponent
different from 2. -/
def Fam (E N q : ℕ) : Prop :=
  OddPerfect N ∧ q.Prime ∧ Odd (N.factorization q) ∧ N.factorization 3 = 2 ∧
    (N.primeFactors.filter fun p => p ≠ q ∧ N.factorization p ≠ 2).card ≤ E

/-- The meaning of a role for a prime with exponent `k`; `hq` says that the prime is `q`.
A square has exponent 2 and is not `q`. A free prime is `q` exactly when `isQ`; its exponent
satisfies `D ∣ k + 1`, `kmin ≤ k`, `3 ∤ k + 1` when `no3`, `k = kmin` when `exact`; for `q`
moreover `k + 1 ≡ 2 (mod 4)`, and for an exception `k` is even and at least 4. -/
def RoleHolds : Role → ℕ → Prop → Prop
  | .sq, k, hq => ¬ hq ∧ k = 2
  | .fr isQ D no3 kmin ex, k, hq =>
    (isQ = true ↔ hq) ∧ D ∣ k + 1 ∧ kmin ≤ k ∧ (no3 = true → ¬ 3 ∣ k + 1) ∧
      (ex = true → k = kmin) ∧ (isQ = true → (k + 1) % 4 = 2) ∧
      (isQ = false → Even k ∧ 4 ≤ k)

/-- The meaning of one key of the key list `ks`: its prime divides `N`, its role holds, and
each contribution `(c, w)` has `c` a prime factor of `N` that is a key, with
`p ^ w ∣ σ(c ^ v_c(N))`; the components are distinct. -/
def KeyHolds (N q : ℕ) (ks : List Key) (k : Key) : Prop :=
  k.p.Prime ∧ k.p ∣ N ∧ RoleHolds k.role (N.factorization k.p) (k.p = q) ∧
    (∀ e ∈ k.cs, e.1.Prime ∧ e.1 ∣ N ∧ e.1 ∈ ks.map Key.p ∧
      k.p ^ e.2 ∣ σ 1 (e.1 ^ N.factorization e.1)) ∧
    (k.cs.map Prod.fst).Nodup

/-- The meaning of a state `(ks, x)` for `N` with special prime `q` under the parameters `P`:
the family holds with `E = P.E`, every key holds, the key primes are distinct, and every prime
below `x` that divides `N` is a key. -/
def Holds (P : Params) (N q : ℕ) (ks : List Key) (x : ℕ) : Prop :=
  Fam P.E N q ∧ (∀ k ∈ ks, KeyHolds N q ks k) ∧ (ks.map Key.p).Nodup ∧
    ∀ p, p.Prime → p < x → p ∣ N → p ∈ ks.map Key.p

/-- The statement of the deficient leaf theorem for the parameters `P`: an accepted deficient
leaf refutes every state that holds. It is proved in its own module. -/
def DefSound (P : Params) : Prop :=
  ∀ (ks : List Key) (x : ℕ) (dd : DefData) (N q : ℕ),
    deficientB P ks x dd = true → Holds P N q ks x → False

/-- The root state holds for every member of the family: `3` is a square key with no
contributions, and the only primes below 5 are 2 (which does not divide the odd `N`) and 3. -/
theorem holds_root {P : Params} {N q : ℕ} (hF : Fam P.E N q) : Holds P N q rootKeys 5 := by
  obtain ⟨hN, hq, hodd, h3, -⟩ := id hF
  have hN0 : N ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hN.1)
  have h3N : 3 ∣ N := Nat.dvd_of_factorization_pos (by omega)
  have h3q : (3 : ℕ) ≠ q := by
    rintro rfl
    rw [h3] at hodd
    exact (by decide : ¬ Odd 2) hodd
  refine ⟨hF, ?_, by simp [rootKeys], ?_⟩
  · intro k hk
    simp only [rootKeys, List.mem_singleton] at hk
    subst hk
    exact ⟨Nat.prime_three, h3N, ⟨h3q, h3⟩, by simp, by simp⟩
  · intro p hp hp5 hpN
    have h2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hN.1) (even_iff_two_dvd.mpr hpN)
    have : p = 3 := by
      have := hp.two_le
      interval_cases p
      · exact absurd rfl h2
      · rfl
      · exact absurd hp (by decide)
    simp [rootKeys, this]

end TwoExcEngine

end OddPerfect

#print axioms OddPerfect.TwoExcEngine.holds_root
