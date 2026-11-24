import OddPerfect.SpecialFiveCode
import OddPerfect.DefectTreeCheck

/-!
# A certificate checker for the special component `5 ^ 1` with bounded components: soundness

This module proves the soundness theorem `check_sound` for the checker of
`OddPerfect.SpecialFiveCode`: if `check B pc tab c = true`, then every odd perfect number `N`
with `v_5(N) = 1` has a prime factor `p` with `B < p ^ v_p(N)`.

The rule lemmas come from `OddPerfect.DefectRules` (forced primes, capacity, abundancy) and the
table lemmas from `OddPerfect.DefectTreeCheck`. The case split of a branch is complete: the
branch prime is a prime factor of `N` other than `5`, so its exponent is even and at least 2,
and its component is at most `B`, so the chain, which runs until the power exceeds `B`,
lists its exponent.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace SpecialFive

open DefectTree (gs kOf look tabOK Tab PCert gs_eq sigma_eq_gs kOf_le look_sound)

/-- The hypotheses carried by the whole tree: `N` is an odd perfect number with `v_5(N) = 1`
all of whose components are at most `B`. -/
structure Ctx (B N : ℕ) : Prop where
  h : OddPerfect N
  h5 : N.factorization 5 = 1
  hB : ∀ p ∈ N.primeFactors, p ^ N.factorization p ≤ B

/-- The meaning of a state: every entry is a prime factor of `N` with the stated exponent, and
the entry primes are distinct. -/
def Holds (N : ℕ) (st : List (ℕ × ℕ)) : Prop :=
  (∀ x ∈ st, x.1 ∈ N.primeFactors ∧ N.factorization x.1 = x.2) ∧ (st.map Prod.fst).Nodup

section Sound

variable {B N : ℕ} {pc : PCert} {tab : Tab}

private theorem find_spec {α : Type} {l : List α} {p : α → Bool} {y : α}
    (h : l.find? p = some y) : y ∈ l ∧ p y = true :=
  ⟨List.mem_of_find?_eq_some h, List.find?_some h⟩

private theorem two_ne (C : Ctx B N) {p : ℕ} (hp : p ∈ N.primeFactors) : p ≠ 2 := by
  rintro rfl
  have h1 := Nat.dvd_of_mem_primeFactors hp
  have h2 := Nat.odd_iff.mp C.h.1
  omega

private theorem five_mem (C : Ctx B N) : 5 ∈ N.primeFactors := by
  have : N.factorization 5 ≠ 0 := by rw [C.h5]; decide
  exact Nat.mem_primeFactors.mpr ⟨by norm_num, Nat.dvd_of_factorization_pos this, C.h.ne_zero⟩

private theorem facts_spec (C : Ctx B N) (hpc : Pratt.check pc = true)
    (ht : tabOK pc tab = true) {st : List (ℕ × ℕ)} (hH : Holds N st) {x : ℕ × ℕ}
    (hx : x ∈ st) {y : ℕ × ℕ} (hy : y ∈ look tab x.1 x.2) :
    y.1 ∈ N.primeFactors ∧ y.2 ≤ sigmaWeight N x.1 y.1 := by
  obtain ⟨hxN, he⟩ := hH.1 x hx
  have hxp := Nat.prime_of_mem_primeFactors hxN
  obtain ⟨hp, h2, hk, hd⟩ := (look_sound hpc ht x.1 x.2).2 y hy
  rw [← sigma_eq_gs hxp, ← he] at hd
  exact ⟨mem_primeFactors_of_dvd_sigma_component C.h hxN hp h2
    ((dvd_pow_self _ (by omega)).trans hd), le_sigmaWeight_of_pow_dvd hxp hp hd⟩

private theorem forced_mem (C : Ctx B N) (hpc : Pratt.check pc = true)
    (ht : tabOK pc tab = true) {st : List (ℕ × ℕ)} (hH : Holds N st) {r : ℕ}
    (h : forcedB tab st r = true) : r ∈ N.primeFactors := by
  unfold forcedB at h
  obtain ⟨y, hy, hyr⟩ := List.any_eq_true.mp h
  rw [beq_iff_eq] at hyr
  obtain ⟨x, hx, hyx⟩ := List.mem_flatMap.mp hy
  exact hyr ▸ (facts_spec C hpc ht hH hx hyx).1

private theorem fresh_spec {st : List (ℕ × ℕ)} {r : ℕ} (h : freshB st r = true) :
    r ∉ st.map Prod.fst := by
  unfold freshB at h
  intro hm
  obtain ⟨x, hx, hxr⟩ := List.mem_map.mp hm
  have ha : (st.any fun x => x.1 == r) = true :=
    List.any_eq_true.mpr ⟨x, hx, beq_iff_eq.mpr hxr⟩
  rw [ha] at h
  exact absurd h (by decide)

private theorem cap_sound (C : Ctx B N) (hpc : Pratt.check pc = true)
    (ht : tabOK pc tab = true) {st : List (ℕ × ℕ)} (hH : Holds N st) {r : ℕ}
    (hl : capB tab st r = true) : False := by
  unfold capB at hl
  split at hl
  · rename_i x hx
    obtain ⟨hxm, hxp⟩ := find_spec hx
    rw [beq_iff_eq] at hxp
    subst hxp
    rw [decide_eq_true_eq] at hl
    obtain ⟨hxN, hv⟩ := hH.1 x hxm
    have hrP := Nat.prime_of_mem_primeFactors hxN
    have hr2 := two_ne C hxN
    have hB : (st.map fun y => kOf (look tab y.1 y.2) x.1).sum ≤
        (st.map fun y => sigmaWeight N y.1 x.1).sum :=
      List.sum_le_sum fun y hy => kOf_le (fun z hz => (facts_spec C hpc ht hH hy hz).2) _
    have e : (st.map fun y => sigmaWeight N y.1 x.1) =
        (st.map Prod.fst).map (fun p => sigmaWeight N p x.1) := by
      rw [List.map_map]; rfl
    have hsub : (st.map Prod.fst).toFinset ⊆ N.primeFactors := by
      intro p hp
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
      exact (hH.1 y hy).1
    have hC : (st.map fun y => sigmaWeight N y.1 x.1).sum ≤ N.factorization x.1 := by
      rw [e, ← List.sum_toFinset _ hH.2]
      exact sum_sigmaWeight_le_factorization C.h hrP hr2 hsub
    omega
  · simp at hl

private theorem abund_sound (C : Ctx B N) {st : List (ℕ × ℕ)} (hH : Holds N st)
    (hl : abundB st = true) : False := by
  unfold abundB at hl
  rw [decide_eq_true_eq] at hl
  have hpr : ∀ p ∈ (st.map Prod.fst).toFinset, p.Prime := by
    intro p hp
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    exact Nat.prime_of_mem_primeFactors (hH.1 y hy).1
  have hle := prod_geom_sum_le_two_mul_prod C.h hpr (f := fun p => N.factorization p)
    (fun _ _ => le_rfl)
  simp only [← gs_eq] at hle
  rw [List.prod_toFinset _ hH.2, List.prod_toFinset _ hH.2, List.map_map,
    List.map_map] at hle
  have e1 : st.map ((fun p => p ^ N.factorization p) ∘ Prod.fst) =
      st.map fun x => x.1 ^ x.2 :=
    List.map_congr_left fun x hx => by simp [(hH.1 x hx).2]
  have e2 : st.map ((fun p => gs p (N.factorization p)) ∘ Prod.fst) =
      st.map fun x => gs x.1 x.2 :=
    List.map_congr_left fun x hx => by simp [(hH.1 x hx).2]
  rw [e1, e2] at hle
  omega

/-- The meaning of a position: a state that holds, and in a chain for the prime `r` at the
exponent `e` also that `r` is a prime factor of `N` that is not an entry, with even exponent at
least the even number `e`. -/
def Inv (N : ℕ) : Mode → List (ℕ × ℕ) → Prop
  | .node, st => Holds N st
  | .chain r e, st => Holds N st ∧ r ∈ N.primeFactors ∧ r ∉ st.map Prod.fst ∧
      e ≤ N.factorization r ∧ e % 2 = 0 ∧ N.factorization r % 2 = 0

/-- Soundness of the tree check. -/
theorem go_sound (C : Ctx B N) (hpc : Pratt.check pc = true) (ht : tabOK pc tab = true) :
    ∀ (c : Cert) (st : List (ℕ × ℕ)) (m : Mode), go B tab c st m = true → Inv N m st →
      False
  | .cap r, st, m, hg, hI => by
    cases m with
    | node => exact cap_sound C hpc ht hI hg
    | chain _ _ => simp [go] at hg
  | .abund, st, m, hg, hI => by
    cases m with
    | node => exact abund_sound C hI hg
    | chain _ _ => simp [go] at hg
  | .br r ch, st, m, hg, hI => by
    cases m with
    | node =>
      simp only [go, Bool.and_eq_true, bne_iff_ne, ne_eq] at hg
      obtain ⟨⟨⟨hf, hfr⟩, h5⟩, hc⟩ := hg
      have hrN := forced_mem C hpc ht hI hf
      obtain ⟨j, hj, hpos⟩ :=
        even_pos_factorization_of_ne C.h (by norm_num) (by rw [C.h5]; decide) hrN h5
      exact go_sound C hpc ht ch st (.chain r 2) hc
        ⟨hI, hrN, fresh_spec hfr, by omega, rfl, by omega⟩
    | chain _ _ => simp [go] at hg
  | .ord kid rest, st, m, hg, hI => by
    cases m with
    | chain r e =>
      simp only [go, Bool.and_eq_true] at hg
      obtain ⟨hH, hrN, hrf, hle, he2, hv2⟩ := hI
      by_cases hv : N.factorization r = e
      · refine go_sound C hpc ht kid _ .node hg.1 ⟨fun y hy => ?_, ?_⟩
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact ⟨hrN, hv⟩
          · exact hH.1 y hy
        · rw [List.map_cons]
          exact List.nodup_cons.mpr ⟨hrf, hH.2⟩
      · exact go_sound C hpc ht rest st (.chain r (e + 2)) hg.2
          ⟨hH, hrN, hrf, by omega, by omega, hv2⟩
    | node => simp [go] at hg
  | .stop, st, m, hg, hI => by
    cases m with
    | chain r e =>
      simp only [go, decide_eq_true_eq] at hg
      obtain ⟨-, hrN, -, hle, -, -⟩ := hI
      have hr1 : 1 ≤ r := (Nat.prime_of_mem_primeFactors hrN).one_lt.le
      have := Nat.pow_le_pow_right hr1 hle
      have := C.hB r hrN
      omega
    | node => simp [go] at hg

end Sound

/-- Soundness of the checker: if `check B pc tab c = true`, then every odd perfect number `N`
with `v_5(N) = 1` has a prime factor `p` whose component `p ^ v_p(N)` exceeds `B`. -/
theorem check_sound {B : ℕ} {pc : PCert} {tab : Tab} {c : Cert}
    (hc : check B pc tab c = true) {N : ℕ} (h : OddPerfect N) (h5 : N.factorization 5 = 1) :
    ∃ p ∈ N.primeFactors, B < p ^ N.factorization p := by
  by_contra hne
  push Not at hne
  simp only [check, Bool.and_eq_true] at hc
  obtain ⟨⟨hpc, ht⟩, hg⟩ := hc
  have C : Ctx B N := ⟨h, h5, hne⟩
  refine go_sound C hpc ht c _ .node hg ⟨fun x hx => ?_, by simp⟩
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨five_mem C, h5⟩

end SpecialFive

end OddPerfect

#print axioms OddPerfect.SpecialFive.go_sound
#print axioms OddPerfect.SpecialFive.check_sound
