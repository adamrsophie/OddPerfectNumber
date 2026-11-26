import OddPerfect.EqualExponentChain

/-!
# Equal exponent chains: certificates in several pieces

The kernel check of a large certificate tree of `OddPerfect.EqualExponentChain` can need more
memory than one module may use. This module lets a tree be checked in pieces. The checker
`runC` is `run` with one change: a `mod4` leaf also accepts the current state when it is
listed in `cuts` (a cut). A cut state is refuted by a separate tree, checked by `run` or by
`runC` with further cuts; `runC_sound_cuts` and `split_sound` chain the pieces.

Restricted family result; no published source was checked; novelty not verified.
-/

namespace OddPerfect.EqChain

open OddPerfect.Pratt (powMod powMod_eq trialPrime trialPrime_sound)

/-- Boolean equality of checker states. -/
def stEq (a b : St) : Bool :=
  a.known == b.known && a.ex == b.ex && a.qs == b.qs && a.M == b.M

/-- Soundness of `stEq`. -/
theorem stEq_sound {a b : St} (h : stEq a b = true) : a = b := by
  cases a
  cases b
  simp only [stEq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  subst h1 h2 h3 h4
  rfl

/-- The checker `run` in which a `mod4` leaf also accepts a state listed in `cuts`. -/
def runC (l : ℕ) (pc : List (ℕ × ℕ × List ℕ)) (cuts : List St) : St → Node → Bool
  | st, .ord p r c =>
      st.known.contains p && isP pc r && r != 2 && neq st r && gm p r l == 0 &&
        runC l pc cuts { st with known := r :: st.known } c
  | st, .spec m r c =>
      match st.qs with
      | some Q => 1 ≤ m && st.M % m == 0 && isP pc r && r != 2 && r != Q && gm Q r m == 0 &&
          runC l pc cuts { st with known := r :: st.known } c
      | none => false
  | st, .branch r y n =>
      runC l pc cuts { st with qs := some r } y && runC l pc cuts { st with ex := r :: st.ex } n
  | st, .expo s d v c =>
      match st.qs with
      | some Q => st.known.contains s && s != 2 && s != l && s % l != 1 && 1 ≤ d &&
          powMod Q d s == 1 && allNe Q s (d - 1) && (d == 1 || powMod Q d (s ^ (v + 1)) != 1) &&
          runC l pc cuts { st with M := Nat.lcm st.M (expoFactor l s d v) } c
      | none => false
  | st, .overflow s ps m k => run l pc st (.overflow s ps m k)
  | st, .mod4 => cuts.any (fun s => stEq s st) || run l pc st .mod4

section Sound

variable {l N q : ℕ} {pc : List (ℕ × ℕ × List ℕ)}

/-- Soundness of `runC`: an accepted tree refutes every state that holds, provided every cut
state is refuted. -/
theorem runC_sound (hpc : Pratt.check pc = true) (hl : l.Prime) (hl2 : l ≠ 2)
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) {cuts : List St}
    (hcuts : ∀ s ∈ cuts, Holds l N q s → False) :
    ∀ (c : Node) (st : St), runC l pc cuts st c = true → Holds l N q st → False := by
  have hN := h.ne_zero
  have hq4 := (special_mod_four h hq hodd).1
  intro c
  induction c with
  | ord p r c ih =>
    intro st hc hs
    simp only [runC, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
      List.contains_iff_mem] at hc
    obtain ⟨⟨⟨⟨⟨hp, hr⟩, hr2⟩, hne⟩, hgm⟩, hnext⟩ := hc
    obtain ⟨hpP, hpe, -⟩ := hs.1 p hp
    have hrP := isP_sound hpc hr
    have hrq := neq_sound hs hq4 hne
    have hrN : r ∣ N := OPNStarter.force_prime h.perfect hpP hpe hrP hr2
      (dvd_sigma_of_gm hpP hl.one_lt.le hgm)
    have hre := hexp r (Nat.mem_primeFactors.mpr ⟨hrP, hrN, hN⟩) hrq
    refine ih _ hnext ⟨fun x hx => ?_, hs.2.1, hs.2.2.1, hs.2.2.2⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨hrP, hre, hrq⟩
    · exact hs.1 x hx
  | spec m r c ih =>
    intro st hc hs
    cases hqs : st.qs with
    | none => simp [runC, hqs] at hc
    | some Q =>
      simp only [runC, hqs, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
        decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨hm, hM⟩, hr⟩, hr2⟩, hrQ⟩, hgm⟩, hnext⟩ := hc
      have hQ := hs.2.2.1 Q hqs
      subst hQ
      have hrP := isP_sound hpc hr
      have hmk : m - 1 + 1 ∣ N.factorization Q + 1 := by
        rw [Nat.sub_add_cancel hm]
        exact (Nat.dvd_of_mod_eq_zero hM).trans hs.2.2.2
      have hrN : r ∣ N := OPNStarter.force_prime h.perfect hq rfl hrP hr2
        ((dvd_sigma_of_gm hq hm hgm).trans (OPNExample.sigma_prime_pow_dvd hq hmk))
      have hre := hexp r (Nat.mem_primeFactors.mpr ⟨hrP, hrN, hN⟩) hrQ
      refine ih _ hnext ⟨fun x hx => ?_, hs.2.1, fun Q' hQ' => hs.2.2.1 Q' (hqs.trans hQ'),
        hs.2.2.2⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨hrP, hre, hrQ⟩
      · exact hs.1 x hx
  | branch r y n ihy ihn =>
    intro st hc hs
    simp only [runC, Bool.and_eq_true] at hc
    by_cases hrq : r = q
    · refine ihy _ hc.1 ⟨hs.1, hs.2.1, fun Q hQ => ?_, hs.2.2.2⟩
      rw [← Option.some.inj hQ, hrq]
    · refine ihn _ hc.2 ⟨hs.1, fun x hx => ?_, hs.2.2.1, hs.2.2.2⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hrq
      · exact hs.2.1 x hx
  | expo s d v c ih =>
    intro st hc hs
    cases hqs : st.qs with
    | none => simp [runC, hqs] at hc
    | some Q =>
      simp only [runC, hqs, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq,
        List.contains_iff_mem, Bool.or_eq_true] at hc
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨hsk, hs2⟩, hsl⟩, hs1⟩, hd1⟩, hpow⟩, hall⟩, hv⟩, hnext⟩ := hc
      have hQ := hs.2.2.1 Q hqs
      subst hQ
      obtain ⟨hsP, hse, hsq⟩ := hs.1 s hsk
      have hdiv := expo_dvd h hq hodd hexp hl hl2 hsP hse hsq hs2 hsl hs1 hd1
        (by rw [← powMod_eq]; exact hpow) (fun j hj0 hj => allNe_sound hall j hj0 (by omega))
        (hv.imp id fun h' => by rwa [powMod_eq] at h')
      exact ih _ hnext ⟨hs.1, hs.2.1, fun Q' hQ' => hs.2.2.1 Q' (hqs.trans hQ'),
        Nat.lcm_dvd hs.2.2.2 hdiv⟩
  | overflow s ps m k =>
    intro st hc hs
    exact run_sound hpc hl hl2 h hq hodd hexp _ st hc hs
  | mod4 =>
    intro st hc hs
    simp only [runC, Bool.or_eq_true, List.any_eq_true] at hc
    rcases hc with ⟨s, hsm, hse⟩ | hc
    · exact hcuts s hsm (stEq_sound hse ▸ hs)
    · exact run_sound hpc hl hl2 h hq hodd hexp _ st hc hs

/-- One piece of a split tree: a tree accepted by `runC` with the cuts `cuts` refutes its
starting state once every cut state is refuted. -/
theorem runC_sound_cuts (hpc : Pratt.check pc = true) (hl : l.Prime) (hl2 : l ≠ 2)
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) {cuts : List St}
    {st : St} {c : Node} (hc : runC l pc cuts st c = true)
    (hcuts : ∀ s ∈ cuts, Holds l N q s → False) : Holds l N q st → False :=
  runC_sound hpc hl hl2 h hq hodd hexp hcuts c st hc

end Sound

/-- The conclusion of `checkAll_sound` from a refutation of the starting state of the case
`l` ordinary (given in any form, for example by pieces) and an accepted tree for `l = q`. -/
theorem split_sound {l : ℕ} {pc : List (ℕ × ℕ × List ℕ)} {specT : Node}
    (hlP : trialPrime l = true) (hl2 : l ≠ 2) (hpc : Pratt.check pc = true)
    (hsp : run l pc ⟨[], [], some l, 2⟩ specT = true) {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hord : Holds l N q ⟨[l], [l], none, 2⟩ → False) : False := by
  have hl := trialPrime_sound hlP
  have hM : 2 ∣ N.factorization q + 1 := by
    obtain ⟨j, hj⟩ := hodd
    exact ⟨j + 1, by omega⟩
  by_cases hlN : l ∣ N
  · by_cases hlq : l = q
    · refine run_sound hpc hl hl2 h hq hodd hexp specT _ hsp
        ⟨by simp, by simp, fun Q hQ => ?_, hM⟩
      rw [← Option.some.inj hQ, hlq]
    · have hle := hexp l (Nat.mem_primeFactors.mpr ⟨hl, hlN, h.ne_zero⟩) hlq
      refine hord ⟨fun p hp => ?_, fun r hr => ?_, by simp, hM⟩
      · rw [List.mem_singleton.mp hp]
        exact ⟨hl, hle, hlq⟩
      · rw [List.mem_singleton.mp hr]
        exact hlq
  · exact not_all_exponents_eq_pred_prime h hq hodd hl hl2 hlN hexp

end OddPerfect.EqChain

#print axioms OddPerfect.EqChain.stEq_sound
#print axioms OddPerfect.EqChain.runC_sound
#print axioms OddPerfect.EqChain.runC_sound_cuts
#print axioms OddPerfect.EqChain.split_sound
