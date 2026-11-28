import OddPerfect.EqualExponentSupport
import OddPerfect.IndexColumnLower
import OddPerfect.SpecialPrime

/-!
# Equal exponents: support certificates with a case split on the special prime

Setting: `N = q ^ a * m ^ 2` is an odd perfect number with special prime `q`, `q ∤ m`, `l` is
an odd prime and every prime factor of `N` other than `q` has exponent `l - 1`. Write
`J = eulerIndex q a m`. A good prime is a prime factor of `N` other than `q`; the row of a good
prime divides `q ^ a * J` (`EqSupport.row_dvd`).

A certificate (`splitCheck`) has a main case and a list of cases `(Q, sources, pieces)`.

* Main case: `q` is none of the listed `Q`. A new source is an odd prime dividing the row of an
  earlier source and either `3` modulo `4` or one of the listed `Q`; so it differs from `q`,
  since `q % 4 = 1`. The piece walk starts from the state `(1, 0)`.
* Case `q = Q`: a new source is an odd prime other than `Q` that divides the row of an earlier
  source or divides `Q + 1`. In the second event it divides `σ(q) ∣ σ(q ^ a)`, since `a` is
  odd, and so it divides `σ(N) = 2 N`. The piece walk starts from the state `(Q, 1)`, which
  holds since `Q = q` is prime.

The root source `l` divides `N` in this family and differs from `q`. Either `q` is one of the
listed `Q`, and that case refutes, or it is not, and the main case refutes. The piece walk is
the landed `EqSupport.piecesOK`. Result: an accepted certificate with target `k + 2`
contradicts `ω(J) ≤ k` (`splitCheck_sound`), with no bound on the special prime and none on
the special exponent. Restricted result for the family where all ordinary exponents equal
`l - 1`; nothing is excluded by this module alone.

Restricted result; no published source was checked; novelty not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect.EqSupport

open OddPerfect.EqCount (neqOK)
open OddPerfect.EqChain (gm)
open OddPerfect.EqCount (Ctx neqOK_sound)
open OddPerfect.EqChain (dvd_sigma_of_gm)

/-- The sources of one case. A new source `s` with earlier source `p` is an odd prime that
passes `neqOK` and divides the row of `p`, or, in a case `q = Q`, divides `Q + 1`. -/
def srcsOKCase (l : ℕ) (qs : Option ℕ) (ex : List ℕ) : List ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | G, (s, p) :: rest =>
    sPrime s && s % 2 == 1 && neqOK qs ex s &&
      ((G.contains p && gm p s l == 0) ||
        match qs with
        | some Q => (Q + 1) % s == 0
        | none => false) &&
      srcsOKCase l qs ex (s :: G) rest

/-- One case: its sources, then the piece walk from `(Q, 1)` in a case `q = Q` and from
`(1, 0)` in the main case. -/
def caseOK (l t : ℕ) (qs : Option ℕ) (ex : List ℕ) (srcs : List (ℕ × ℕ))
    (pieces : List (ℕ × ℕ × ℕ)) : Bool :=
  srcsOKCase l qs ex [l] srcs &&
    match qs with
    | some Q => piecesOK l t (l :: srcs.map Prod.fst) Q 1 pieces
    | none => piecesOK l t (l :: srcs.map Prod.fst) 1 0 pieces

/-- The whole certificate: the main case, with the listed primes as excluded values of `q`, and
one case for each listed prime. -/
def splitCheck (l t : ℕ) (msrcs : List (ℕ × ℕ)) (mpieces : List (ℕ × ℕ × ℕ))
    (cases : List (ℕ × List (ℕ × ℕ) × List (ℕ × ℕ × ℕ))) : Bool :=
  caseOK l t none (cases.map Prod.fst) msrcs mpieces &&
    cases.all fun c => caseOK l t (some c.1) [] c.2.1 c.2.2

/-- A new source accepted by `srcsOKCase` is good, under the meaning `Ctx q qs ex` of the case.
No bound on `q` is needed. -/
theorem srcsOKCase_sound {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) {qs : Option ℕ}
    {ex : List ℕ} (hc : Ctx q qs ex) :
    ∀ (srcs : List (ℕ × ℕ)) (G : List ℕ), (∀ s ∈ G, Good N q s) →
      srcsOKCase l qs ex G srcs = true → ∀ s ∈ srcs.map Prod.fst, Good N q s := by
  have hq4 : q % 4 = 1 := (special_mod_four h hq hodd).1
  intro srcs
  induction srcs with
  | nil => intro G _ _ s hs; simp at hs
  | cons e rest ih =>
    obtain ⟨s, p⟩ := e
    intro G hG hcs
    simp only [srcsOKCase, Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem,
      beq_iff_eq] at hcs
    obtain ⟨⟨⟨⟨hsP, hs2⟩, hneq⟩, hsrc⟩, hnext⟩ := hcs
    have hsp := sPrime_sound hsP
    have hsq : s ≠ q := neqOK_sound hq4 hc hneq
    have hsN : s ∣ N := by
      rcases hsrc with ⟨hpG, hgm⟩ | hM
      · obtain ⟨hpp, hpN, hpq⟩ := hG p hpG
        have hpN' : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpN, h.ne_zero⟩
        have hsd : s ∣ σ 1 (p ^ (l - 1)) := dvd_sigma_of_gm hpp hl.one_lt.le hgm
        exact OPNStarter.force_prime h.perfect hpp (hexp p hpN' hpq) hsp
          (by rintro rfl; omega) hsd
      · cases hqs : qs with
        | none => simp only [hqs] at hM; exact absurd hM (by simp)
        | some Q =>
          simp only [hqs, beq_iff_eq] at hM
          rw [hc.1 Q hqs] at hM
          have hk : 1 + 1 ∣ N.factorization q + 1 := by
            obtain ⟨j, hj⟩ := hodd
            exact ⟨j + 1, by omega⟩
          have hσ : s ∣ σ 1 (q ^ 1) := by
            rw [sigma_one_apply_prime_pow hq, Finset.sum_range_succ, Finset.sum_range_one,
              pow_zero, pow_one]
            exact Nat.dvd_of_mod_eq_zero (by rw [Nat.add_comm]; exact hM)
          exact OPNStarter.force_prime h.perfect hq rfl hsp (by rintro rfl; omega)
            (hσ.trans (OPNExample.sigma_prime_pow_dvd hq hk))
    have hgood : Good N q s := ⟨hsp, hsN, hsq⟩
    have hG' : ∀ x ∈ s :: G, Good N q x := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hgood
      · exact hG x hx
    intro x hx
    rw [List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hgood
    · exact ih (s :: G) hG' hnext x hx

/-- An accepted case refutes `ω(J) ≤ k`, under the meaning `Ctx q qs ex` of the case and given
that the root source `l` is good. -/
theorem caseOK_sound {N q a m l k : ℕ} {qs : Option ℕ} {ex : List ℕ} {srcs : List (ℕ × ℕ)}
    {pieces : List (ℕ × ℕ × ℕ)} (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2)
    (hqm : ¬ q ∣ m) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hJ : (eulerIndex q a m).primeFactors.card ≤ k) (hlg : Good N q l) (hc : Ctx q qs ex)
    (hok : caseOK l (k + 2) qs ex srcs pieces = true) : False := by
  simp only [caseOK, Bool.and_eq_true] at hok
  obtain ⟨hsrc, hpc⟩ := hok
  obtain ⟨-, hqa, hao, -⟩ := euler_frame h hq hN hqm
  have hodd : Odd (N.factorization q) := hqa ▸ hao
  have hG0 : ∀ s ∈ [l], Good N q s := fun s hs => by
    rw [List.mem_singleton] at hs
    exact hs ▸ hlg
  have hS := srcsOKCase_sound h hq hodd hl hexp hc srcs [l] hG0 hsrc
  have hG : ∀ s ∈ l :: srcs.map Prod.fst, Good N q s := by
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hlg
    · exact hS s hs
  cases hqs : qs with
  | none =>
    simp only [hqs] at hpc
    exact piecesOK_sound h hq hN hqm hl hexp hJ hG pieces 1 0 hpc
      ⟨one_ne_zero, by simp, by simp⟩
  | some Q =>
    simp only [hqs] at hpc
    rw [hc.1 Q hqs] at hpc
    refine piecesOK_sound h hq hN hqm hl hexp hJ hG pieces q 1 hpc
      ⟨hq.ne_zero, fun r hr => ?_, by rw [hq.primeFactors]; simp⟩
    rw [hq.primeFactors, Finset.mem_singleton] at hr
    exact Finset.mem_insert.mpr (Or.inl hr)

/-- Soundness of an accepted split certificate. In the family where every ordinary exponent
equals `l - 1`, an Euler index `J` with at most `k` prime factors and a certificate accepted by
`splitCheck` with target `k + 2` give a contradiction. There is no bound on the special prime
and none on the special exponent. Restricted result; no published source was checked; novelty
not verified. -/
theorem splitCheck_sound {N q a m l k : ℕ} {msrcs : List (ℕ × ℕ)}
    {mpieces : List (ℕ × ℕ × ℕ)} {cases : List (ℕ × List (ℕ × ℕ) × List (ℕ × ℕ × ℕ))}
    (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m)
    (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hJ : (eulerIndex q a m).primeFactors.card ≤ k)
    (hc : splitCheck l (k + 2) msrcs mpieces cases = true) : False := by
  simp only [splitCheck, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨hmain, hall⟩ := hc
  obtain ⟨-, hqa, hao, -⟩ := euler_frame h hq hN hqm
  have hodd : Odd (N.factorization q) := hqa ▸ hao
  have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl.one_lt.le
  have hidx' : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, N.factorization p + 1 = l ^ γ :=
    fun p hp hpq => ⟨1, by rw [hexp p hp hpq, hl1, pow_one]⟩
  have hlq : l ≠ q := LCol.ne_of_prime_pow_index h hl hodd hidx'
  by_cases hlN : l ∣ N
  · have hlg : Good N q l := ⟨hl, hlN, hlq⟩
    by_cases hmem : q ∈ cases.map Prod.fst
    · obtain ⟨c, hcm, hcq⟩ := List.mem_map.mp hmem
      have hctx : Ctx q (some c.1) [] :=
        ⟨fun Q hQ => by rw [← hcq]; exact (Option.some.inj hQ).symm, by simp⟩
      exact caseOK_sound h hq hN hqm hl hexp hJ hlg hctx (hall c hcm)
    · have hctx : Ctx q none (cases.map Prod.fst) :=
        ⟨fun Q hQ => by simp at hQ, fun r hr hrq => hmem (by rw [← hrq]; exact hr)⟩
      exact caseOK_sound h hq hN hqm hl hexp hJ hlg hctx hmain
  · exact not_all_exponents_eq_pred_prime h hq hodd hl hl2 hlN hexp

end OddPerfect.EqSupport

#print axioms OddPerfect.EqSupport.srcsOKCase_sound
#print axioms OddPerfect.EqSupport.caseOK_sound
#print axioms OddPerfect.EqSupport.splitCheck_sound
