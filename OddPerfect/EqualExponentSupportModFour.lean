import OddPerfect.EqualExponentSupport
import OddPerfect.IndexColumnLower
import OddPerfect.SpecialPrime

/-!
# Equal exponents: support certificates whose sources are 3 modulo 4

Setting: `N = q ^ a * m ^ 2` is an odd perfect number with special prime `q`, `q ∤ m`, `l` is
an odd prime and every prime factor of `N` other than `q` has exponent `l - 1`. This module is
a variant of the checker in `OddPerfect.EqualExponentSupport`. There a new source `s` is
accepted only when `s ≤ B`, and soundness needs `B < q`. Here a new source is accepted only
when `s % 4 = 3`. The special prime is `1` modulo `4`, so every such source differs from `q`
with no bound on `q`, and so no bound on the special exponent `a`. The root source `l` differs
from `q` because every ordinary index is a power of `l` (`LCol.ne_of_prime_pow_index`). The
piece walk `piecesOK` and its soundness theorem are reused unchanged.

Result: an accepted certificate with target `k + 2` contradicts `ω(J) ≤ k`, where
`J = eulerIndex q a m` (`supportCheckFour_sound`). Restricted result for the family where all
ordinary exponents equal `l - 1`; nothing is excluded by this module alone.

Restricted result; no published source was checked; novelty not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect.EqSupport

open OddPerfect.EqChain (gm dvd_sigma_of_gm)

/-- The sources: each new source `s` is a prime with `s % 4 = 3` dividing the row of an earlier
source `p` (the list `G` holds the sources accepted so far). -/
def srcsOKFour (l : ℕ) : List ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | G, (s, p) :: rest =>
    G.contains p && sPrime s && s % 4 == 3 && gm p s l == 0 && srcsOKFour l (s :: G) rest

/-- A whole certificate for `l` and target count `t`, with sources that are `3` modulo `4`. -/
def supportCheckFour (l t : ℕ) (srcs : List (ℕ × ℕ)) (pieces : List (ℕ × ℕ × ℕ)) : Bool :=
  srcsOKFour l [l] srcs && piecesOK l t (l :: srcs.map Prod.fst) 1 0 pieces

/-- A new source accepted by `srcsOKFour` is good: a prime factor of `N` other than the special
prime `q`. No bound on `q` is needed, since every new source is `3` modulo `4`. -/
theorem srcsOKFour_sound {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    ∀ (srcs : List (ℕ × ℕ)) (G : List ℕ), (∀ s ∈ G, Good N q s) → srcsOKFour l G srcs = true →
      ∀ s ∈ srcs.map Prod.fst, Good N q s := by
  have hq4 : q % 4 = 1 := (special_mod_four h hq hodd).1
  intro srcs
  induction srcs with
  | nil => intro G _ _ s hs; simp at hs
  | cons e rest ih =>
    obtain ⟨s, p⟩ := e
    intro G hG hc
    simp only [srcsOKFour, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨hpG, hsP⟩, hs4⟩, hgm⟩, hnext⟩ := hc
    have hsp := sPrime_sound hsP
    obtain ⟨hpp, hpN, hpq⟩ := hG p hpG
    have hpN' : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpN, h.ne_zero⟩
    have hsd : s ∣ σ 1 (p ^ (l - 1)) := dvd_sigma_of_gm hpp hl.one_lt.le hgm
    have hsN : s ∣ N := OPNStarter.force_prime h.perfect hpp (hexp p hpN' hpq) hsp
      (by rintro rfl; omega) hsd
    have hsq : s ≠ q := by omega
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

/-- Soundness of an accepted support certificate with sources that are `3` modulo `4`. In the
family where every ordinary exponent equals `l - 1`, an Euler index `J` with at most `k` prime
factors and a certificate accepted with target `k + 2` give a contradiction. There is no bound
on the special prime and none on the special exponent. Restricted result; no published source
was checked; novelty not verified. -/
theorem supportCheckFour_sound {N q a m l k : ℕ} {srcs : List (ℕ × ℕ)}
    {pieces : List (ℕ × ℕ × ℕ)} (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2)
    (hqm : ¬ q ∣ m) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hJ : (eulerIndex q a m).primeFactors.card ≤ k)
    (hc : supportCheckFour l (k + 2) srcs pieces = true) : False := by
  simp only [supportCheckFour, Bool.and_eq_true] at hc
  obtain ⟨hsrc, hpc⟩ := hc
  obtain ⟨-, hqa, hao, -⟩ := euler_frame h hq hN hqm
  have hodd : Odd (N.factorization q) := hqa ▸ hao
  have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl.one_lt.le
  have hidx' : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, N.factorization p + 1 = l ^ γ :=
    fun p hp hpq => ⟨1, by rw [hexp p hp hpq, hl1, pow_one]⟩
  have hlq : l ≠ q := LCol.ne_of_prime_pow_index h hl hodd hidx'
  by_cases hlN : l ∣ N
  · have hlg : Good N q l := ⟨hl, hlN, hlq⟩
    have hG0 : ∀ s ∈ [l], Good N q s := fun s hs => by
      rw [List.mem_singleton] at hs
      exact hs ▸ hlg
    have hS := srcsOKFour_sound h hq hodd hl hexp srcs [l] hG0 hsrc
    have hG : ∀ s ∈ l :: srcs.map Prod.fst, Good N q s := by
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact hlg
      · exact hS s hs
    exact piecesOK_sound h hq hN hqm hl hexp hJ hG pieces 1 0 hpc
      ⟨one_ne_zero, by simp, by simp⟩
  · exact not_all_exponents_eq_pred_prime h hq hodd hl hl2 hlN hexp

end OddPerfect.EqSupport

#print axioms OddPerfect.EqSupport.srcsOKFour_sound
#print axioms OddPerfect.EqSupport.supportCheckFour_sound
