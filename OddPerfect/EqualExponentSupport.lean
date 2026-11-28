import OddPerfect.EqualExponentCount
import OddPerfect.EulerPart

/-!
# Equal exponents: support certificates for the Euler index

Setting: `N = q ^ a * m ^ 2` is an odd perfect number with special prime `q`, `q ∤ m`, `l` is
an odd prime and every prime factor of `N` other than `q` has exponent `l - 1`. Write
`J = eulerIndex q a m` and `row(s) = ∑ i < l, s ^ i = σ(s ^ (l - 1))`.

Call a prime `s` good when `s ∣ N` and `s ≠ q`. Suppose `B < q`.

* `l` is good when `l ≤ B` (it divides `N` in this family).
* If `p` is good, `s ≤ B` is an odd prime and `s ∣ row(p)`, then `s` is good: `s ∣ σ(N) = 2 N`
  and `s` is odd.
* For good `s`, `row(s)` divides `σ(m ^ 2) = q ^ a J`; so every prime factor of a divisor of
  `row(s)` is `q` or a prime factor of `J`.

A certificate lists sources `(s, p)` (a new source `s` and an earlier source `p` whose row it
divides) and pieces `(s, M, w)` with `M > 1` dividing `row(s)` for a listed source `s`, the
pieces pairwise coprime. A piece counts `1`, or `2` when the witness `w` shows that `M` is not
a prime power (`EqCount.witnessOK`). The pieces have pairwise disjoint sets of prime factors
inside `{q} ∪ J.primeFactors`; so a total count of at least `k + 2` contradicts
`J.primeFactors.card ≤ k` (`supportCheck_sound`).

Restricted result; no published source was checked; novelty not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect.EqSupport

open OddPerfect.EqCount (fermatRes weight witnessOK weight_le)
open OddPerfect.EqChain (gm dvd_sigma_of_gm)

/-! ## Computable checker -/

/-- Trial division by `m, m + 2, ...` while `m * m ≤ q`. -/
def tdivS (q : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, m => q < m * m || (q % m != 0 && tdivS q f (m + 2))

/-- Primality by trial division over odd numbers up to the square root. -/
def sPrime (q : ℕ) : Bool := decide (2 ≤ q) && (q == 2 || (q % 2 != 0 && tdivS q q 3))

/-- The sources: each new source `s` is an odd prime `s ≤ B` dividing the row of an earlier
source `p` (the list `G` holds the sources accepted so far). -/
def srcsOK (l B : ℕ) : List ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | G, (s, p) :: rest =>
    G.contains p && sPrime s && s % 2 == 1 && s ≤ B && gm p s l == 0 && srcsOK l B (s :: G) rest

/-- Walk the pieces `(s, M, w)` with product `P` and count `k`; close when `t ≤ k`. -/
def piecesOK (l t : ℕ) (G : List ℕ) : ℕ → ℕ → List (ℕ × ℕ × ℕ) → Bool
  | _, k, [] => t ≤ k
  | P, k, (s, M, w) :: rest =>
    G.contains s && 1 < M && gm s M l == 0 && Nat.gcd M P == 1 && witnessOK M w &&
      piecesOK l t G (P * M) (k + weight w) rest

/-- A whole certificate for `l`, source bound `B` and target count `t`. -/
def supportCheck (l B t : ℕ) (srcs : List (ℕ × ℕ)) (pieces : List (ℕ × ℕ × ℕ)) : Bool :=
  l ≤ B && srcsOK l B [l] srcs && piecesOK l t (l :: srcs.map Prod.fst) 1 0 pieces

/-! ## Soundness of the primality test -/

/-- Soundness of `tdivS`. -/
theorem tdivS_sound (q : ℕ) : ∀ f m, tdivS q f m = true →
    ∀ k, m ≤ k → k % 2 = m % 2 → k * k ≤ q → q % k ≠ 0
  | 0, _, h => by simp [tdivS] at h
  | f + 1, m, h => by
    intro k hmk hpar hkq
    simp only [tdivS, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne,
      ne_eq] at h
    rcases h with h | ⟨h1, h2⟩
    · exact absurd (lt_of_lt_of_le h (Nat.mul_le_mul hmk hmk)) (not_lt.mpr hkq)
    · rcases Nat.eq_or_lt_of_le hmk with rfl | hlt
      · exact h1
      · exact tdivS_sound q f (m + 2) h2 k (by omega) (by omega) hkq

/-- Soundness of `sPrime`. -/
theorem sPrime_sound {q : ℕ} (h : sPrime q = true) : q.Prime := by
  simp only [sPrime, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq] at h
  rcases h with ⟨h2, rfl | ⟨hodd, ht⟩⟩
  · exact Nat.prime_two
  by_contra hp
  have hm := Nat.minFac_prime (show q ≠ 1 by omega)
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  have hdvd := Nat.minFac_dvd q
  have hm2 : q.minFac % 2 = 1 := by
    rcases hm.eq_two_or_odd with h' | h'
    · rw [h'] at hdvd
      exact absurd (Nat.mod_eq_zero_of_dvd hdvd) hodd
    · exact h'
  have hm3 : 3 ≤ q.minFac := by have := hm.two_le; omega
  exact tdivS_sound q q 3 ht _ hm3 (by omega) (by simpa [pow_two] using hsq)
    (Nat.mod_eq_zero_of_dvd hdvd)

/-! ## Soundness -/

/-- Divisor sum of a full prime power component divides the divisor sum of the number. -/
theorem sigma_component_dvd' {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    σ 1 (p ^ n.factorization p) ∣ σ 1 n := by
  have hcop := (Nat.coprime_ordCompl hp hn).pow_left (n.factorization p)
  calc σ 1 (ordProj[p] n) ∣ σ 1 (ordProj[p] n) * σ 1 (ordCompl[p] n) := dvd_mul_right _ _
    _ = σ 1 (ordProj[p] n * ordCompl[p] n) :=
      (isMultiplicative_sigma.map_mul_of_coprime hcop).symm
    _ = σ 1 n := by rw [Nat.ordProj_mul_ordCompl_eq_self]

/-- The Euler frame: `m ≠ 0`, `v_q(N) = a`, `a` odd, and `v_p(N) = v_p(m ^ 2)` for `p ≠ q`. -/
theorem euler_frame {N q a m : ℕ} (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2)
    (hqm : ¬ q ∣ m) :
    m ≠ 0 ∧ N.factorization q = a ∧ Odd a ∧
      ∀ p, p ≠ q → N.factorization p = (m ^ 2).factorization p := by
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hfac : ∀ p, N.factorization p = (q ^ a).factorization p + (m ^ 2).factorization p := by
    intro p
    rw [hN, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm),
      Finsupp.add_apply]
  have hqa : N.factorization q = a := by
    rw [hfac, hq.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (fun hd => hqm (hq.dvd_of_dvd_pow hd)), add_zero]
  refine ⟨hm, hqa, ?_, fun p hp => ?_⟩
  · rcases Nat.even_or_odd a with ⟨j, hj⟩ | ho
    · exact absurd ⟨q ^ j * m, by rw [hN, hj]; ring⟩ (not_isSquare h)
    · exact ho
  · rw [hfac, hq.factorization_pow, Finsupp.single_apply, ite_eq_right (Ne.symm hp), zero_add]

section Sound

variable {N q a m l B : ℕ}

/-- A good source: a prime factor of `N` other than `q`. -/
abbrev Good (N q s : ℕ) : Prop := s.Prime ∧ s ∣ N ∧ s ≠ q

/-- The row of a good source divides `q ^ a J`. -/
theorem row_dvd (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) {s : ℕ}
    (hs : Good N q s) : σ 1 (s ^ (l - 1)) ∣ q ^ a * eulerIndex q a m := by
  obtain ⟨hm, -, -, hfm⟩ := euler_frame h hq hN hqm
  have hsN : s ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hs.1, hs.2.1, h.ne_zero⟩
  have he : (m ^ 2).factorization s = l - 1 := by rw [← hfm s hs.2.2, hexp s hsN hs.2.2]
  rw [← sigma_sq_eq_mul_eulerIndex h hq hN hqm, ← he]
  exact sigma_component_dvd' (pow_ne_zero _ hm) hs.1

/-- A new source accepted by `srcsOK` is good. -/
theorem srcsOK_sound (h : OddPerfect N) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) (hB : B < q) :
    ∀ (srcs : List (ℕ × ℕ)) (G : List ℕ), (∀ s ∈ G, Good N q s) → srcsOK l B G srcs = true →
      ∀ s ∈ srcs.map Prod.fst, Good N q s := by
  intro srcs
  induction srcs with
  | nil => intro G _ _ s hs; simp at hs
  | cons e rest ih =>
    obtain ⟨s, p⟩ := e
    intro G hG hc
    simp only [srcsOK, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq,
      beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨⟨hpG, hsP⟩, hs2⟩, hsB⟩, hgm⟩, hnext⟩ := hc
    have hsp := sPrime_sound hsP
    obtain ⟨hpp, hpN, hpq⟩ := hG p hpG
    have hpN' : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpN, h.ne_zero⟩
    have hsd : s ∣ σ 1 (p ^ (l - 1)) := dvd_sigma_of_gm hpp hl.one_lt.le hgm
    have hsN : s ∣ N := OPNStarter.force_prime h.perfect hpp (hexp p hpN' hpq) hsp
      (by rintro rfl; omega) hsd
    have hgood : Good N q s := ⟨hsp, hsN, by omega⟩
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

/-- The meaning of a state `(P, k)` of the piece walk. -/
abbrev Holds (q J P k : ℕ) : Prop :=
  P ≠ 0 ∧ (∀ r ∈ P.primeFactors, r ∈ insert q J.primeFactors) ∧ k ≤ P.primeFactors.card

/-- Soundness of the piece walk: an accepted walk refutes every state that holds. -/
theorem piecesOK_sound (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2)
    (hqm : ¬ q ∣ m) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) {k0 : ℕ}
    (hJ : (eulerIndex q a m).primeFactors.card ≤ k0) {G : List ℕ} (hG : ∀ s ∈ G, Good N q s) :
    ∀ (c : List (ℕ × ℕ × ℕ)) (P k : ℕ), piecesOK l (k0 + 2) G P k c = true →
      Holds q (eulerIndex q a m) P k → False := by
  set J := eulerIndex q a m with hJdef
  have hσ : σ 1 (m ^ 2) = q ^ a * J := sigma_sq_eq_mul_eulerIndex h hq hN hqm
  obtain ⟨hm, -, -, -⟩ := euler_frame h hq hN hqm
  have hJ0 : J ≠ 0 := by
    intro h0
    have := sigma_pos 1 (m ^ 2) (pow_ne_zero 2 hm)
    rw [hσ, h0, mul_zero] at this
    exact lt_irrefl 0 this
  intro c
  induction c with
  | nil =>
    intro P k hr hs
    obtain ⟨-, hPf, hk⟩ := hs
    simp only [piecesOK, decide_eq_true_eq] at hr
    have h1 := Finset.card_le_card (show P.primeFactors ⊆ insert q J.primeFactors from hPf)
    have h2 := Finset.card_insert_le q J.primeFactors
    omega
  | cons e rest ih =>
    obtain ⟨s, M, w⟩ := e
    intro P k hr hs
    simp only [piecesOK, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq,
      beq_iff_eq] at hr
    obtain ⟨⟨⟨⟨⟨hsG, hM1⟩, hgm⟩, hcop⟩, hw⟩, hnext⟩ := hr
    have hgs := hG s hsG
    have hMrow : M ∣ q ^ a * J :=
      (dvd_sigma_of_gm hgs.1 hl.one_lt.le hgm).trans (row_dvd h hq hN hqm hexp hgs)
    have hM0 : M ≠ 0 := by omega
    have hcop' : Nat.Coprime M P := hcop
    refine ih (P * M) (k + weight w) hnext ⟨mul_ne_zero hs.1 hM0, fun r hr => ?_, ?_⟩
    · rw [Nat.primeFactors_mul hs.1 hM0, Finset.mem_union] at hr
      rcases hr with hr | hr
      · exact hs.2.1 r hr
      · have hrP := Nat.prime_of_mem_primeFactors hr
        have hrd := (Nat.dvd_of_mem_primeFactors hr).trans hMrow
        rcases (Nat.Prime.dvd_mul hrP).mp hrd with h' | h'
        · exact Finset.mem_insert.mpr
            (Or.inl ((Nat.prime_dvd_prime_iff_eq hrP hq).mp (hrP.dvd_of_dvd_pow h')))
        · exact Finset.mem_insert_of_mem (Nat.mem_primeFactors.mpr ⟨hrP, h', hJ0⟩)
    · rw [Nat.Coprime.primeFactors_mul hcop'.symm, Finset.card_union_of_disjoint
        hcop'.symm.disjoint_primeFactors]
      have := weight_le hM1 hw
      have := hs.2.2
      omega

end Sound

/-- Soundness of an accepted support certificate. In the family where every ordinary exponent
equals `l - 1`, an Euler index `J` with at most `k` prime factors, a special prime above `B`
and a certificate accepted with target `k + 2` give a contradiction. Restricted result; no
published source was checked; novelty not verified. -/
theorem supportCheck_sound {N q a m l B k : ℕ} {srcs : List (ℕ × ℕ)}
    {pieces : List (ℕ × ℕ × ℕ)} (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2)
    (hqm : ¬ q ∣ m) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hJ : (eulerIndex q a m).primeFactors.card ≤ k) (hB : B < q)
    (hc : supportCheck l B (k + 2) srcs pieces = true) : False := by
  simp only [supportCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hlB, hsrc⟩, hpc⟩ := hc
  obtain ⟨-, hqa, hao, -⟩ := euler_frame h hq hN hqm
  by_cases hlN : l ∣ N
  · have hlg : Good N q l := ⟨hl, hlN, by omega⟩
    have hG0 : ∀ s ∈ [l], Good N q s := fun s hs => by
      rw [List.mem_singleton] at hs
      exact hs ▸ hlg
    have hS := srcsOK_sound h hl hexp hB srcs [l] hG0 hsrc
    have hG : ∀ s ∈ l :: srcs.map Prod.fst, Good N q s := by
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact hlg
      · exact hS s hs
    exact piecesOK_sound h hq hN hqm hl hexp hJ hG pieces 1 0 hpc
      ⟨one_ne_zero, by simp, by simp⟩
  · exact not_all_exponents_eq_pred_prime h hq (hqa ▸ hao) hl hl2 hlN hexp

end OddPerfect.EqSupport

#print axioms OddPerfect.EqSupport.tdivS_sound
#print axioms OddPerfect.EqSupport.sPrime_sound
#print axioms OddPerfect.EqSupport.sigma_component_dvd'
#print axioms OddPerfect.EqSupport.euler_frame
#print axioms OddPerfect.EqSupport.row_dvd
#print axioms OddPerfect.EqSupport.srcsOK_sound
#print axioms OddPerfect.EqSupport.piecesOK_sound
#print axioms OddPerfect.EqSupport.supportCheck_sound
