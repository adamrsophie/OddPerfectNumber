import OddPerfect.ThreeExceptionsUniform
import OddPerfect.Euler

/-!
# Any bounded number of exceptions for a large common index prime (reduction to a gap statement)

Let `N` be an odd perfect number, `E` a finite set of at most `s` natural numbers, and `l` a prime
such that every prime factor `p ∉ E` of `N` has `l ∣ e_p + 1`, with at least one prime factor
outside `E`. `exists_index_bound_of_exceptions_of` shows: if the gap statement
`GeneralGapStatement s` holds for every `s`, then for every `s` there is a bound `L` with
`l ∣ N` for every such `N` and every prime `l ≥ L`. The bound is not explicit: the proof gives no
value for it, since the gap statement provides none. For two and three exceptions the landed
modules `OddPerfect.TwoExceptionsUniform` and `OddPerfect.ThreeExceptionsUniform` give explicit
bounds, `l ≥ 23` and `l ≥ 359`.

The argument follows `OddPerfect.ThreeExceptionsUniform` with `S = s + 1`, `A = (l - 1) / S`,
`G = (A + 1) / (4 S)` and the block base `3 ^ G`. The compatible primes up to `3 ^ G` and the
exceptions that are not receivers form at most `S` prime factors; their component abundancies
multiply to less than `2`, hence to less than `2 - ε` by the gap statement. The receivers and
the compatible primes above `3 ^ G` contribute at most `1 / (1 - x)` with
`x = S / (3 ^ G - 1) + S / (2 l) ≤ ε / 2`.

Restricted result; published method, see below; novelty not verified. The odd perfect
number conjecture remains open.

Method. The count of monomials `p ^ i * p' ^ j` below a prime power modulus, all of them roots
of `X ^ l = 1`, is Lemma 3.1 of T. Yamada, On finiteness of odd superperfect numbers
(arXiv 0803.0437v7). A gap of this kind between two primes with a common dominant receiver is
Lemma 3.2 there (with other constants), and the split of the sources into classes by dominant
receiver is the proof of Lemma 3.3 there. That paper does not state the theorems of this
module; no other source was checked.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The gap statement for sets of at most `s` odd prime powers of Euler form. -/
def GeneralGapStatement (s : ℕ) : Prop :=
    ∃ ε : ℚ, 0 < ε ∧
      ∀ (C : Finset ℕ) (e : ℕ → ℕ) (q : ℕ), C.card ≤ s → (∀ c ∈ C, c.Prime ∧ c ≠ 2) →
        (∀ c ∈ C, c ≠ q → Even (e c)) → (q ∈ C → q % 4 = 1 ∧ e q % 4 = 1) →
        ∏ c ∈ C, ((σ 1 (c ^ e c) : ℚ) / ((c : ℚ) ^ e c)) < 2 →
        ∏ c ∈ C, ((σ 1 (c ^ e c) : ℚ) / ((c : ℚ) ^ e c)) < 2 - ε

namespace ExcS

open OddPerfect.TwoExcGen OddPerfect.ExcUniform

/-- Every prime factor of the row of a compatible prime is a prime factor of `N`, an element
of `E`, and `1` modulo `l`. -/
theorem keyE {l N : ℕ} {E : Finset ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (h : OddPerfect N)
    (hlN : ¬ l ∣ N) (hcomp : ∀ p ∈ N.primeFactors, p ∉ E → l ∣ N.factorization p + 1)
    {p : ℕ} (hp : p ∈ N.primeFactors) (hpE : p ∉ E) {s : ℕ}
    (hs : s.Prime) (hsR : s ∣ ∑ i ∈ Finset.range l, p ^ i) :
    s ∈ N.primeFactors ∧ s ∈ E ∧ s % l = 1 := by
  have hpP := Nat.prime_of_mem_primeFactors hp
  have hN := h.ne_zero
  have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl.one_lt.le
  have hdv : σ 1 (p ^ (l - 1)) ∣ σ 1 (p ^ N.factorization p) :=
    OPNExample.sigma_prime_pow_dvd (a := l - 1) hpP (by rw [hl1]; exact hcomp p hp hpE)
  rw [R_eq_sigma hl.one_lt.le hpP] at hsR
  have hsl : s % l = 1 := by
    rcases prime_dvd_sigma_prime_pow_of_prime_length hpP hs hl hsR with h1 | h1
    · subst h1
      exact absurd (OPNStarter.force_prime h.perfect hpP rfl hl hl2 (hsR.trans hdv)) hlN
    · exact h1
  have hs2 : s ≠ 2 := by
    intro h2
    rw [h2] at hsl
    have := hl.two_le
    have : 2 % l = 2 := Nat.mod_eq_of_lt (by omega)
    omega
  have hsN : s ∣ N := OPNStarter.force_prime h.perfect hpP rfl hs hs2 (hsR.trans hdv)
  have hsP : s ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hs, hsN, hN⟩
  refine ⟨hsP, ?_, hsl⟩
  by_contra hsE
  have hd2 : σ 1 (s ^ (l - 1)) ∣ σ 1 (s ^ N.factorization s) :=
    OPNExample.sigma_prime_pow_dvd (a := l - 1) hs (by rw [hl1]; exact hcomp s hsP hsE)
  have hls : l ∣ σ 1 (s ^ (l - 1)) := by
    rw [← R_eq_sigma hl.one_lt.le hs]
    exact dvd_R_of_mod hl.two_le hsl
  exact hlN (OPNStarter.force_prime h.perfect hs rfl hl hl2 (hls.trans hd2))

/-- The pair count with `A = (l - 1) / S` and `G = (A + 1) / (4 S)` exceeds `l`. -/
theorem count_gtS {l S A G : ℕ} (hS : 1 ≤ S) (hA : A = (l - 1) / S)
    (hG : G = (A + 1) / (4 * S)) (hG1 : 1 ≤ G) (hl : 1 ≤ l) :
    l < ∑ j ∈ Finset.range (A / G + 1), (A - G * j + 1) := by
  have h4 : G * (4 * S) ≤ A + 1 := by rw [hG]; exact Nat.div_mul_le_self _ _
  have hlA : l ≤ S * A + S := by
    have h1 := Nat.div_add_mod (l - 1) S
    have h2 := Nat.mod_lt (l - 1) (show S > 0 by omega)
    rw [← hA] at h1
    omega
  have e24 : G * (2 * S) * 2 = G * (4 * S) := by ring
  have e2S : 2 * S * G = G * (2 * S) := by ring
  have hX : 1 ≤ G * (2 * S) := Nat.mul_pos (by omega) (by omega)
  have hdiv : 2 * S ≤ A / G := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hsub : Finset.range (2 * S + 1) ⊆ Finset.range (A / G + 1) :=
    Finset.range_subset_range.mpr (by omega)
  have e1 := Finset.sum_le_sum_of_subset (f := fun j => A - G * j + 1) hsub
  have e2 : ∑ _j ∈ Finset.range (2 * S + 1), (A + 1 - G * (2 * S)) ≤
      ∑ j ∈ Finset.range (2 * S + 1), (A - G * j + 1) := Finset.sum_le_sum fun j hj => by
    have := Finset.mem_range.mp hj
    have : G * j ≤ G * (2 * S) := Nat.mul_le_mul_left _ (by omega)
    omega
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at e2
  have hT2 : A + 1 ≤ 2 * (A + 1 - G * (2 * S)) := by omega
  have e3 : S * (A + 1) ≤ S * (2 * (A + 1 - G * (2 * S))) := Nat.mul_le_mul_left S hT2
  have e4 : (2 * S + 1) * (A + 1 - G * (2 * S)) =
      S * (2 * (A + 1 - G * (2 * S))) + (A + 1 - G * (2 * S)) := by ring
  have e5 : S * (A + 1) = S * A + S := by ring
  omega

/-- The argument for fixed parameters. -/
theorem core {N l S n : ℕ} {ε : ℚ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hS : 1 ≤ S)
    (hn : 4 * (S : ℚ) < n * ε)
    (hgapC : ∀ (C : Finset ℕ) (e : ℕ → ℕ) (q : ℕ), C.card ≤ S → (∀ c ∈ C, c.Prime ∧ c ≠ 2) →
        (∀ c ∈ C, c ≠ q → Even (e c)) → (q ∈ C → q % 4 = 1 ∧ e q % 4 = 1) →
        ∏ c ∈ C, ((σ 1 (c ^ e c) : ℚ) / ((c : ℚ) ^ e c)) < 2 →
        ∏ c ∈ C, ((σ 1 (c ^ e c) : ℚ) / ((c : ℚ) ^ e c)) < 2 - ε)
    (h : OddPerfect N) (hl : l.Prime) (hL : 4 * S * S * (n + 2) + n + 3 ≤ l)
    {E : Finset ℕ} (hE : E.card ≤ S) (hex : ∃ p ∈ N.primeFactors, p ∉ E)
    (hcomp : ∀ p ∈ N.primeFactors, p ∉ E → l ∣ N.factorization p + 1) : l ∣ N := by
  classical
  by_contra hlN
  have hl2 : l ≠ 2 := by omega
  obtain ⟨A, hA⟩ : ∃ A, A = (l - 1) / S := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = (A + 1) / (4 * S) := ⟨_, rfl⟩
  have hAS : A * S ≤ l - 1 := by rw [hA]; exact Nat.div_mul_le_self _ _
  have hA4 : 4 * S * (n + 2) ≤ A := by
    rw [hA]
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    have : 4 * S * (n + 2) * S = 4 * S * S * (n + 2) := by ring
    omega
  have hGn : n + 2 ≤ G := by
    rw [hG]
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    have : (n + 2) * (4 * S) = 4 * S * (n + 2) := by ring
    omega
  have hG2 : 2 ≤ G := by omega
  have hcount : l < ∑ j ∈ Finset.range (A / G + 1), (A - G * j + 1) :=
    count_gtS hS hA hG (by omega) (by omega)
  obtain ⟨M, hM⟩ : ∃ M, M = 3 ^ G := ⟨_, rfl⟩
  have hMG : G < M := by rw [hM]; exact Nat.lt_pow_self (by norm_num)
  have hM2 : 2 ≤ M := by omega
  set P := N.primeFactors with hP
  have hP2 : ∀ p ∈ P, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hP3 : ∀ p ∈ P, 3 ≤ p ∧ p % 2 = 1 := fun p hp => by
    have h1 := odd_of_mem h hp
    have h2 := hP2 p hp
    exact ⟨by omega, h1⟩
  set Gc := P.filter (fun p => p ∉ E) with hGc
  set Ex := P.filter (fun p => ¬ p ∉ E) with hEx
  have hGm : ∀ p ∈ Gc, p ∈ P ∧ p ∉ E := fun p hp => Finset.mem_filter.mp hp
  have hExP : Ex ⊆ P := Finset.filter_subset _ _
  have hExcard : Ex.card ≤ S := by
    refine le_trans (Finset.card_le_card fun x hx => ?_) hE
    exact not_not.mp (Finset.mem_filter.mp hx).2
  -- a receiver with a large power is a prime factor of `N` in `E`, `1` modulo `l`
  have hrecv : ∀ p ∈ Gc, ∀ d, p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d →
      d ∈ Ex ∧ d.Prime ∧ d % l = 1 := by
    intro p hp d hd
    obtain ⟨hpP, hpE⟩ := hGm p hp
    have hv : (∑ i ∈ Finset.range l, p ^ i).factorization d ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hd
      exact absurd hd (not_lt.mpr (Nat.one_le_pow _ _ (by have := hP2 p hpP; omega)))
    have hmem : d ∈ (∑ i ∈ Finset.range l, p ^ i).primeFactors := by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.mpr hv
    have hdP : d.Prime := Nat.prime_of_mem_primeFactors hmem
    have hdR : d ∣ ∑ i ∈ Finset.range l, p ^ i := Nat.dvd_of_mem_primeFactors hmem
    obtain ⟨hdN, hdE, hdl⟩ := keyE hl hl2 h hlN hcomp hpP hpE hdP hdR
    exact ⟨Finset.mem_filter.mpr ⟨hdN, fun hc => hc hdE⟩, hdP, hdl⟩
  -- every compatible prime has a receiver with a large power
  have hcover : ∀ p ∈ Gc, ∃ d, p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d := by
    intro p hp
    obtain ⟨hpP, hpE⟩ := hGm p hp
    have hsub : (∑ i ∈ Finset.range l, p ^ i).primeFactors ⊆ E := fun x hx =>
      (keyE hl hl2 h hlN hcomp hpP hpE (Nat.prime_of_mem_primeFactors hx)
        (Nat.dvd_of_mem_primeFactors hx)).2.1
    have hR0 : (∑ i ∈ Finset.range l, p ^ i) ≠ 0 :=
      (lt_trans zero_lt_one (R_one_lt hl.two_le (hP2 p hpP))).ne'
    have hlt := pow_lt_R hl.two_le (show 1 ≤ p by have := hP2 p hpP; omega)
    have hp1 : 1 ≤ p ^ A := Nat.one_le_pow _ _ (by have := hP2 p hpP; omega)
    by_contra hno
    push Not at hno
    have e0 : ∏ s ∈ (∑ i ∈ Finset.range l, p ^ i).primeFactors,
        s ^ (∑ i ∈ Finset.range l, p ^ i).factorization s = ∑ i ∈ Finset.range l, p ^ i :=
      Nat.prod_factorization_pow_eq_self hR0
    have e1 : ∑ i ∈ Finset.range l, p ^ i ≤ ∏ s ∈ (∑ i ∈ Finset.range l, p ^ i).primeFactors,
        p ^ A := by
      calc _ = _ := e0.symm
        _ ≤ _ := Finset.prod_le_prod fun s _ => hno s
    rw [Finset.prod_const] at e1
    have e2 : (p ^ A) ^ (∑ i ∈ Finset.range l, p ^ i).primeFactors.card ≤ (p ^ A) ^ S :=
      Nat.pow_le_pow_right hp1 ((Finset.card_le_card hsub).trans hE)
    have e3 : (p ^ A) ^ S ≤ p ^ (l - 1) := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by have := hP2 p hpP; omega) hAS
    omega
  -- the receivers
  set D := Ex.filter (fun d => ∃ p ∈ Gc,
    p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d) with hD
  set D' := Ex.filter (fun d => ¬ ∃ p ∈ Gc,
    p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d) with hD'
  have hDE : D ⊆ Ex := Finset.filter_subset _ _
  have hDcard : D.card ≤ S := (Finset.card_le_card hDE).trans hExcard
  have hDprop : ∀ d ∈ D, 2 * l + 1 ≤ d ∧ d.Prime ∧ d ≠ l := by
    intro d hd
    obtain ⟨-, p, hp, hpd⟩ := Finset.mem_filter.mp hd
    obtain ⟨-, hdP, hdl⟩ := hrecv p hp d hpd
    have h1 : l ∣ d - 1 := by
      have := Nat.dvd_sub_mod (n := l) d
      rwa [hdl] at this
    have hdodd := (hP3 d (hExP (hDE hd))).2
    have h2 : 2 ∣ d - 1 := Nat.dvd_of_mod_eq_zero (by omega)
    have h3 : l * 2 ∣ d - 1 :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hl Nat.prime_two).mpr hl2) h1 h2
    have h4 := Nat.le_of_dvd (by have := hdP.two_le; omega) h3
    refine ⟨by omega, hdP, ?_⟩
    intro hdl'
    rw [hdl', Nat.mod_self] at hdl
    omega
  -- two compatible primes sharing a receiver are far apart
  have hgap : ∀ d ∈ D, ∀ p ∈ Gc, ∀ p' ∈ Gc, p < p' →
      p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d →
      p' ^ A < d ^ (∑ i ∈ Finset.range l, p' ^ i).factorization d → p ^ G < p' := by
    intro d hd p hp p' hp' hpp' h1 h2
    obtain ⟨-, hdP, hdl⟩ := hDprop d hd
    have hpP := Nat.prime_of_mem_primeFactors (hGm p hp).1
    have hp'P := Nat.prime_of_mem_primeFactors (hGm p' hp').1
    exact pow_lt_of_common_receiver_power hl hdP hdl hpP hp'P hpp' (Nat.ordProj_dvd _ d)
      (Nat.ordProj_dvd _ d) h1 (lt_of_le_of_lt (Nat.pow_le_pow_left hpp'.le A) h2) hcount
  -- a set of compatible primes without far apart pairs has at most `D.card` elements
  have hcnt : ∀ X ⊆ Gc, (∀ p ∈ X, ∀ p' ∈ X, p < p' → p' ≤ p ^ G) → X.card ≤ D.card := by
    intro X hXG hX
    have hsub : X ⊆ D.biUnion (fun d => X.filter
        (fun p => p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d)) := by
      intro p hp
      obtain ⟨d, hd⟩ := hcover p (hXG hp)
      rw [Finset.mem_biUnion]
      exact ⟨d, Finset.mem_filter.mpr ⟨(hrecv p (hXG hp) d hd).1, p, hXG hp, hd⟩,
        Finset.mem_filter.mpr ⟨hp, hd⟩⟩
    have hone : ∀ d ∈ D, (X.filter
        (fun p => p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d)).card ≤ 1 := by
      intro d hd
      rw [Finset.card_le_one]
      intro p hp p' hp'
      rw [Finset.mem_filter] at hp hp'
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have := hgap d hd p (hXG hp.1) p' (hXG hp'.1) hlt hp.2 hp'.2
        have := hX p hp.1 p' hp'.1 hlt
        omega
      · have := hgap d hd p' (hXG hp'.1) p (hXG hp.1) hlt hp'.2 hp.2
        have := hX p' hp'.1 p hp.1 hlt
        omega
    calc X.card ≤ (D.biUnion (fun d => X.filter
          (fun p => p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ d ∈ D, (X.filter
          (fun p => p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _d ∈ D, 1 := Finset.sum_le_sum hone
      _ = D.card := by simp
  -- the compatible primes up to `M` and above `M`
  set S0 := Gc.filter (fun p => p ≤ M) with hS0
  set Gt := Gc.filter (fun p => ¬ p ≤ M) with hGt
  have hS0G : S0 ⊆ Gc := Finset.filter_subset _ _
  have hGtG : Gt ⊆ Gc := Finset.filter_subset _ _
  have hS0c : S0.card ≤ D.card := hcnt S0 hS0G (fun p hp p' hp' _ => by
    have h1 := (hP3 p (hGm p (hS0G hp)).1).1
    have h2 := (Finset.mem_filter.mp hp').2
    have : M ≤ p ^ G := by rw [hM]; exact Nat.pow_le_pow_left h1 G
    omega)
  have hGtbig : ∀ p ∈ Gt, M < p := fun p hp => by
    have := (Finset.mem_filter.mp hp).2
    omega
  have hblock : ∀ j, 1 ≤ j → (Gt.filter (fun p => M ^ j < p ∧ p ≤ M ^ (j + 1))).card ≤ S := by
    intro j hj
    refine le_trans (hcnt _ ((Finset.filter_subset _ _).trans hGtG) ?_) hDcard
    intro p hp p' hp' _
    have h1 := (Finset.mem_filter.mp hp).2.1
    have h2 := (Finset.mem_filter.mp hp').2.2
    have e1 : (M ^ j) ^ G < p ^ G := Nat.pow_lt_pow_left h1 (by omega)
    have hjG : j * 2 ≤ j * G := Nat.mul_le_mul_left j hG2
    have e2 : M ^ (j + 1) ≤ (M ^ j) ^ G := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hsumT := sum_inv_pred_le_of_interval_card (B := M) (c := S) hM2 hGtbig hblock
  -- the receivers: `1 / (d - 1) ≤ 1 / (2 l)`
  have hl0 : (0 : ℚ) < 2 * l := by
    have : (1 : ℚ) ≤ l := by exact_mod_cast hl.one_lt.le
    linarith
  have hsumD : ∑ p ∈ D, (1 : ℚ) / ((p : ℚ) - 1) ≤ (S : ℚ) / (2 * l) := by
    calc ∑ p ∈ D, (1 : ℚ) / ((p : ℚ) - 1) ≤ ∑ _p ∈ D, (1 : ℚ) / (2 * l) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have h1 : ((2 * l + 1 : ℕ) : ℚ) ≤ p := by exact_mod_cast (hDprop p hp).1
          push_cast at h1
          exact one_div_le_one_div_of_le hl0 (by linarith)
      _ = (D.card : ℚ) * (1 / (2 * l)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (S : ℚ) * (1 / (2 * l)) := by
          have : (D.card : ℚ) ≤ S := by exact_mod_cast hDcard
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = (S : ℚ) / (2 * l) := by rw [mul_one_div]
  -- the two parts of `x` are at most `ε / 4`
  have hMq : (n : ℚ) + 1 ≤ (M : ℚ) - 1 := by
    have : ((n + 2 : ℕ) : ℚ) ≤ (M : ℚ) := by exact_mod_cast (show n + 2 ≤ M by omega)
    push_cast at this
    linarith
  have hlq : (n : ℚ) ≤ l := by exact_mod_cast (show n ≤ l by omega)
  have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  have hx1 : (S : ℚ) / ((M : ℚ) - 1) ≤ ε / 4 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hMq hε.le]
  have hx2 : (S : ℚ) / (2 * l) ≤ ε / 4 := by
    rw [div_le_iff₀ hl0]
    nlinarith [mul_le_mul_of_nonneg_left hlq hε.le]
  have hdisjT : Disjoint Gt D := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_filter.mp (hDE hx')).2 (hGm x (hGtG hx)).2
  have hsumU : ∑ p ∈ Gt ∪ D, (1 : ℚ) / ((p : ℚ) - 1) ≤
      (S : ℚ) / ((M : ℚ) - 1) + (S : ℚ) / (2 * l) := by
    rw [Finset.sum_union hdisjT]
    exact add_le_add hsumT hsumD
  have hU2 : ∀ p ∈ Gt ∪ D, 2 ≤ p := fun p hp => by
    rcases Finset.mem_union.mp hp with h1 | h1
    · exact hP2 p (hGm p (hGtG h1)).1
    · exact hP2 p (hExP (hDE h1))
  have hprodU := prod_ab_le_of_sum hU2 hsumU (by linarith)
  -- the kept part
  have hDD' : D.card + D'.card = Ex.card := Finset.card_filter_add_card_filter_not _
  have hdisj : Disjoint S0 D' := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_filter.mp (Finset.filter_subset _ _ hx')).2 (hGm x (hS0G hx)).2
  have hU : (S0 ∪ D').card ≤ S := by
    have := Finset.card_union_le S0 D'
    omega
  have hUP : S0 ∪ D' ⊆ P := by
    intro p hp
    rcases Finset.mem_union.mp hp with h1 | h1
    · exact (hGm p (hS0G h1)).1
    · exact hExP (Finset.filter_subset _ _ h1)
  -- components
  have hf1 : ∀ p ∈ P, 1 ≤ abundancy (p ^ N.factorization p) := fun p hp =>
    ThreeGap.one_le_abundancy_pow (Nat.prime_of_mem_primeFactors hp) _
  have hfab : ∀ p ∈ P, abundancy (p ^ N.factorization p) ≤ ab p := fun p hp =>
    (abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors hp) _).le
  have hTf : ∏ p ∈ Gt, abundancy (p ^ N.factorization p) ≤ ∏ p ∈ Gt, ab p :=
    Finset.prod_le_prod₀ (fun p hp => zero_le_one.trans (hf1 p (hGm p (hGtG hp)).1))
      fun p hp => hfab p (hGm p (hGtG hp)).1
  have hDf : ∏ p ∈ D, abundancy (p ^ N.factorization p) ≤ ∏ p ∈ D, ab p :=
    Finset.prod_le_prod₀ (fun p hp => zero_le_one.trans (hf1 p (hExP (hDE hp))))
      fun p hp => hfab p (hExP (hDE hp))
  have hprod : ∏ p ∈ P, abundancy (p ^ N.factorization p) = 2 := by
    rw [hP, ← abundancy_eq_prod_primeFactors h.ne_zero]
    exact (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
  have e1 : (∏ p ∈ Gc, abundancy (p ^ N.factorization p)) *
      (∏ p ∈ Ex, abundancy (p ^ N.factorization p)) =
      ∏ p ∈ P, abundancy (p ^ N.factorization p) :=
    Finset.prod_filter_mul_prod_filter_not P _ _
  have e2 : (∏ p ∈ S0, abundancy (p ^ N.factorization p)) *
      (∏ p ∈ Gt, abundancy (p ^ N.factorization p)) =
      ∏ p ∈ Gc, abundancy (p ^ N.factorization p) :=
    Finset.prod_filter_mul_prod_filter_not Gc _ _
  have e3 : (∏ p ∈ D, abundancy (p ^ N.factorization p)) *
      (∏ p ∈ D', abundancy (p ^ N.factorization p)) =
      ∏ p ∈ Ex, abundancy (p ^ N.factorization p) :=
    Finset.prod_filter_mul_prod_filter_not Ex _ _
  have e4 : ∏ p ∈ S0 ∪ D', abundancy (p ^ N.factorization p) =
      (∏ p ∈ S0, abundancy (p ^ N.factorization p)) *
        (∏ p ∈ D', abundancy (p ^ N.factorization p)) :=
    Finset.prod_union hdisj
  have hsplit : (2 : ℚ) = (∏ p ∈ S0 ∪ D', abundancy (p ^ N.factorization p)) *
      ((∏ p ∈ Gt, abundancy (p ^ N.factorization p)) *
      (∏ p ∈ D, abundancy (p ^ N.factorization p))) := by
    rw [← hprod, ← e1, ← e2, ← e3, e4]
    ring
  have nT : 1 ≤ ∏ p ∈ Gt, abundancy (p ^ N.factorization p) :=
    Finset.one_le_prod₀ fun p hp => hf1 p (hGm p (hGtG hp)).1
  have nK : 0 ≤ ∏ p ∈ S0 ∪ D', abundancy (p ^ N.factorization p) :=
    Finset.prod_nonneg fun p hp => zero_le_one.trans (hf1 p (hUP hp))
  -- a receiver exists, and its component exceeds `1`
  have hD1 : 1 < ∏ p ∈ D, abundancy (p ^ N.factorization p) := by
    obtain ⟨p0, hp0P, hp0E⟩ := hex
    have hp0 : p0 ∈ Gc := Finset.mem_filter.mpr ⟨hp0P, hp0E⟩
    obtain ⟨d, hd⟩ := hcover p0 hp0
    have hdD : d ∈ D := Finset.mem_filter.mpr ⟨(hrecv p0 hp0 d hd).1, p0, hp0, hd⟩
    have hdP := (hrecv p0 hp0 d hd).2.1
    have hdN : d ∈ P := hExP (hDE hdD)
    have hfd := one_add_inv_le_abundancy_prime_pow hdP
      (ThreeGap.one_le_fac h hdP (Nat.dvd_of_mem_primeFactors hdN))
    have hdi : (0 : ℚ) < (d : ℚ)⁻¹ := by
      have : (0 : ℚ) < d := by exact_mod_cast hdP.pos
      positivity
    have hme := Finset.mul_prod_erase D (fun p => abundancy (p ^ N.factorization p)) hdD
    beta_reduce at hme
    rw [← hme]
    have hrest : 1 ≤ ∏ p ∈ D.erase d, abundancy (p ^ N.factorization p) :=
      Finset.one_le_prod₀ fun p hp => hf1 p (hExP (hDE (Finset.mem_of_mem_erase hp)))
    nlinarith [mul_le_mul_of_nonneg_left hrest
      (show (0 : ℚ) ≤ abundancy (d ^ N.factorization d) by linarith)]
  have hTD : 1 < (∏ p ∈ Gt, abundancy (p ^ N.factorization p)) *
      (∏ p ∈ D, abundancy (p ^ N.factorization p)) := by
    nlinarith [mul_le_mul_of_nonneg_right nT
      (show (0 : ℚ) ≤ ∏ p ∈ D, abundancy (p ^ N.factorization p) by linarith)]
  have hTDY : (∏ p ∈ Gt, abundancy (p ^ N.factorization p)) *
      (∏ p ∈ D, abundancy (p ^ N.factorization p)) ≤
      1 / (1 - ((S : ℚ) / ((M : ℚ) - 1) + (S : ℚ) / (2 * l))) := by
    rw [Finset.prod_union hdisjT] at hprodU
    refine le_trans ?_ hprodU
    exact mul_le_mul hTf hDf
      (Finset.prod_nonneg fun p hp => zero_le_one.trans (hf1 p (hExP (hDE hp))))
      (prod_ab_nonneg fun p hp => hP2 p (hGm p (hGtG hp)).1)
  -- the kept part is below `2`, hence below `2 - ε`
  have hK2 : ∏ p ∈ S0 ∪ D', abundancy (p ^ N.factorization p) < 2 := by
    by_contra hK
    push Not at hK
    have := mul_lt_mul_of_pos_left hTD (show 0 < ∏ p ∈ S0 ∪ D',
      abundancy (p ^ N.factorization p) by linarith)
    linarith
  obtain ⟨q, hq, -, hq4, he4, hev⟩ := exists_special_prime h
  have hrw : ∏ p ∈ S0 ∪ D', abundancy (p ^ N.factorization p) =
      ∏ p ∈ S0 ∪ D', ((σ 1 (p ^ N.factorization p) : ℚ) / ((p : ℚ) ^ N.factorization p)) :=
    Finset.prod_congr rfl fun p _ => by rw [abundancy, Nat.cast_pow]
  have hKg : ∏ p ∈ S0 ∪ D', abundancy (p ^ N.factorization p) < 2 - ε := by
    rw [hrw] at hK2 ⊢
    refine hgapC (S0 ∪ D') (fun p => N.factorization p) q hU
      (fun c hc => ⟨Nat.prime_of_mem_primeFactors (hUP hc), by
        have := (hP3 c (hUP hc)).1
        omega⟩)
      (fun c hc hcq => hev c (Nat.prime_of_mem_primeFactors (hUP hc)) hcq)
      (fun _ => ⟨hq4, he4⟩) hK2
  -- the contradiction
  have hY : (0 : ℚ) < 1 / (1 - ((S : ℚ) / ((M : ℚ) - 1) + (S : ℚ) / (2 * l))) :=
    one_div_pos.mpr (by linarith)
  have hYb : (2 - ε) * (1 / (1 - ((S : ℚ) / ((M : ℚ) - 1) + (S : ℚ) / (2 * l)))) ≤ 2 := by
    rw [mul_one_div, div_le_iff₀ (by linarith)]
    linarith
  have c1 := mul_le_mul_of_nonneg_left hTDY nK
  have c2 := mul_lt_mul_of_pos_right hKg hY
  linarith

end ExcS

/-- Let `s` be a natural number. If the gap statement `GeneralGapStatement s` holds for every
`s`, then there is a bound `L` such that every odd perfect number `N`, every prime `l ≥ L` and
every set `E` of at most `s` natural numbers with a prime factor of `N` outside `E` and with
`l ∣ e_p + 1` for every prime factor `p ∉ E` of `N` satisfy `l ∣ N`. Restricted result. The
bound `L` is not explicit: the proof gives no value for it. For two and three exceptions the
landed modules give `l ≥ 23` and `l ≥ 359`. Published method, see header; novelty not
verified. The odd perfect number conjecture remains open. -/
theorem exists_index_bound_of_exceptions_of (hgap : ∀ s, GeneralGapStatement s) (s : ℕ) :
    ∃ L : ℕ, ∀ {N l : ℕ}, OddPerfect N → l.Prime → L ≤ l →
      ∀ E : Finset ℕ, E.card ≤ s → (∃ p ∈ N.primeFactors, p ∉ E) →
        (∀ p ∈ N.primeFactors, p ∉ E → l ∣ N.factorization p + 1) → l ∣ N := by
  obtain ⟨ε₀, hε₀, hg⟩ := hgap (s + 1)
  have hε : 0 < min ε₀ 1 := lt_min hε₀ one_pos
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * ((s + 1 : ℕ) : ℚ) / min ε₀ 1)
  rw [div_lt_iff₀ hε] at hn
  refine ⟨4 * (s + 1) * (s + 1) * (n + 2) + n + 3, ?_⟩
  intro N l h hl hL E hE hex hcomp
  exact ExcS.core hε (min_le_right _ _) (by omega) hn
    (fun C e q h1 h2 h3 h4 h5 => (hg C e q h1 h2 h3 h4 h5).trans_le
      (sub_le_sub_left (min_le_left _ _) 2)) h hl hL (by omega) hex hcomp

end OddPerfect

#print axioms OddPerfect.ExcS.keyE
#print axioms OddPerfect.ExcS.count_gtS
#print axioms OddPerfect.ExcS.core
#print axioms OddPerfect.exists_index_bound_of_exceptions_of
