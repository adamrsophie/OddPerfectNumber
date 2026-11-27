import OddPerfect.ThreeComponentGap
import OddPerfect.TwoExceptionsUniform

/-!
# Three exceptions at every prime `l ≥ 359`

Let `l ≥ 359` be a prime, write `R(x) = ∑ i < l, x ^ i`, and let `a`, `b` and `c` be arbitrary
natural numbers. If every prime factor `p` of an odd perfect number `N` other than `a`, `b` and
`c` has `l ∣ e_p + 1`, then `l ∣ N`. The argument needs no finite data.

Assume `l ∤ N` and put `A = (l - 1) / 3`, `B = 3 ^ 16 = 43046721`. For a compatible prime
factor `p` (one other than `a`, `b`, `c`) every prime factor of `R(p)` is a prime factor of `N`
in `{a, b, c}` and `1` modulo `l`. Since `R(p) > p ^ (3 A)` and `R(p)` has at most three prime
factors, some receiver `d` has `d ^ v_d(R(p)) > p ^ A`. Two compatible primes `p < p'` sharing
such a receiver satisfy `p ^ 16 < p'` (`pow_lt_of_common_receiver_power`). So the compatible
primes up to `B` number at most `r`, the number of receivers, and every interval
`(B ^ j, B ^ (j + 1)]` holds at most `r ≤ 3` of them. The compatible primes up to `B` together
with the exceptions that are not receivers form at most three prime factors, whose component
abundancies multiply to at most `52514 / 26325` (`abundancy_three_components_le`). The
receivers are prime factors of `N` that are `1` modulo `2 l`. Hence
`2 ≤ (52514 / 26325) (719 / 718) (1437 / 1436) (2155 / 2154) (43046720 / 43046717) < 2`,
a contradiction.

Restricted result; published method, see below; novelty not verified. Four exceptions are
not covered, and primes `l` below `359` are not covered by this module. The odd perfect number
conjecture remains open.

Method. The count of monomials `p ^ i * p' ^ j` below a prime power modulus, all of them roots
of `X ^ l = 1`, is Lemma 3.1 of T. Yamada, On finiteness of odd superperfect numbers
(arXiv 0803.0437v7). A gap of this kind between two primes with a common dominant receiver is
Lemma 3.2 there (with other constants), and the split of the sources into classes by dominant
receiver is the proof of Lemma 3.3 there. That paper does not state the theorems of this
module; no other source was checked.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect.ExcUniform3

open OddPerfect.TwoExcGen OddPerfect.ExcUniform

/-- Every prime factor of the row of a compatible prime is a prime factor of `N`, one of the
three exceptions, and `1` modulo `l`. -/
theorem key3 {l N a b c : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (h : OddPerfect N) (hlN : ¬ l ∣ N)
    (hcomp : ∀ p ∈ N.primeFactors, p ≠ a → p ≠ b → p ≠ c → l ∣ N.factorization p + 1)
    {p : ℕ} (hp : p ∈ N.primeFactors) (hpa : p ≠ a) (hpb : p ≠ b) (hpc : p ≠ c) {s : ℕ}
    (hs : s.Prime) (hsR : s ∣ ∑ i ∈ Finset.range l, p ^ i) :
    s ∈ N.primeFactors ∧ (s = a ∨ s = b ∨ s = c) ∧ s % l = 1 := by
  have hpP := Nat.prime_of_mem_primeFactors hp
  have hN := h.ne_zero
  have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl.one_lt.le
  have hdv : σ 1 (p ^ (l - 1)) ∣ σ 1 (p ^ N.factorization p) :=
    OPNExample.sigma_prime_pow_dvd (a := l - 1) hpP
      (by rw [hl1]; exact hcomp p hp hpa hpb hpc)
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
  by_contra hne
  have h1 : s ≠ a := fun e => hne (Or.inl e)
  have h2 : s ≠ b := fun e => hne (Or.inr (Or.inl e))
  have h3 : s ≠ c := fun e => hne (Or.inr (Or.inr e))
  have hd2 : σ 1 (s ^ (l - 1)) ∣ σ 1 (s ^ N.factorization s) :=
    OPNExample.sigma_prime_pow_dvd (a := l - 1) hs
      (by rw [hl1]; exact hcomp s hsP h1 h2 h3)
  have hls : l ∣ σ 1 (s ^ (l - 1)) := by
    rw [← R_eq_sigma hl.one_lt.le hs]
    exact dvd_R_of_mod hl.two_le hsl
  exact hlN (OPNStarter.force_prime h.perfect hs rfl hl hl2 (hls.trans hd2))

/-- The pair count with `G = 16` and `A = (l - 1) / 3` exceeds `l` for `l ≥ 359`. -/
theorem count_gt3 {l : ℕ} (hl : 359 ≤ l) :
    l < ∑ j ∈ Finset.range ((l - 1) / 3 / 16 + 1), ((l - 1) / 3 - 16 * j + 1) := by
  have hsub : Finset.range 4 ⊆ Finset.range ((l - 1) / 3 / 16 + 1) :=
    Finset.range_subset_range.mpr (by omega)
  have e := Finset.sum_le_sum_of_subset (f := fun j => (l - 1) / 3 - 16 * j + 1) hsub
  have e4 : ∑ j ∈ Finset.range 4, ((l - 1) / 3 - 16 * j + 1) =
      ((l - 1) / 3 + 1) + ((l - 1) / 3 - 16 + 1) + ((l - 1) / 3 - 32 + 1) +
        ((l - 1) / 3 - 48 + 1) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    omega
  omega

/-- Numbers at least `m` that are pairwise congruent to `1` modulo `L`: the product of
`p / (p - 1)` over at most `n` of them is at most `∏ k < n, ab (m + L k)`. -/
theorem prod_ab_le_progression {L : ℕ} (hL : 0 < L) : ∀ (n m : ℕ) (s : Finset ℕ), 2 ≤ m →
    s.card ≤ n → (∀ d ∈ s, m ≤ d ∧ L ∣ d - 1) →
    ∏ p ∈ s, ab p ≤ ∏ k ∈ Finset.range n, ab (m + L * k) := by
  intro n
  induction n with
  | zero =>
    intro m s _ hc _
    rw [Finset.card_eq_zero.mp (show s.card = 0 by omega)]
    simp
  | succ n ih =>
    intro m s hm hc hs
    have hone : ∀ k, 1 ≤ ab (m + L * k) := fun k => one_le_ab (by omega)
    rw [Finset.prod_range_succ', Nat.mul_zero, Nat.add_zero]
    have hP1 : 1 ≤ ∏ k ∈ Finset.range n, ab (m + L * (k + 1)) :=
      Finset.one_le_prod₀ fun k _ => hone (k + 1)
    rcases s.eq_empty_or_nonempty with hs0 | hne
    · rw [hs0, Finset.prod_empty]
      have := one_le_ab hm
      nlinarith
    · have hx := Finset.min'_mem s hne
      rw [← Finset.mul_prod_erase s ab hx]
      have hxs := hs _ hx
      have hrest : ∀ d ∈ s.erase (s.min' hne), m + L ≤ d ∧ L ∣ d - 1 := by
        intro d hd
        obtain ⟨hdx, hds⟩ := Finset.mem_erase.mp hd
        have hle := Finset.min'_le s d hds
        have hlt : s.min' hne < d := lt_of_le_of_ne hle (Ne.symm hdx)
        have hdd := hs d hds
        have h2 : L ∣ (d - 1) - (s.min' hne - 1) := Nat.dvd_sub hdd.2 hxs.2
        have h3 := Nat.le_of_dvd (by omega) h2
        exact ⟨by omega, hdd.2⟩
      have hcard : (s.erase (s.min' hne)).card ≤ n := by
        rw [Finset.card_erase_of_mem hx]
        omega
      have hih := ih (m + L) (s.erase (s.min' hne)) (by omega) hcard hrest
      have heq : ∏ k ∈ Finset.range n, ab (m + L + L * k) =
          ∏ k ∈ Finset.range n, ab (m + L * (k + 1)) :=
        Finset.prod_congr rfl fun k _ => by congr 1; ring
      rw [heq] at hih
      have hab := ab_anti hm hxs.1
      have hn0 : 0 ≤ ∏ p ∈ s.erase (s.min' hne), ab p :=
        prod_ab_nonneg fun p hp => by have := (hrest p hp).1; omega
      rw [mul_comm]
      exact mul_le_mul hih hab (ab_nonneg (by omega)) (by linarith)

/-- At most three distinct numbers `1` modulo `2 l`, `l ≥ 359`, contribute at most
`(719 / 718) (1437 / 1436) (2155 / 2154)`. -/
theorem prod_ab_le_rec3 {l : ℕ} (hl : 359 ≤ l) {s : Finset ℕ}
    (hs : ∀ d ∈ s, 2 ≤ d ∧ 2 * l ∣ d - 1) (hk : s.card ≤ 3) :
    ∏ p ∈ s, ab p ≤ 719 / 718 * (1437 / 1436) * (2155 / 2154) := by
  have hs' : ∀ d ∈ s, 2 * l + 1 ≤ d ∧ 2 * l ∣ d - 1 := fun d hd => by
    have := Nat.le_of_dvd (by have := (hs d hd).1; omega) (hs d hd).2
    exact ⟨by omega, (hs d hd).2⟩
  have h := prod_ab_le_progression (L := 2 * l) (by omega) 3 (2 * l + 1) s (by omega) hk hs'
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul] at h
  have f0 := ab_anti (a := 719) (by norm_num) (show 719 ≤ 2 * l + 1 + 2 * l * 0 by omega)
  have f1 := ab_anti (a := 1437) (by norm_num) (show 1437 ≤ 2 * l + 1 + 2 * l * 1 by omega)
  have f2 := ab_anti (a := 2155) (by norm_num) (show 2155 ≤ 2 * l + 1 + 2 * l * 2 by omega)
  have a0 : ab 719 = 719 / 718 := by norm_num [ab]
  have a1 : ab 1437 = 1437 / 1436 := by norm_num [ab]
  have a2 : ab 2155 = 2155 / 2154 := by norm_num [ab]
  rw [a0] at f0
  rw [a1] at f1
  rw [a2] at f2
  have n0 := ab_nonneg (p := 2 * l + 1 + 2 * l * 0) (by omega)
  have n1 := ab_nonneg (p := 2 * l + 1 + 2 * l * 1) (by omega)
  have n2 := ab_nonneg (p := 2 * l + 1 + 2 * l * 2) (by omega)
  exact h.trans (mul_le_mul (mul_le_mul f0 f1 n1 (by norm_num)) f2 n2 (by norm_num))

end OddPerfect.ExcUniform3

namespace OddPerfect

open OddPerfect.TwoExcGen OddPerfect.ExcUniform OddPerfect.ExcUniform3

/-- Let `l ≥ 359` be a prime and let `a`, `b` and `c` be arbitrary natural numbers. An odd
perfect number all of whose prime factors other than `a`, `b` and `c` have an index divisible
by `l` is divisible by `l`. Restricted result; four exceptions are not covered; primes `l`
below `359` are not covered by this module; published method, see header; novelty not
verified. The odd perfect number conjecture remains open. -/
theorem dvd_of_three_exceptions_uniform {N l a b c : ℕ} (h : OddPerfect N) (hl : l.Prime)
    (hl359 : 359 ≤ l)
    (hcomp : ∀ p ∈ N.primeFactors, p ≠ a → p ≠ b → p ≠ c → l ∣ N.factorization p + 1) :
    l ∣ N := by
  classical
  by_contra hlN
  have hl2 : l ≠ 2 := by omega
  have hcnt16 := count_gt3 hl359
  set A := (l - 1) / 3 with hAdef
  have hA : A * 3 ≤ l - 1 := by omega
  set P := N.primeFactors with hP
  have hP2 : ∀ p ∈ P, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hP3 : ∀ p ∈ P, 3 ≤ p ∧ p % 2 = 1 := fun p hp => by
    have h1 := odd_of_mem h hp
    have h2 := hP2 p hp
    exact ⟨by omega, h1⟩
  set G := P.filter (fun p => p ≠ a ∧ p ≠ b ∧ p ≠ c) with hG
  set E := P.filter (fun p => ¬ (p ≠ a ∧ p ≠ b ∧ p ≠ c)) with hE
  have hGm : ∀ p ∈ G, p ∈ P ∧ p ≠ a ∧ p ≠ b ∧ p ≠ c := fun p hp => Finset.mem_filter.mp hp
  have hEP : E ⊆ P := Finset.filter_subset _ _
  -- a receiver with a large power is a prime factor of `N`, an exception, `1` modulo `l`
  have hrecv : ∀ p ∈ G, ∀ d, p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d →
      d ∈ E ∧ d.Prime ∧ d % l = 1 := by
    intro p hp d hd
    obtain ⟨hpP, hpa, hpb, hpc⟩ := hGm p hp
    have hv : (∑ i ∈ Finset.range l, p ^ i).factorization d ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hd
      exact absurd hd (not_lt.mpr (Nat.one_le_pow _ _ (by have := hP2 p hpP; omega)))
    have hmem : d ∈ (∑ i ∈ Finset.range l, p ^ i).primeFactors := by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.mpr hv
    have hdP : d.Prime := Nat.prime_of_mem_primeFactors hmem
    have hdR : d ∣ ∑ i ∈ Finset.range l, p ^ i := Nat.dvd_of_mem_primeFactors hmem
    obtain ⟨hdN, hdabc, hdl⟩ := key3 hl hl2 h hlN hcomp hpP hpa hpb hpc hdP hdR
    refine ⟨Finset.mem_filter.mpr ⟨hdN, fun hc => ?_⟩, hdP, hdl⟩
    rcases hdabc with e | e | e
    · exact hc.1 e
    · exact hc.2.1 e
    · exact hc.2.2 e
  -- every compatible prime has a receiver with a large power
  have hcover : ∀ p ∈ G, ∃ d, p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d := by
    intro p hp
    obtain ⟨hpP, hpa, hpb, hpc⟩ := hGm p hp
    have hsub : (∑ i ∈ Finset.range l, p ^ i).primeFactors ⊆ {a, b, c} := by
      intro x hx
      have := (key3 hl hl2 h hlN hcomp hpP hpa hpb hpc (Nat.prime_of_mem_primeFactors hx)
        (Nat.dvd_of_mem_primeFactors hx)).2.1
      rcases this with e | e | e <;> simp [e]
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
    have e2 : (p ^ A) ^ (∑ i ∈ Finset.range l, p ^ i).primeFactors.card ≤ (p ^ A) ^ 3 :=
      Nat.pow_le_pow_right hp1 ((Finset.card_le_card hsub).trans Finset.card_le_three)
    have e3 : (p ^ A) ^ 3 ≤ p ^ (l - 1) := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by have := hP2 p hpP; omega) hA
    omega
  -- the receivers
  set D := E.filter (fun d => ∃ p ∈ G,
    p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d) with hD
  set D' := E.filter (fun d => ¬ ∃ p ∈ G,
    p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d) with hD'
  have hDE : D ⊆ E := Finset.filter_subset _ _
  have hEcard : E.card ≤ 3 := (Finset.card_le_card (t := {a, b, c}) (fun x hx => by
      rw [Finset.mem_filter] at hx
      have : x = a ∨ x = b ∨ x = c := by tauto
      rcases this with e | e | e <;> simp [e])).trans Finset.card_le_three
  have hDcard : D.card ≤ 3 := (Finset.card_le_card hDE).trans hEcard
  have hDprop : ∀ d ∈ D, 2 ≤ d ∧ 2 * l ∣ d - 1 ∧ d.Prime ∧ d ≠ l := by
    intro d hd
    obtain ⟨-, p, hp, hpd⟩ := Finset.mem_filter.mp hd
    obtain ⟨-, hdP, hdl⟩ := hrecv p hp d hpd
    have h1 : l ∣ d - 1 := by
      have := Nat.dvd_sub_mod (n := l) d
      rwa [hdl] at this
    have hdodd := (hP3 d (hEP (hDE hd))).2
    have h2 : 2 ∣ d - 1 := Nat.dvd_of_mod_eq_zero (by omega)
    refine ⟨hdP.two_le, ?_, hdP, ?_⟩
    · rw [mul_comm]
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hl Nat.prime_two).mpr hl2)
        h1 h2
    · intro hdl'
      rw [hdl', Nat.mod_self] at hdl
      omega
  -- two compatible primes sharing a receiver are far apart
  have hgap : ∀ d ∈ D, ∀ p ∈ G, ∀ p' ∈ G, p < p' →
      p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d →
      p' ^ A < d ^ (∑ i ∈ Finset.range l, p' ^ i).factorization d → p ^ 16 < p' := by
    intro d hd p hp p' hp' hpp' h1 h2
    obtain ⟨-, -, hdP, hdl⟩ := hDprop d hd
    have hpP := Nat.prime_of_mem_primeFactors (hGm p hp).1
    have hp'P := Nat.prime_of_mem_primeFactors (hGm p' hp').1
    exact pow_lt_of_common_receiver_power hl hdP hdl hpP hp'P hpp' (Nat.ordProj_dvd _ d)
      (Nat.ordProj_dvd _ d) h1 (lt_of_le_of_lt (Nat.pow_le_pow_left hpp'.le A) h2) hcnt16
  -- a set of compatible primes without far apart pairs has at most `D.card` elements
  have hcnt : ∀ X ⊆ G, (∀ p ∈ X, ∀ p' ∈ X, p < p' → p' ≤ p ^ 16) → X.card ≤ D.card := by
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
  -- the compatible primes up to `B` and above `B`
  set S0 := G.filter (fun p => p ≤ 43046721) with hS0
  set Gt := G.filter (fun p => ¬ p ≤ 43046721) with hGt
  have hS0G : S0 ⊆ G := Finset.filter_subset _ _
  have hGtG : Gt ⊆ G := Finset.filter_subset _ _
  have hS0c : S0.card ≤ D.card := hcnt S0 hS0G (fun p hp p' hp' _ => by
    have h1 := (hP3 p (hGm p (hS0G hp)).1).1
    have h2 := (Finset.mem_filter.mp hp').2
    have : 43046721 ≤ p ^ 16 := le_trans (by norm_num) (Nat.pow_le_pow_left h1 16)
    omega)
  have hGtbig : ∀ p ∈ Gt, 43046721 < p := fun p hp => by
    have := (Finset.mem_filter.mp hp).2
    omega
  have hblock : ∀ j, 1 ≤ j →
      (Gt.filter (fun p => 43046721 ^ j < p ∧ p ≤ 43046721 ^ (j + 1))).card ≤ 3 := by
    intro j hj
    refine le_trans (hcnt _ ((Finset.filter_subset _ _).trans hGtG) ?_) hDcard
    intro p hp p' hp' _
    have h1 := (Finset.mem_filter.mp hp).2.1
    have h2 := (Finset.mem_filter.mp hp').2.2
    have e1 : (43046721 ^ j) ^ 16 < p ^ 16 := Nat.pow_lt_pow_left h1 (by norm_num)
    have e2 : 43046721 ^ (j + 1) ≤ (43046721 ^ j) ^ 16 := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hsum := sum_inv_pred_le_of_interval_card (B := 43046721) (c := 3) (by norm_num) hGtbig
    hblock
  have hGtb := prod_ab_le_of_sum (fun p hp => by have := hGtbig p hp; omega) hsum
    (by norm_num)
  -- the kept part: compatible primes up to `B` and exceptions that are not receivers
  have hDD' : D.card + D'.card = E.card := Finset.card_filter_add_card_filter_not _
  have hdisj : Disjoint S0 D' := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have h1 := (hGm x (hS0G hx)).2
    have h2 := (Finset.mem_filter.mp (Finset.filter_subset _ _ hx')).2
    exact h2 h1
  have hU : (S0 ∪ D').card ≤ 3 := by
    have := Finset.card_union_le S0 D'
    omega
  have hUP : S0 ∪ D' ⊆ P := by
    intro p hp
    rcases Finset.mem_union.mp hp with h1 | h1
    · exact (hGm p (hS0G h1)).1
    · exact hEP (Finset.filter_subset _ _ h1)
  have hKept : ∏ p ∈ S0 ∪ D', abundancy (p ^ N.factorization p) ≤ 52514 / 26325 := by
    have hk := abundancy_three_components_le h hUP hU
    have hrw : ∏ p ∈ S0 ∪ D', abundancy (p ^ N.factorization p) =
        ∏ p ∈ S0 ∪ D', ((σ 1 (p ^ N.factorization p) : ℚ) / ((p : ℚ) ^ N.factorization p)) :=
      Finset.prod_congr rfl fun p _ => by rw [abundancy, Nat.cast_pow]
    rw [hrw]
    exact hk
  -- the receivers
  have hDb : ∏ p ∈ D, ab p ≤ 719 / 718 * (1437 / 1436) * (2155 / 2154) :=
    prod_ab_le_rec3 hl359 (fun d hd => ⟨(hDprop d hd).1, (hDprop d hd).2.1⟩) hDcard
  -- components against `p / (p - 1)`
  have hf1 : ∀ p ∈ P, 1 ≤ abundancy (p ^ N.factorization p) := fun p hp =>
    ThreeGap.one_le_abundancy_pow (Nat.prime_of_mem_primeFactors hp) _
  have hfab : ∀ p ∈ P, abundancy (p ^ N.factorization p) ≤ ab p := fun p hp =>
    (abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors hp) _).le
  have hTf : ∏ p ∈ Gt, abundancy (p ^ N.factorization p) ≤ ∏ p ∈ Gt, ab p :=
    Finset.prod_le_prod₀ (fun p hp => zero_le_one.trans (hf1 p (hGm p (hGtG hp)).1))
      fun p hp => hfab p (hGm p (hGtG hp)).1
  have hDf : ∏ p ∈ D, abundancy (p ^ N.factorization p) ≤ ∏ p ∈ D, ab p :=
    Finset.prod_le_prod₀ (fun p hp => zero_le_one.trans (hf1 p (hEP (hDE hp))))
      fun p hp => hfab p (hEP (hDE hp))
  -- assemble
  have hprod : ∏ p ∈ P, abundancy (p ^ N.factorization p) = 2 := by
    rw [hP, ← abundancy_eq_prod_primeFactors h.ne_zero]
    exact (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
  have e1 : (∏ p ∈ G, abundancy (p ^ N.factorization p)) *
      (∏ p ∈ E, abundancy (p ^ N.factorization p)) =
      ∏ p ∈ P, abundancy (p ^ N.factorization p) :=
    Finset.prod_filter_mul_prod_filter_not P _ _
  have e2 : (∏ p ∈ S0, abundancy (p ^ N.factorization p)) *
      (∏ p ∈ Gt, abundancy (p ^ N.factorization p)) =
      ∏ p ∈ G, abundancy (p ^ N.factorization p) :=
    Finset.prod_filter_mul_prod_filter_not G _ _
  have e3 : (∏ p ∈ D, abundancy (p ^ N.factorization p)) *
      (∏ p ∈ D', abundancy (p ^ N.factorization p)) =
      ∏ p ∈ E, abundancy (p ^ N.factorization p) :=
    Finset.prod_filter_mul_prod_filter_not E _ _
  have e4 : ∏ p ∈ S0 ∪ D', abundancy (p ^ N.factorization p) =
      (∏ p ∈ S0, abundancy (p ^ N.factorization p)) *
        (∏ p ∈ D', abundancy (p ^ N.factorization p)) :=
    Finset.prod_union hdisj
  have hsplit : (2 : ℚ) = (∏ p ∈ S0 ∪ D', abundancy (p ^ N.factorization p)) *
      (∏ p ∈ Gt, abundancy (p ^ N.factorization p)) *
      (∏ p ∈ D, abundancy (p ^ N.factorization p)) := by
    rw [← hprod, ← e1, ← e2, ← e3, e4]
    ring
  have n1 : 0 ≤ ∏ p ∈ Gt, abundancy (p ^ N.factorization p) :=
    Finset.prod_nonneg fun p hp => zero_le_one.trans (hf1 p (hGm p (hGtG hp)).1)
  have n2 : 0 ≤ ∏ p ∈ D, abundancy (p ^ N.factorization p) :=
    Finset.prod_nonneg fun p hp => zero_le_one.trans (hf1 p (hEP (hDE hp)))
  have b1 := mul_le_mul hKept (hTf.trans hGtb) n1 (by norm_num)
  have b2 := mul_le_mul b1 (hDf.trans hDb) n2 (by norm_num)
  have hnum : (52514 / 26325 : ℚ) *
      (1 / (1 - ((3 : ℕ) : ℚ) / (((43046721 : ℕ) : ℚ) - 1))) *
      (719 / 718 * (1437 / 1436) * (2155 / 2154)) < 2 := by norm_num
  linarith

end OddPerfect

#print axioms OddPerfect.ExcUniform3.key3
#print axioms OddPerfect.ExcUniform3.prod_ab_le_progression
#print axioms OddPerfect.ExcUniform3.prod_ab_le_rec3
#print axioms OddPerfect.dvd_of_three_exceptions_uniform
