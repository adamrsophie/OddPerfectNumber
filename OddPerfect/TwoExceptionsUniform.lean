import OddPerfect.TwoExceptionsGeneralCore
import OddPerfect.PrimeMonomialCount

/-!
# Two exceptions at every prime `l ≥ 23`

Let `l ≥ 23` be a prime, write `R(x) = ∑ i < l, x ^ i`, and let `a` and `b` be arbitrary natural
numbers. If every prime factor `p` of an odd perfect number `N` other than `a` and `b` has
`l ∣ e_p + 1`, then `l ∣ N`. The argument needs no finite data.

Assume `l ∤ N` and put `A = (l - 1) / 2`. For a compatible prime factor `p` (one other than `a`
and `b`) every prime factor of `R(p)` is a prime factor of `N` equal to `a` or `b` and `1`
modulo `l`. Since `R(p) > p ^ (2 A)`, some receiver `d` has `d ^ v_d(R(p)) > p ^ A`. Two
compatible primes `p < p'` sharing such a receiver satisfy `p ^ 4 < p'`
(`pow_lt_of_common_receiver_power`). So the compatible primes up to `81` number at most `r`,
the number of receivers, and every interval `(81 ^ j, 81 ^ (j + 1)]` holds at most `r ≤ 2`
of them. The receivers are prime factors of `N` that are `1` modulo `2 l`. Hence
`∏ p / (p - 1) ≤ (15 / 8) (47 / 46) (93 / 92) (40 / 39) < 2`, a contradiction.

Restricted result; no published source was checked; novelty not verified. Three exceptions
(see `ThreeExceptionsUniform` for `l ≥ 359`) and primes `l` below `23` are not covered by this
module. The odd perfect number conjecture remains open.
-/

namespace OddPerfect.ExcUniform

open OddPerfect.TwoExcGen

/-- The row exceeds its leading term. -/
theorem pow_lt_R {l p : ℕ} (hl : 2 ≤ l) (hp : 1 ≤ p) :
    p ^ (l - 1) < ∑ i ∈ Finset.range l, p ^ i := by
  have hl' : l = (l - 1) + 1 := by omega
  have hsplit := Finset.sum_range_succ (fun i => p ^ i) (l - 1)
  rw [← hl'] at hsplit
  rw [hsplit]
  have : 0 < ∑ i ∈ Finset.range (l - 1), p ^ i :=
    Finset.sum_pos (fun i _ => pow_pos (by omega) i) ⟨0, Finset.mem_range.mpr (by omega)⟩
  omega

/-- The pair count with `G = 4` and `A = (l - 1) / 2` exceeds `l` for `l ≥ 23`. -/
theorem count_gt {l : ℕ} (hl23 : 23 ≤ l) (hodd : l % 2 = 1) :
    l < ∑ j ∈ Finset.range ((l - 1) / 2 / 4 + 1), ((l - 1) / 2 - 4 * j + 1) := by
  have hsub : Finset.range 3 ⊆ Finset.range ((l - 1) / 2 / 4 + 1) :=
    Finset.range_subset_range.mpr (by omega)
  have e := Finset.sum_le_sum_of_subset (f := fun j => (l - 1) / 2 - 4 * j + 1) hsub
  have e3 : ∑ j ∈ Finset.range 3, ((l - 1) / 2 - 4 * j + 1) =
      ((l - 1) / 2 + 1) + ((l - 1) / 2 - 4 + 1) + ((l - 1) / 2 - 8 + 1) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    omega
  omega

/-- At most two distinct numbers `1` modulo `2 l`, `l ≥ 23`, contribute at most
`(47 / 46) (93 / 92)`. -/
theorem prod_ab_le_rec {l : ℕ} (hl23 : 23 ≤ l) {s : Finset ℕ}
    (hs : ∀ d ∈ s, 2 ≤ d ∧ 2 * l ∣ d - 1) (hk : s.card ≤ 2) :
    ∏ p ∈ s, ab p ≤ 47 / 46 * (93 / 92) := by
  have ab47 : ab 47 = 47 / 46 := by norm_num [ab]
  have ab93 : ab 93 = 93 / 92 := by norm_num [ab]
  have lb : ∀ d ∈ s, 47 ≤ d := fun d hd => by
    obtain ⟨h2, hdv⟩ := hs d hd
    have := Nat.le_of_dvd (by omega) hdv
    omega
  rcases Nat.lt_or_ge s.card 2 with h | h
  · have := prod_ab_le_pow (a := 47) (k := 1) (by norm_num) lb (by omega)
    rw [ab47, pow_one] at this
    linarith
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp (le_antisymm hk h)
    rw [Finset.prod_pair hxy]
    have key2 : ∀ u v : ℕ, 2 ≤ u → 2 * l ∣ u - 1 → 2 * l ∣ v - 1 → u < v →
        ab u * ab v ≤ 47 / 46 * (93 / 92) := by
      intro u v hu hud hvd huv
      have h1 := Nat.le_of_dvd (by omega) hud
      have h2 : 2 * l ∣ (v - 1) - (u - 1) := Nat.dvd_sub hvd hud
      have h3 := Nat.le_of_dvd (by omega) h2
      have f1 := ab_anti (a := 47) (by norm_num) (show 47 ≤ u by omega)
      have f2 := ab_anti (a := 93) (by norm_num) (show 93 ≤ v by omega)
      rw [ab47] at f1
      rw [ab93] at f2
      exact mul_le_mul f1 f2 (ab_nonneg (by omega)) (by norm_num)
    have hx := hs x (by simp)
    have hy := hs y (by simp)
    rcases lt_or_gt_of_ne hxy with hlt | hlt
    · exact key2 x y hx.1 hx.2 hy.2 hlt
    · rw [mul_comm]
      exact key2 y x hy.1 hy.2 hx.2 hlt

end OddPerfect.ExcUniform

namespace OddPerfect

open OddPerfect.TwoExcGen OddPerfect.ExcUniform

/-- Let `l ≥ 23` be a prime and let `a` and `b` be arbitrary natural numbers. An odd perfect
number all of whose prime factors other than `a` and `b` have an index divisible by `l` is
divisible by `l`. Restricted result; three exceptions and primes `l` below `23` are not
covered by this module; no published source was checked; novelty not verified. The odd
perfect number conjecture remains open. -/
theorem dvd_of_two_exceptions_uniform {N l a b : ℕ} (h : OddPerfect N) (hl : l.Prime)
    (hl23 : 23 ≤ l)
    (hcomp : ∀ p ∈ N.primeFactors, p ≠ a → p ≠ b → l ∣ N.factorization p + 1) : l ∣ N := by
  classical
  by_contra hlN
  have hl2 : l ≠ 2 := by omega
  have hlodd : l % 2 = 1 := hl.eq_two_or_odd.resolve_left hl2
  have H : (2 : ℚ) < ∏ p ∈ N.primeFactors, ab p := two_lt_prod_primeFactors_div h
  have hcnt4 := count_gt hl23 hlodd
  set A := (l - 1) / 2 with hAdef
  have hA : l - 1 = A + A := by omega
  set P := N.primeFactors with hP
  have hP2 : ∀ p ∈ P, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hP3 : ∀ p ∈ P, 3 ≤ p ∧ p % 2 = 1 := fun p hp => by
    have h1 := odd_of_mem h hp
    have h2 := hP2 p hp
    exact ⟨by omega, h1⟩
  set G := P.filter (fun p => p ≠ a ∧ p ≠ b) with hG
  set E := P.filter (fun p => ¬ (p ≠ a ∧ p ≠ b)) with hE
  have hGm : ∀ p ∈ G, p ∈ P ∧ p ≠ a ∧ p ≠ b := fun p hp => Finset.mem_filter.mp hp
  have hEP : E ⊆ P := Finset.filter_subset _ _
  -- a receiver with a large power is a prime factor of `N`, an exception, `1` modulo `l`
  have hrecv : ∀ p ∈ G, ∀ d, p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d →
      d ∈ E ∧ d.Prime ∧ d % l = 1 := by
    intro p hp d hd
    obtain ⟨hpP, hpa, hpb⟩ := hGm p hp
    have hv : (∑ i ∈ Finset.range l, p ^ i).factorization d ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hd
      exact absurd hd (not_lt.mpr (Nat.one_le_pow _ _ (by have := hP2 p hpP; omega)))
    have hmem : d ∈ (∑ i ∈ Finset.range l, p ^ i).primeFactors := by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.mpr hv
    have hdP : d.Prime := Nat.prime_of_mem_primeFactors hmem
    have hdR : d ∣ ∑ i ∈ Finset.range l, p ^ i := Nat.dvd_of_mem_primeFactors hmem
    obtain ⟨hdN, hdab, hdl⟩ := key hl hl2 h hlN hcomp hpP hpa hpb hdP hdR
    exact ⟨Finset.mem_filter.mpr ⟨hdN, fun hc => hdab.elim hc.1 hc.2⟩, hdP, hdl⟩
  -- every compatible prime has a receiver with a large power
  have hcover : ∀ p ∈ G, ∃ d, p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d := by
    intro p hp
    obtain ⟨hpP, hpa, hpb⟩ := hGm p hp
    have hsub : (∑ i ∈ Finset.range l, p ^ i).primeFactors ⊆ {a, b} := by
      intro x hx
      have := (key hl hl2 h hlN hcomp hpP hpa hpb (Nat.prime_of_mem_primeFactors hx)
        (Nat.dvd_of_mem_primeFactors hx)).2.1
      rcases this with rfl | rfl <;> simp
    have hR0 : (∑ i ∈ Finset.range l, p ^ i) ≠ 0 :=
      (lt_trans zero_lt_one (R_one_lt hl.two_le (hP2 p hpP))).ne'
    have hle := le_mul_of_pf_subset hR0 hsub
    have hlt := pow_lt_R hl.two_le (show 1 ≤ p by have := hP2 p hpP; omega)
    by_contra hno
    push Not at hno
    have e := Nat.mul_le_mul (hno a) (hno b)
    rw [← pow_add, ← hA] at e
    omega
  -- the receivers
  set D := E.filter (fun d => ∃ p ∈ G,
    p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d) with hD
  set D' := E.filter (fun d => ¬ ∃ p ∈ G,
    p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d) with hD'
  have hDE : D ⊆ E := Finset.filter_subset _ _
  have hEcard : E.card ≤ 2 := (Finset.card_le_card (t := {a, b}) (fun x hx => by
      rw [Finset.mem_filter] at hx
      have : x = a ∨ x = b := by tauto
      rcases this with rfl | rfl <;> simp)).trans Finset.card_le_two
  have hDcard : D.card ≤ 2 := (Finset.card_le_card hDE).trans hEcard
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
      p' ^ A < d ^ (∑ i ∈ Finset.range l, p' ^ i).factorization d → p ^ 4 < p' := by
    intro d hd p hp p' hp' hpp' h1 h2
    obtain ⟨-, -, hdP, hdl⟩ := hDprop d hd
    have hpP := Nat.prime_of_mem_primeFactors (hGm p hp).1
    have hp'P := Nat.prime_of_mem_primeFactors (hGm p' hp').1
    exact pow_lt_of_common_receiver_power hl hdP hdl hpP hp'P hpp' (Nat.ordProj_dvd _ d)
      (Nat.ordProj_dvd _ d) h1 (lt_of_le_of_lt (Nat.pow_le_pow_left hpp'.le A) h2) hcnt4
  -- a set of compatible primes without far apart pairs has at most `D.card` elements
  have hcnt : ∀ X ⊆ G, (∀ p ∈ X, ∀ p' ∈ X, p < p' → p' ≤ p ^ 4) → X.card ≤ D.card := by
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
  -- the compatible primes up to `81` and above `81`
  set S0 := G.filter (fun p => p ≤ 81) with hS0
  set Gt := G.filter (fun p => ¬ p ≤ 81) with hGt
  have hS0G : S0 ⊆ G := Finset.filter_subset _ _
  have hGtG : Gt ⊆ G := Finset.filter_subset _ _
  have hS0c : S0.card ≤ D.card := hcnt S0 hS0G (fun p hp p' hp' _ => by
    have h1 := (hP3 p (hGm p (hS0G hp)).1).1
    have h2 := (Finset.mem_filter.mp hp').2
    have : 81 ≤ p ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left h1 4)
    omega)
  have hGtbig : ∀ p ∈ Gt, 81 < p := fun p hp => by
    have := (Finset.mem_filter.mp hp).2
    omega
  have hblock : ∀ j, 1 ≤ j →
      (Gt.filter (fun p => 81 ^ j < p ∧ p ≤ 81 ^ (j + 1))).card ≤ 2 := by
    intro j hj
    refine le_trans (hcnt _ ((Finset.filter_subset _ _).trans hGtG) ?_) hDcard
    intro p hp p' hp' _
    have h1 := (Finset.mem_filter.mp hp).2.1
    have h2 := (Finset.mem_filter.mp hp').2.2
    have e1 : (81 ^ j) ^ 4 < p ^ 4 := Nat.pow_lt_pow_left h1 (by norm_num)
    have e2 : 81 ^ (j + 1) ≤ (81 ^ j) ^ 4 := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hsum := sum_inv_pred_le_of_interval_card (B := 81) (c := 2) (by norm_num) hGtbig hblock
  have hGtb := prod_ab_le_of_sum (fun p hp => by have := hGtbig p hp; omega) hsum
    (by norm_num)
  -- the compatible primes up to `81` and the exceptions that are not receivers
  have hDD' : D.card + D'.card = E.card := Finset.card_filter_add_card_filter_not _
  have hdisj : Disjoint S0 D' := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have h1 := (hGm x (hS0G hx)).2
    have h2 := (Finset.mem_filter.mp (Finset.filter_subset _ _ hx')).2
    exact h2 h1
  have hU : (S0 ∪ D').card ≤ 2 := by
    have := Finset.card_union_le S0 D'
    omega
  have hUP : ∀ p ∈ S0 ∪ D', p ∈ P := by
    intro p hp
    rcases Finset.mem_union.mp hp with h1 | h1
    · exact (hGm p (hS0G h1)).1
    · exact hEP (Finset.filter_subset _ _ h1)
  have hUb : ∏ p ∈ S0 ∪ D', ab p ≤ 15 / 8 := prod_ab_le_pair (fun p hp => hP3 p (hUP p hp)) hU
  -- the receivers
  have hDb : ∏ p ∈ D, ab p ≤ 47 / 46 * (93 / 92) :=
    prod_ab_le_rec hl23 (fun d hd => ⟨(hDprop d hd).1, (hDprop d hd).2.1⟩) hDcard
  -- assemble
  have e1 : (∏ p ∈ G, ab p) * (∏ p ∈ E, ab p) = ∏ p ∈ P, ab p :=
    Finset.prod_filter_mul_prod_filter_not P _ ab
  have e2 : (∏ p ∈ S0, ab p) * (∏ p ∈ Gt, ab p) = ∏ p ∈ G, ab p :=
    Finset.prod_filter_mul_prod_filter_not G _ ab
  have e3 : (∏ p ∈ D, ab p) * (∏ p ∈ D', ab p) = ∏ p ∈ E, ab p :=
    Finset.prod_filter_mul_prod_filter_not E _ ab
  have e4 : ∏ p ∈ S0 ∪ D', ab p = (∏ p ∈ S0, ab p) * (∏ p ∈ D', ab p) :=
    Finset.prod_union hdisj
  have hsplit : ∏ p ∈ P, ab p =
      (∏ p ∈ S0 ∪ D', ab p) * (∏ p ∈ Gt, ab p) * (∏ p ∈ D, ab p) := by
    rw [← e1, ← e2, ← e3, e4]
    ring
  have n2 : 0 ≤ ∏ p ∈ Gt, ab p := prod_ab_nonneg fun p hp => by have := hGtbig p hp; omega
  have n3 : 0 ≤ ∏ p ∈ D, ab p := prod_ab_nonneg fun p hp => (hDprop p hp).1
  have b1 := mul_le_mul hUb hGtb n2 (by norm_num)
  have b2 := mul_le_mul b1 hDb n3 (by norm_num)
  have hnum : (15 / 8 : ℚ) * (1 / (1 - ((2 : ℕ) : ℚ) / (((81 : ℕ) : ℚ) - 1))) *
      (47 / 46 * (93 / 92)) < 2 := by norm_num
  rw [hsplit] at H
  linarith

end OddPerfect

#print axioms OddPerfect.ExcUniform.count_gt
#print axioms OddPerfect.ExcUniform.prod_ab_le_rec
#print axioms OddPerfect.dvd_of_two_exceptions_uniform
