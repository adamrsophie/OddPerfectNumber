import OddPerfect.PerfectRigidity
import OddPerfect.RestrainedFifteen
import OddPerfect.RestrainedEighteen
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Forbidden return and reachability of prime factors

For an odd perfect number `N` say that a prime factor `p` *sends to* a prime `t` when
`t ∣ σ(p ^ v_p(N))`.

* `not_dvd_phi3_of_dvd_succ`: for `q > 7` (prime or not) and `t ∣ q + 1`, `q ∤ t² + t + 1`.
  `sq_not_sends_back`: if the special prime `q > 7` has exponent 1 and a square prime `s`
  sends to `q`, then `q` does not send to `s`.
* `exists_sends_into`: for a nonempty proper subset `U` of the prime factors, some prime factor
  outside `U` sends to a member of `U`.
* `ball N r i` is the set of prime factors at distance at most `i` from `r` along the relation
  "sends to"; `layer N r i` is the set at distance exactly `i`. `exists_ball_eq` and
  `biUnion_layer_eq`: from a prime factor `r` every prime factor lies in some layer.
* `prod_layer_succ_le`: if every prime of layer `i` has exponent at most 2, the product of the
  primes of layer `i + 1` is at most twice the square of the product of the primes of layer `i`.
* `restrained_prod_lt` and `restrained_three_lt`: in the restrained family with special
  exponent 1, if every prime factor lies within distance `d` of 3, the product of the prime
  factors other than 3 is below `3 ^ ((E + 1)(2 ^ d - 1))` with `E = v_3(N)`, and
  `E < 3 ^ (2 ^ d + 1)`. With the landed bound `E ≥ 288482`, some prime factor has distance at
  least 4 from 3 (`restrained_exists_far`).

No uniform upper bound on the distance from 3 is proved here (for each `N` the number of
prime factors minus one is a trivial bound), so the restrained family is not excluded by these
results. These are restricted results checked by the kernel; novelty is not verified.
The odd perfect number conjecture is open and nothing here decides it.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace ReturnReach

/-! ### Forbidden return -/

/-- If `z w = q + 1` and `q ∣ z² + z + 1` then `q ∣ w² + w + 1`. -/
theorem dvd_phi3_swap {q z w : ℕ} (hzw : z * w = q + 1) (h : q ∣ z ^ 2 + z + 1) :
    q ∣ w ^ 2 + w + 1 := by
  have hid : w ^ 2 * (z ^ 2 + z + 1) = (w ^ 2 + w + 1) + q * (q + 2 + w) := by
    have : w ^ 2 * (z ^ 2 + z + 1) = (z * w) ^ 2 + (z * w) * w + w ^ 2 := by ring
    rw [this, hzw]; ring
  have h2 : q ∣ (w ^ 2 + w + 1) + q * (q + 2 + w) := hid ▸ dvd_mul_of_dvd_right h _
  exact (Nat.dvd_add_left (dvd_mul_right q _)).mp h2

/-- The case `z ≤ w` of the forbidden return. -/
theorem not_dvd_phi3_of_le {q z w : ℕ} (h7 : 7 < q) (hzw : z * w = q + 1) (hle : z ≤ w)
    (h : q ∣ z ^ 2 + z + 1) : False := by
  obtain ⟨c, hc⟩ := h
  have hzz : z * z ≤ q + 1 := hzw ▸ Nat.mul_le_mul_left z hle
  have hc1 : c = 1 := by
    rcases Nat.lt_or_ge c 2 with hc2 | hc2
    · interval_cases c
      · omega
      · rfl
    · exfalso
      have : 2 * q ≤ z ^ 2 + z + 1 := by rw [hc, mul_comm 2 q]; exact Nat.mul_le_mul_left q hc2
      nlinarith
  subst hc1
  have hz2 : z ∣ 2 := by
    have : z ∣ z * (z + 1) + 2 := by
      have : z * (z + 1) + 2 = z * w := by rw [hzw]; nlinarith
      rw [this]; exact dvd_mul_right z w
    exact (Nat.dvd_add_right (dvd_mul_right z _)).mp this
  have hz : z ≤ 2 := Nat.le_of_dvd (by norm_num) hz2
  interval_cases z <;> omega

end ReturnReach

open ReturnReach

/-- **Forbidden return.** For `q > 7` (in particular a prime `q > 7`) and a divisor `t` of
`q + 1`, `q` does not divide `t² + t + 1`. With `q + 1 = t h`, `q ∣ t² + t + 1` gives
`q ∣ h² + h + 1`; for `z = min(t, h)` this forces `z² + z + 1 = q` and `z ∣ 2`, so
`q ∈ {3, 7}`. The primality of `q` and the positivity of `t` are not needed.
The statement also follows from `eq_one_or_two_or_four_of_dvd_phi3_of_dvd_succ` in
`OddPerfect/LargePrimes.lean` (Zelinsky's Lemma 1, arXiv 1810.11734), which gives
`t ∈ {1, 2, 4}`. Restricted result; novelty not verified. -/
theorem not_dvd_phi3_of_dvd_succ {q t : ℕ} (h7 : 7 < q) (htd : t ∣ q + 1) :
    ¬ q ∣ t ^ 2 + t + 1 := by
  intro h
  obtain ⟨w, hw⟩ := htd
  rcases le_total t w with hle | hle
  · exact not_dvd_phi3_of_le h7 hw.symm hle h
  · exact not_dvd_phi3_of_le h7 (by rw [hw]; ring) hle (dvd_phi3_swap hw.symm h)

/-- **No return to a square prime.** Let the prime `q > 7` have exponent 1 in `N` (for an odd
perfect number: the special prime with exponent 1), and let the prime `s` have exponent 2 and
send to `q`, that is `q ∣ σ(s ^ 2) = s² + s + 1`. Then `q` does not send to `s`:
`s ∤ σ(q) = q + 1`. The hypothesis that `N` is odd perfect is not needed.
It also follows from `prime_dvd_phi3_dvd_succ` in `OddPerfect/LargePrimes.lean` (Zelinsky's
Lemma 1, arXiv 1810.11734), which forces `(s, q) = (2, 7)`.
Restricted result; novelty not verified. -/
theorem sq_not_sends_back {N q s : ℕ} (hq : q.Prime) (h7 : 7 < q) (hq1 : N.factorization q = 1)
    (hs : s.Prime) (hs2 : N.factorization s = 2)
    (hqs : q ∣ σ 1 (s ^ N.factorization s)) : ¬ s ∣ σ 1 (q ^ N.factorization q) := by
  rw [hs2, sigma_one_apply_prime_pow hs] at hqs
  rw [hq1, sigma_one_apply_prime_pow hq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at hqs ⊢
  intro hsd
  exact not_dvd_phi3_of_dvd_succ (t := s) h7 (by rw [add_comm]; exact hsd)
    (by convert hqs using 1; ring)

namespace ReturnReach

/-! ### Unitary parts -/

/-- The unitary divisor of `N` carried by a set `T` of primes. -/
def part (N : ℕ) (T : Finset ℕ) : ℕ := ∏ p ∈ T, p ^ N.factorization p

/-- The parts of a set of prime factors and of its complement multiply to `N`. -/
theorem part_mul_compl {N : ℕ} {T : Finset ℕ} (hN : N ≠ 0) (hT : T ⊆ N.primeFactors) :
    part N T * part N (N.primeFactors \ T) = N := by
  unfold part
  rw [mul_comm, Finset.prod_sdiff hT]
  exact (Nat.prod_primeFactors_pow_factorization hN).symm

/-- The parts of disjoint sets of prime factors are coprime. -/
theorem coprime_part {N : ℕ} {A B : Finset ℕ} (hA : A ⊆ N.primeFactors) (hB : B ⊆ N.primeFactors)
    (hAB : Disjoint A B) : Nat.Coprime (part N A) (part N B) := by
  unfold part
  refine Nat.Coprime.prod_left fun a ha => Nat.Coprime.prod_right fun b hb => ?_
  refine Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors (hA ha))
    (Nat.prime_of_mem_primeFactors (hB hb))).mpr ?_)
  rintro rfl
  exact Finset.disjoint_left.mp hAB ha hb

/-- The divisor sum of a part is the product of the component divisor sums. -/
theorem sigma_part {N : ℕ} {T : Finset ℕ} (hT : T ⊆ N.primeFactors) :
    σ 1 (part N T) = ∏ p ∈ T, σ 1 (p ^ N.factorization p) := by
  unfold part
  refine isMultiplicative_sigma.map_prod _ T fun a ha b hb hab => ?_
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors (hT ha))
    (Nat.prime_of_mem_primeFactors (hT hb))).mpr hab)

/-- A part is positive. -/
theorem part_pos {N : ℕ} {T : Finset ℕ} (hT : T ⊆ N.primeFactors) : 0 < part N T :=
  Finset.prod_pos fun _ hp => pow_pos (Nat.prime_of_mem_primeFactors (hT hp)).pos _

/-- The part of a nonempty set of prime factors exceeds 1. -/
theorem one_lt_part {N : ℕ} {T : Finset ℕ} (hT : T ⊆ N.primeFactors) (hne : T.Nonempty) :
    1 < part N T := by
  obtain ⟨p, hp⟩ := hne
  have hpp := Nat.prime_of_mem_primeFactors (hT hp)
  have hv : 1 ≤ N.factorization p :=
    hpp.factorization_pos_of_dvd (Nat.mem_primeFactors.mp (hT hp)).2.2
      (Nat.mem_primeFactors.mp (hT hp)).2.1
  have h1 : p ≤ p ^ N.factorization p := Nat.le_self_pow (by omega) p
  have h2 : p ^ N.factorization p ≤ part N T :=
    Finset.single_le_prod' (fun i hi => Nat.one_le_iff_ne_zero.mpr
      (pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hT hi)).ne_zero)) hp
  have := hpp.one_lt
  omega

/-- A part divides `N`. -/
theorem part_dvd {N : ℕ} {T : Finset ℕ} (hN : N ≠ 0) (hT : T ⊆ N.primeFactors) :
    part N T ∣ N :=
  ⟨_, (part_mul_compl hN hT).symm⟩

/-- The cofactor of a part is the part of the complement. -/
theorem div_part {N : ℕ} {T : Finset ℕ} (hN : N ≠ 0) (hT : T ⊆ N.primeFactors) :
    N / part N T = part N (N.primeFactors \ T) := by
  exact Nat.div_eq_of_eq_mul_right (part_pos hT) (part_mul_compl hN hT).symm

/-- The part of a proper subset of the prime factors is below `N`. -/
theorem part_lt {N : ℕ} {T : Finset ℕ} (hN : N ≠ 0) (hT : T ⊆ N.primeFactors)
    (hne : T ≠ N.primeFactors) : part N T < N := by
  have hc : (N.primeFactors \ T).Nonempty := by
    rw [Finset.sdiff_nonempty]
    exact fun h => hne (Finset.Subset.antisymm hT h)
  have h1 := one_lt_part (Finset.sdiff_subset (s := N.primeFactors) (t := T)) hc
  have h0 := part_pos hT
  conv_rhs => rw [← part_mul_compl hN hT]
  exact lt_mul_of_one_lt_right h0 h1

/-- A part is a unitary divisor of `N`. -/
theorem coprime_div_part {N : ℕ} {T : Finset ℕ} (hN : N ≠ 0) (hT : T ⊆ N.primeFactors) :
    Nat.Coprime (part N T) (N / part N T) := by
  rw [div_part hN hT]
  exact coprime_part hT Finset.sdiff_subset Finset.disjoint_sdiff

/-- For an odd perfect number, `σ(part N T) ≤ 2 part N T` for every set `T` of prime factors. -/
theorem sigma_part_le {N : ℕ} (h : OddPerfect N) {T : Finset ℕ} (hT : T ⊆ N.primeFactors) :
    σ 1 (part N T) ≤ 2 * part N T := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp [part]
  by_cases hall : T = N.primeFactors
  · have := part_mul_compl h.ne_zero hT
    rw [hall, Finset.sdiff_self] at this
    simp only [part, Finset.prod_empty, mul_one] at this
    rw [hall]
    unfold part
    rw [this, h.sigma_eq]
  · exact (sigma_unitary_divisor_bounds h.sigma_eq (part_dvd h.ne_zero hT)
      (coprime_div_part h.ne_zero hT) (one_lt_part hT hne) (part_lt h.ne_zero hT hall)).2.le

/-- The primes of `T`, each receiving from some member of `A`, have product dividing
`σ(part N A)`. -/
theorem prod_dvd_sigma_part {N : ℕ} {A T : Finset ℕ} (hA : A ⊆ N.primeFactors)
    (hT : ∀ t ∈ T, t.Prime) (hs : ∀ t ∈ T, ∃ p ∈ A, t ∣ σ 1 (p ^ N.factorization p)) :
    ∏ t ∈ T, t ∣ σ 1 (part N A) := by
  rw [sigma_part hA]
  refine Finset.prod_primes_dvd _ (fun t ht => (hT t ht).prime) fun t ht => ?_
  obtain ⟨p, hp, hd⟩ := hs t ht
  exact hd.trans (Finset.dvd_prod_of_mem _ hp)

end ReturnReach

/-! ### Reachability -/

/-- **Every set of prime factors is entered.** Let `U` be a nonempty proper subset of the prime
factors of an odd perfect number `N`. Some prime factor `p ∉ U` sends to a member `t` of `U`:
`t ∣ σ(p ^ v_p(N))`. The unitary divisor carried by the complement of `U` has a forced prime
(`exists_forced_prime`), which lies in `U` and divides the divisor sum of a component of the
complement. This restates `exists_sigmaEdge_crossing` (`OddPerfect/Network.lean`, proved for
every perfect `N`) for odd perfect `N`. Restricted result; novelty not verified. -/
theorem exists_sends_into {N : ℕ} (h : OddPerfect N) {U : Finset ℕ} (hU : U ⊆ N.primeFactors)
    (hne : U.Nonempty) (hproper : U ≠ N.primeFactors) :
    ∃ p ∈ N.primeFactors, p ∉ U ∧ ∃ t ∈ U, t ∣ σ 1 (p ^ N.factorization p) := by
  set V := N.primeFactors \ U with hV
  have hVsub : V ⊆ N.primeFactors := Finset.sdiff_subset
  have hVne : V.Nonempty := by
    rw [hV, Finset.sdiff_nonempty]
    exact fun h' => hproper (Finset.Subset.antisymm hU h')
  obtain ⟨u, hu⟩ := hne
  have hVproper : V ≠ N.primeFactors := by
    intro hEq
    have : u ∈ V := hEq ▸ hU hu
    exact (Finset.mem_sdiff.mp this).2 hu
  have hN0 := h.ne_zero
  obtain ⟨r, hr, hforced⟩ := exists_forced_prime h.sigma_eq (part_dvd hN0 hVsub)
    (coprime_div_part hN0 hVsub) (one_lt_part hVsub hVne) (part_lt hN0 hVsub hVproper)
  have hrC := forced_prime_dvd_cofactor h.sigma_eq (part_dvd hN0 hVsub)
    (coprime_div_part hN0 hVsub) (one_lt_part hVsub hVne) hr hforced
  rw [div_part hN0 hVsub, hV, Finset.sdiff_sdiff_eq_self hU] at hrC
  obtain ⟨t, ht, hrt⟩ := (Prime.dvd_finsetProd_iff hr.prime _).mp hrC
  have hrt' : r = t := (Nat.prime_dvd_prime_iff_eq hr
    (Nat.prime_of_mem_primeFactors (hU ht))).mp (hr.dvd_of_dvd_pow hrt)
  subst hrt'
  have hsig0 : σ 1 (part N V) ≠ 0 := (sigma_pos 1 _ (part_pos hVsub).ne').ne'
  have hrs : r ∣ σ 1 (part N V) := (hr.dvd_iff_one_le_factorization hsig0).mpr (by omega)
  rw [sigma_part hVsub] at hrs
  obtain ⟨p, hp, hrp⟩ := (Prime.dvd_finsetProd_iff hr.prime _).mp hrs
  obtain ⟨hpN, hpU⟩ := Finset.mem_sdiff.mp hp
  exact ⟨p, hpN, hpU, r, ht, hrp⟩

/-- The prime factors of `N` at distance at most `i` from `r` along the relation "sends to":
`ball N r 0 = {r}`, and `ball N r (i + 1)` adds the prime factors `t` with
`t ∣ σ(p ^ v_p(N))` for some `p ∈ ball N r i`. -/
def ball (N r : ℕ) : ℕ → Finset ℕ
  | 0 => {r}
  | i + 1 => ball N r i ∪
      N.primeFactors.filter fun t => ∃ p ∈ ball N r i, t ∣ σ 1 (p ^ N.factorization p)

/-- The layers from `r`: `layer N r 0 = {r}` and `layer N r (i + 1)` is the set of prime
factors that receive from a prime of `ball N r i` (equivalently of `layer N r i`, see
`mem_layer_succ`) and lie in no earlier layer. -/
def layer (N r : ℕ) : ℕ → Finset ℕ
  | 0 => {r}
  | i + 1 => ball N r (i + 1) \ ball N r i

namespace ReturnReach

/-- The balls increase with the radius by one. -/
theorem ball_subset_succ (N r i : ℕ) : ball N r i ⊆ ball N r (i + 1) :=
  Finset.subset_union_left

/-- The balls increase with the radius. -/
theorem ball_mono (N r : ℕ) {i j : ℕ} (hij : i ≤ j) : ball N r i ⊆ ball N r j := by
  induction j with
  | zero => rw [Nat.le_zero.mp hij]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · exact (ih (by omega)).trans (ball_subset_succ N r j)
    · rw [show i = j + 1 by omega]

/-- From a prime factor, every ball consists of prime factors. -/
theorem ball_subset {N r : ℕ} (hr : r ∈ N.primeFactors) (i : ℕ) :
    ball N r i ⊆ N.primeFactors := by
  induction i with
  | zero => simpa [ball] using hr
  | succ i ih => exact Finset.union_subset ih (Finset.filter_subset _ _)

/-- Membership in the next ball. -/
theorem mem_ball_succ {N r i t : ℕ} :
    t ∈ ball N r (i + 1) ↔ t ∈ ball N r i ∨
      (t ∈ N.primeFactors ∧ ∃ p ∈ ball N r i, t ∣ σ 1 (p ^ N.factorization p)) := by
  simp [ball, Finset.mem_union, Finset.mem_filter]

/-- A layer lies in the ball of the same radius. -/
theorem layer_subset_ball (N r i : ℕ) : layer N r i ⊆ ball N r i := by
  cases i with
  | zero => exact Finset.Subset.refl _
  | succ i => exact Finset.sdiff_subset

/-- The center lies in every ball. -/
theorem r_mem_ball (N r i : ℕ) : r ∈ ball N r i :=
  ball_mono N r (Nat.zero_le i) (by simp [ball])

/-- The center lies in no layer after the first. -/
theorem r_not_mem_layer_succ (N r i : ℕ) : r ∉ layer N r (i + 1) := fun h =>
  (Finset.mem_sdiff.mp h).2 (r_mem_ball N r i)

/-- A prime of layer `i + 1` receives from a prime of layer `i`. -/
theorem mem_layer_succ {N r i t : ℕ} (ht : t ∈ layer N r (i + 1)) :
    t ∈ N.primeFactors ∧ ∃ p ∈ layer N r i, t ∣ σ 1 (p ^ N.factorization p) := by
  obtain ⟨ht1, ht0⟩ := Finset.mem_sdiff.mp ht
  rcases mem_ball_succ.mp ht1 with h | ⟨htN, p, hp, hd⟩
  · exact absurd h ht0
  refine ⟨htN, p, ?_, hd⟩
  cases i with
  | zero => exact hp
  | succ j =>
    refine Finset.mem_sdiff.mpr ⟨hp, fun hpj => ht0 ?_⟩
    exact mem_ball_succ.mpr (Or.inr ⟨htN, p, hpj, hd⟩)

/-- The ball of radius `d` is the union of the layers `0, …, d`. -/
theorem ball_eq_biUnion (N r d : ℕ) :
    ball N r d = (Finset.range (d + 1)).biUnion (layer N r) := by
  induction d with
  | zero => simp [ball, layer]
  | succ d ih =>
    rw [Finset.range_add_one, Finset.biUnion_insert, ← ih]
    ext t
    simp only [Finset.mem_union, layer, Finset.mem_sdiff]
    constructor
    · intro h
      by_cases hd : t ∈ ball N r d
      · exact Or.inr hd
      · exact Or.inl ⟨h, hd⟩
    · rintro (⟨h, -⟩ | h)
      · exact h
      · exact ball_subset_succ N r d h

/-- While the ball is a proper subset of the prime factors, it grows. -/
theorem card_lt_ball_succ {N r i : ℕ} (h : OddPerfect N) (hr : r ∈ N.primeFactors)
    (hne : ball N r i ≠ N.primeFactors) :
    (ball N r i).card < (ball N r (i + 1)).card := by
  set U := N.primeFactors \ ball N r i
  have hsub := ball_subset hr i
  have hUne : U.Nonempty := by
    rw [Finset.sdiff_nonempty]
    exact fun h' => hne (Finset.Subset.antisymm hsub h')
  have hUproper : U ≠ N.primeFactors := by
    intro hEq
    have : r ∈ U := hEq ▸ hr
    exact (Finset.mem_sdiff.mp this).2 (r_mem_ball N r i)
  obtain ⟨p, hpN, hpU, t, htU, hd⟩ := exists_sends_into h Finset.sdiff_subset hUne hUproper
  have hpB : p ∈ ball N r i := by
    by_contra hc
    exact hpU (Finset.mem_sdiff.mpr ⟨hpN, hc⟩)
  obtain ⟨htN, htB⟩ := Finset.mem_sdiff.mp htU
  refine Finset.card_lt_card (Finset.ssubset_iff_of_subset (ball_subset_succ N r i) |>.mpr ?_)
  exact ⟨t, mem_ball_succ.mpr (Or.inr ⟨htN, p, hpB, hd⟩), htB⟩

/-- Either the ball of radius `i` is everything or it has at least `i + 1` members. -/
theorem ball_card_ge {N r : ℕ} (h : OddPerfect N) (hr : r ∈ N.primeFactors) (i : ℕ) :
    ball N r i = N.primeFactors ∨ i + 1 ≤ (ball N r i).card := by
  induction i with
  | zero => right; simp [ball]
  | succ i ih =>
    by_cases he : ball N r (i + 1) = N.primeFactors
    · exact Or.inl he
    right
    have hne : ball N r i ≠ N.primeFactors := by
      intro hb
      apply he
      exact Finset.Subset.antisymm (ball_subset hr _) (hb ▸ ball_subset_succ N r i)
    rcases ih with hb | hb
    · exact absurd hb hne
    · have := card_lt_ball_succ h hr hne
      omega

end ReturnReach

open ReturnReach

/-- **Every prime factor is reached.** For a prime factor `r` of an odd perfect number `N`,
the ball of radius `ω(N)` around `r` along the relation "sends to" is the set of all prime
factors. Restricted result; novelty not verified. -/
theorem exists_ball_eq {N r : ℕ} (h : OddPerfect N) (hr : r ∈ N.primeFactors) :
    ball N r N.primeFactors.card = N.primeFactors := by
  rcases ball_card_ge h hr N.primeFactors.card with hb | hb
  · exact hb
  · have := Finset.card_le_card (ball_subset hr N.primeFactors.card)
    omega

/-- **Every prime factor lies in a layer.** For a prime factor `r` of an odd perfect number
`N`, the union of the layers `0, …, ω(N)` from `r` is the set of all prime factors.
Restricted result; novelty not verified. -/
theorem biUnion_layer_eq {N r : ℕ} (h : OddPerfect N) (hr : r ∈ N.primeFactors) :
    (Finset.range (N.primeFactors.card + 1)).biUnion (layer N r) = N.primeFactors := by
  rw [← ball_eq_biUnion, exists_ball_eq h hr]

/-! ### Layer sizes -/

/-- **Layer sizes when exponents are at most 2.** Let `r` be a prime factor of an odd perfect
number `N`, and suppose every prime of layer `i` from `r` has exponent at most 2. Then the
product of the primes of layer `i + 1` is at most twice the square of the product of the
primes of layer `i`. Restricted result; novelty not verified. -/
theorem prod_layer_succ_le {N r : ℕ} (h : OddPerfect N) (hr : r ∈ N.primeFactors) (i : ℕ)
    (he : ∀ p ∈ layer N r i, N.factorization p ≤ 2) :
    ∏ t ∈ layer N r (i + 1), t ≤ 2 * (∏ p ∈ layer N r i, p) ^ 2 := by
  have hA : layer N r i ⊆ N.primeFactors := (layer_subset_ball N r i).trans (ball_subset hr i)
  have hdvd := prod_dvd_sigma_part (N := N) hA
    (fun t ht => Nat.prime_of_mem_primeFactors (mem_layer_succ ht).1)
    (fun t ht => (mem_layer_succ ht).2)
  have hle := Nat.le_of_dvd (sigma_pos 1 _ (part_pos hA).ne') hdvd
  have hM : part N (layer N r i) ≤ (∏ p ∈ layer N r i, p) ^ 2 := by
    unfold part
    rw [← Finset.prod_pow]
    exact Finset.prod_le_prod' fun p hp =>
      Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors (hA hp)).pos (he p hp)
  have := sigma_part_le h hA
  omega

namespace ReturnReach

/-! ### Restrained family -/

/-- `2 σ(3 ^ E) + 1 = 3 ^ (E + 1)`. -/
theorem two_mul_sigma_three_pow_add_one (E : ℕ) : 2 * σ 1 (3 ^ E) + 1 = 3 ^ (E + 1) := by
  rw [sigma_one_apply_prime_pow Nat.prime_three]
  induction E with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, mul_add, pow_succ 3 (k + 1)]; omega

/-- The product of a finite set of positive integers is at least the factorial of its size. -/
theorem factorial_card_le_prod (s : Finset ℕ) (hs : ∀ x ∈ s, 0 < x) :
    s.card.factorial ≤ ∏ x ∈ s, x := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h' => lt_irrefl a (hlt a h')
    rw [Finset.card_insert_of_notMem ha, Finset.prod_insert ha, Nat.factorial_succ]
    have hsub : s ⊆ Finset.Ioo 0 a := fun x hx =>
      Finset.mem_Ioo.mpr ⟨hs x (Finset.mem_insert_of_mem hx), hlt x hx⟩
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Ioo] at hc
    have hapos := hs a (Finset.mem_insert_self a s)
    exact Nat.mul_le_mul (by omega) (ih fun x hx => hs x (Finset.mem_insert_of_mem hx))

/-- `n ^ n ≤ 3 ^ n n!`, from `n ^ n / n! ≤ e ^ n` and `e < 3`. -/
theorem pow_self_le (n : ℕ) : n ^ n ≤ 3 ^ n * n.factorial := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h1 := Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
  rw [div_le_iff₀ hf] at h1
  have h2 : Real.exp (n : ℝ) ≤ 3 ^ n := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le n
  have h3 : ((n ^ n : ℕ) : ℝ) ≤ ((3 ^ n * n.factorial : ℕ) : ℝ) := by
    push_cast
    exact h1.trans (mul_le_mul_of_nonneg_right h2 hf.le)
  exact_mod_cast h3

end ReturnReach

/-- **Restrained family: product of the prime factors within distance `d` of 3.** Let `N` be
an odd perfect number with special prime `q` of exponent 1, a prime `r ≠ q`, and every prime
factor other than `q` and `r` of exponent 2 (the landed results give `r = 3`). If every prime
factor lies within distance `d` of 3 along the relation "sends to" (`ball N 3 d` is the set of
all prime factors), then the product of the prime factors other than 3 is below
`3 ^ ((E + 1)(2 ^ d - 1))` with `E = v_3(N)`. No uniform upper bound on the distance from 3 is
proved here, and the family is not excluded. Restricted result; novelty not verified. -/
theorem restrained_prod_lt {N q r d : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hq1 : N.factorization q = 1) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hball : ball N 3 d = N.primeFactors) :
    ∏ p ∈ N.primeFactors.erase 3, p < 3 ^ ((N.factorization 3 + 1) * (2 ^ d - 1)) := by
  have hodd : Odd (N.factorization q) := by rw [hq1]; exact odd_one
  obtain ⟨rfl, -⟩ := restrained_exception_eq_three h hq hodd hr hrq hsq
  set E := N.factorization 3
  have h3N : 3 ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_three, restrained_three_dvd h hq hodd hr hrq hsq,
      h.ne_zero⟩
  have hqN : q ∈ N.primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hq, Nat.dvd_of_factorization_pos (by omega), h.ne_zero⟩
  have hq3 : q ≠ 3 := hrq.symm
  -- exponents at most 2 away from 3
  have hle2 : ∀ p ∈ N.primeFactors, p ≠ 3 → N.factorization p ≤ 2 := by
    intro p hp hp3
    by_cases hpq : p = q
    · rw [hpq, hq1]; norm_num
    · rw [hsq p hp hpq hp3]
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exfalso
      have : q ∈ ball N 3 0 := hball ▸ hqN
      simp [ball] at this
      exact hq3 this
    · exact hd
  set K : ℕ → ℕ := fun i => ∏ t ∈ layer N 3 i, t
  set P : ℕ → ℕ := fun i => ∏ t ∈ (ball N 3 i).erase 3, t
  set x := 2 * σ 1 (3 ^ E)
  have hx : x < 3 ^ (E + 1) := by
    have := two_mul_sigma_three_pow_add_one E; omega
  -- the first layer
  have hK1 : 2 * K 1 ≤ x := by
    have hA : ({3} : Finset ℕ) ⊆ N.primeFactors := Finset.singleton_subset_iff.mpr h3N
    have hdvd := prod_dvd_sigma_part (N := N) (T := layer N 3 1) hA
      (fun t ht => Nat.prime_of_mem_primeFactors (mem_layer_succ ht).1)
      (fun t ht => by simpa [layer] using (mem_layer_succ ht).2)
    simp only [part, Finset.prod_singleton] at hdvd
    have : K 1 ≤ σ 1 (3 ^ E) := Nat.le_of_dvd (sigma_pos 1 _ (pow_ne_zero _ (by norm_num))) hdvd
    simp only [x]
    omega
  -- later layers
  have hKs : ∀ j, K (j + 2) ≤ 2 * K (j + 1) ^ 2 := by
    intro j
    refine prod_layer_succ_le h h3N (j + 1) fun p hp => ?_
    have hpB := (layer_subset_ball N 3 (j + 1)) hp
    refine hle2 p (ball_subset h3N _ hpB) ?_
    rintro rfl
    exact r_not_mem_layer_succ N 3 j hp
  -- the ball minus 3 splits into the previous one and the new layer
  have hP : ∀ i, P (i + 1) = P i * K (i + 1) := by
    intro i
    simp only [P, K, layer]
    have hsplit : (ball N 3 (i + 1)).erase 3 =
        (ball N 3 (i + 1) \ ball N 3 i) ∪ (ball N 3 i).erase 3 := by
      ext t
      simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ⟨h3, hb⟩
        by_cases hti : t ∈ ball N 3 i
        · exact Or.inr ⟨h3, hti⟩
        · exact Or.inl ⟨hb, hti⟩
      · rintro (⟨hb, hti⟩ | ⟨h3, hti⟩)
        · exact ⟨fun ht3 => hti (ht3 ▸ r_mem_ball N 3 i), hb⟩
        · exact ⟨h3, ball_subset_succ N 3 i hti⟩
    rw [hsplit, Finset.prod_union, mul_comm]
    rw [Finset.disjoint_left]
    intro t ht ht'
    exact (Finset.mem_sdiff.mp ht).2 (Finset.mem_of_mem_erase ht')
  have hP0 : P 0 = 1 := by simp [P, ball]
  -- induction
  have key : ∀ j, 2 * K (j + 1) ≤ x ^ (2 ^ j) ∧
      2 ^ (j + 1) * P (j + 1) ≤ x ^ (2 ^ (j + 1) - 1) := by
    intro j
    induction j with
    | zero =>
      refine ⟨by simpa using hK1, ?_⟩
      rw [hP 0, hP0]
      simpa using hK1
    | succ j ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hk : 2 * K (j + 2) ≤ x ^ 2 ^ (j + 1) := by
        have := hKs j
        calc 2 * K (j + 2) ≤ (2 * K (j + 1)) ^ 2 := by nlinarith
          _ ≤ (x ^ 2 ^ j) ^ 2 := Nat.pow_le_pow_left ih1 2
          _ = x ^ 2 ^ (j + 1) := by rw [← pow_mul, pow_succ]
      refine ⟨hk, ?_⟩
      have he : 2 ^ (j + 1 + 1) - 1 = (2 ^ (j + 1) - 1) + 2 ^ (j + 1) := by
        have : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
        rw [pow_succ]; omega
      rw [hP (j + 1), he]
      calc 2 ^ (j + 1 + 1) * (P (j + 1) * K (j + 1 + 1))
          = (2 ^ (j + 1) * P (j + 1)) * (2 * K (j + 2)) := by ring
        _ ≤ x ^ (2 ^ (j + 1) - 1) * x ^ 2 ^ (j + 1) := Nat.mul_le_mul ih2 hk
        _ = x ^ (2 ^ (j + 1) - 1 + 2 ^ (j + 1)) := (pow_add _ _ _).symm
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
  have hPd : P (j + 1) = ∏ p ∈ N.primeFactors.erase 3, p := by simp only [P, hball]
  rw [← hPd, pow_mul]
  have h2 := (key j).2
  have hpos : 2 ^ (j + 1) - 1 ≠ 0 := by
    have : 2 ≤ 2 ^ (j + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  calc P (j + 1) ≤ 2 ^ (j + 1) * P (j + 1) := Nat.le_mul_of_pos_left _ (by positivity)
    _ ≤ x ^ (2 ^ (j + 1) - 1) := h2
    _ < (3 ^ (E + 1)) ^ (2 ^ (j + 1) - 1) := Nat.pow_lt_pow_left hx hpos

/-- **Restrained family: bounded distance bounds the exponent of 3.** In the setting of
`restrained_prod_lt` (special exponent 1), if every prime factor lies within distance `d` of 3
then `E < 3 ^ (2 ^ d + 1)` with `E = v_3(N)`. With `a = 1` the `E` prime factors that are
1 modulo 3 (`restrained_three_eq`) have product at least `E!`, and `E ^ E ≤ 3 ^ E E!`. This
is an upper bound for `E` in a structural subfamily: no uniform upper bound on the distance
is proved here, and the family is not excluded. Restricted result; novelty not verified. -/
theorem restrained_three_lt {N q r d : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hq1 : N.factorization q = 1) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hball : ball N 3 d = N.primeFactors) :
    N.factorization 3 < 3 ^ (2 ^ d + 1) := by
  have hodd : Odd (N.factorization q) := by rw [hq1]; exact odd_one
  have hlt := restrained_prod_lt h hq hq1 hr hrq hsq hball
  have hE := restrained_three_eq h hq hodd hr hrq hsq
  rw [hq1, show padicValNat 3 (1 + 1) = 0 by norm_num, add_zero] at hE
  set E := N.factorization 3
  set O := {p ∈ N.primeFactors | p ≠ 3 ∧ p ≠ q ∧ p % 3 = 1}
  have hsub : O ⊆ N.primeFactors.erase 3 := fun p hp => by
    obtain ⟨hpN, hp3, -⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_erase.mpr ⟨hp3, hpN⟩
  have hO : E.factorial ≤ ∏ p ∈ N.primeFactors.erase 3, p := by
    rw [hE]
    refine (factorial_card_le_prod O fun x hx =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hx).1).pos).trans ?_
    exact Nat.le_of_dvd (Finset.prod_pos fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).pos)
      (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
  have hF : E.factorial < 3 ^ ((E + 1) * (2 ^ d - 1)) := lt_of_le_of_lt hO hlt
  by_contra hge
  push Not at hge
  set k := 2 ^ d
  have hk1 : 1 ≤ k := Nat.one_le_two_pow
  have hkE : k ≤ E := by
    have : k < 3 ^ (k + 1) := by
      calc k < 2 ^ k := Nat.lt_two_pow_self
        _ ≤ 3 ^ k := Nat.pow_le_pow_left (by norm_num) k
        _ ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h1 : 3 ^ ((k + 1) * E) ≤ E ^ E := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hge E
  have h2 := pow_self_le E
  have h3 : 3 ^ E * E.factorial < 3 ^ E * 3 ^ ((E + 1) * (k - 1)) :=
    Nat.mul_lt_mul_of_pos_left hF (by positivity)
  rw [← pow_add] at h3
  have h4 : 3 ^ ((k + 1) * E) < 3 ^ (E + (E + 1) * (k - 1)) := by omega
  have h5 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp h4
  obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [hm, Nat.add_sub_cancel] at h5
  nlinarith

/-- **Restrained family: some prime factor is far from 3.** In the setting of
`restrained_prod_lt` (special exponent 1), some prime factor has distance at least 4 from 3:
it is not in `ball N 3 3`. From `restrained_three_lt` with `d = 3`, `E < 3 ^ 9 = 19683`, against
`E ≥ 288482` (`restrained_three_ge_wheel`). The family is not excluded.
Restricted result; novelty not verified. -/
theorem restrained_exists_far {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hq1 : N.factorization q = 1) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    ∃ p ∈ N.primeFactors, p ∉ ball N 3 3 := by
  have hodd : Odd (N.factorization q) := by rw [hq1]; exact odd_one
  obtain ⟨rfl, -⟩ := restrained_exception_eq_three h hq hodd hr hrq hsq
  by_contra hcon
  push Not at hcon
  have hb : ball N 3 3 = N.primeFactors :=
    Finset.Subset.antisymm (ball_subset (Nat.mem_primeFactors.mpr ⟨Nat.prime_three,
      restrained_three_dvd h hq hodd hr hrq hsq, h.ne_zero⟩) 3) hcon
  have h1 := restrained_three_lt h hq hq1 hr hrq hsq hb
  have h2 := restrained_three_ge_wheel h hq hodd hr hrq hsq
  norm_num at h1
  omega

end OddPerfect

#print axioms OddPerfect.ReturnReach.dvd_phi3_swap
#print axioms OddPerfect.ReturnReach.not_dvd_phi3_of_le
#print axioms OddPerfect.not_dvd_phi3_of_dvd_succ
#print axioms OddPerfect.sq_not_sends_back
#print axioms OddPerfect.ReturnReach.part_mul_compl
#print axioms OddPerfect.ReturnReach.coprime_part
#print axioms OddPerfect.ReturnReach.sigma_part
#print axioms OddPerfect.ReturnReach.part_pos
#print axioms OddPerfect.ReturnReach.one_lt_part
#print axioms OddPerfect.ReturnReach.part_dvd
#print axioms OddPerfect.ReturnReach.div_part
#print axioms OddPerfect.ReturnReach.part_lt
#print axioms OddPerfect.ReturnReach.coprime_div_part
#print axioms OddPerfect.ReturnReach.sigma_part_le
#print axioms OddPerfect.ReturnReach.prod_dvd_sigma_part
#print axioms OddPerfect.exists_sends_into
#print axioms OddPerfect.ReturnReach.ball_subset_succ
#print axioms OddPerfect.ReturnReach.ball_mono
#print axioms OddPerfect.ReturnReach.ball_subset
#print axioms OddPerfect.ReturnReach.mem_ball_succ
#print axioms OddPerfect.ReturnReach.layer_subset_ball
#print axioms OddPerfect.ReturnReach.r_mem_ball
#print axioms OddPerfect.ReturnReach.r_not_mem_layer_succ
#print axioms OddPerfect.ReturnReach.mem_layer_succ
#print axioms OddPerfect.ReturnReach.ball_eq_biUnion
#print axioms OddPerfect.ReturnReach.card_lt_ball_succ
#print axioms OddPerfect.ReturnReach.ball_card_ge
#print axioms OddPerfect.exists_ball_eq
#print axioms OddPerfect.biUnion_layer_eq
#print axioms OddPerfect.prod_layer_succ_le
#print axioms OddPerfect.ReturnReach.two_mul_sigma_three_pow_add_one
#print axioms OddPerfect.ReturnReach.factorial_card_le_prod
#print axioms OddPerfect.ReturnReach.pow_self_le
#print axioms OddPerfect.restrained_prod_lt
#print axioms OddPerfect.restrained_three_lt
#print axioms OddPerfect.restrained_exists_far
