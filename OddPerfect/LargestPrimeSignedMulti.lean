import OddPerfect.LargestPrimeSigned

/-!
# Signed capacity of the largest prime factor with any number of senders

Let `N` be an odd perfect number with largest prime factor `P`, and write `P - 1 = 2 ^ a · m`
with `m` odd. A sender of weight at least `j` into `P` is an odd prime `u < P` with
`u ^ (2 m) ≡ 1 (mod P ^ j)`. The landed modules bound the number of such senders from one, two
and (at level three only) three senders. This module does the same with any number of senders
at every level.

* `signedCount s A B`: the number of pairs of exponent vectors `a, c : {1, …, s} → ℕ` with
  `∑ a ≤ A`, `∑ c ≤ B` and `a_i c_i = 0`, defined by the recursion on the last sender.
* `card_le_of_signed_senders`: `s` senders at level `j` give `signedCount s (j / 2) ((j + 1) / 2)`
  distinct reduced pairs `(∏ u ^ a_u, ∏ u ^ c_u)`, so that count is at most `m`.
* `card_le_signedMultiLevel`: hence at most `signedMultiLevel m j` senders have weight at least
  `j`.
* `factorization_largest_le_signedCapMulti`: `e_P ≤ signedCapMulti m`, the sum of these level
  bounds over `j = 1, …, φ(m) - 1`.

These hold for every odd perfect number whose largest prime factor `P` has the given odd part
`m` of `P - 1`, with no hypothesis on the exponents. The odd part is not bounded, so no
contradiction follows and nothing is excluded. Novelty was not verified.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## The count of exponent vector pairs -/

/-- `signedCountSum f n = f 0 + ⋯ + f (n - 1)`, a structural sum that the kernel evaluates
quickly. -/
def signedCountSum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => signedCountSum f n + f n

/-- `signedCountSum` is the sum over `range n`. -/
theorem signedCountSum_eq (f : ℕ → ℕ) (n : ℕ) : signedCountSum f n = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [signedCountSum, ih, sum_range_succ]

/-- The number of pairs of exponent vectors on `s` senders with numerator degree at most `A`,
denominator degree at most `B` and disjoint supports, by the recursion on the last sender: its
exponent is `0` in both, or `A - i ≥ 1` in the numerator (with numerator budget `i` left for
the others), or `B - i ≥ 1` in the denominator. -/
def signedCount : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | s + 1, A, B => signedCount s A B + signedCountSum (fun i => signedCount s i B) A +
      signedCountSum (fun i => signedCount s A i) B

/-- The recursion of `signedCount` with the sums written over `range`. -/
theorem signedCount_succ (s A B : ℕ) : signedCount (s + 1) A B = signedCount s A B +
    (∑ i ∈ range A, signedCount s i B) + ∑ i ∈ range B, signedCount s A i := by
  rw [signedCount, signedCountSum_eq, signedCountSum_eq]

private theorem lpsm_one_le_signedCount (s A B : ℕ) : 1 ≤ signedCount s A B := by
  induction s generalizing A B with
  | zero => simp [signedCount]
  | succ s ih => rw [signedCount_succ]; have := ih A B; omega

private theorem lpsm_signedCount_mono (A B : ℕ) {s s' : ℕ} (h : s ≤ s') :
    signedCount s A B ≤ signedCount s' A B := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [signedCount_succ]; omega

private theorem lpsm_succ_le_signedCount (s A : ℕ) {B : ℕ} (hB : 1 ≤ B) :
    s + 1 ≤ signedCount s A B := by
  induction s with
  | zero => simp [signedCount]
  | succ s ih =>
    rw [signedCount_succ]
    obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
    rw [sum_range_succ]
    have := lpsm_one_le_signedCount s A B'
    omega

/-! ## The level bound -/

/-- The first failure search: starting from `s`, step up while `signedCount (s + 1) A B ≤ m`,
at most `f` times. -/
def signedLevelSearch (m A B : ℕ) : ℕ → ℕ → ℕ
  | 0, s => s
  | f + 1, s => if signedCount (s + 1) A B ≤ m then signedLevelSearch m A B f (s + 1) else s

/-- The bound on the number of senders of weight at least `j`: the largest `s ≤ m` with
`signedCount s (j / 2) ((j + 1) / 2) ≤ m`, found by a search from `0` that stops at the first
failure (the count is monotone in `s`). -/
def signedMultiLevel (m j : ℕ) : ℕ := signedLevelSearch m (j / 2) ((j + 1) / 2) m 0

/-- The signed capacity with any number of senders:
`∑ j ∈ [1, φ(m) - 1], signedMultiLevel m j`. -/
def signedCapMulti (m : ℕ) : ℕ := ∑ j ∈ Icc 1 (m.totient - 1), signedMultiLevel m j

private theorem lpsm_self_le_search (m A B f s : ℕ) : s ≤ signedLevelSearch m A B f s := by
  induction f generalizing s with
  | zero => exact le_rfl
  | succ f ih =>
    rw [signedLevelSearch]
    split_ifs
    · exact (Nat.le_succ s).trans (ih (s + 1))
    · exact le_rfl

private theorem lpsm_le_search (m A B : ℕ) {c : ℕ} (hc : signedCount c A B ≤ m) :
    ∀ f s, s ≤ c → c ≤ s + f → c ≤ signedLevelSearch m A B f s := by
  intro f
  induction f with
  | zero => intro s h1 h2; rw [signedLevelSearch]; omega
  | succ f ih =>
    intro s h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact lpsm_self_le_search m A B _ _
    · rw [signedLevelSearch, if_pos ((lpsm_signedCount_mono A B hlt).trans hc)]
      exact ih (s + 1) hlt (by omega)

/-! ## Reduced pairs from any number of senders -/

private theorem lpsm_factorization_pow_mul {u x : ℕ} (hu : u.Prime) (hx : x ≠ 0)
    (hux : ¬ u ∣ x) (a : ℕ) : (u ^ a * x).factorization u = a := by
  rw [Nat.factorization_mul (pow_ne_zero _ hu.ne_zero) hx, Finsupp.add_apply,
    Nat.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hux, Finsupp.smul_apply,
    hu.factorization_self]
  simp

private theorem lpsm_not_dvd_pow_mul {q u x : ℕ} (hq : q.Prime) (hu : u.Prime) (hqu : q ≠ u)
    (hqx : ¬ q ∣ x) (a : ℕ) : ¬ q ∣ u ^ a * x := by
  intro hd
  rcases (Nat.Prime.dvd_mul hq).mp hd with h | h
  · exact hqu ((Nat.prime_dvd_prime_iff_eq hq hu).mp (hq.dvd_of_dvd_pow h))
  · exact hqx h

private theorem lpsm_odd_pow_mul {u x : ℕ} (hu : u % 2 = 1) (hx : x % 2 = 1) (a : ℕ) :
    u ^ a * x % 2 = 1 :=
  Nat.odd_iff.mp ((Nat.odd_iff.mpr hu).pow.mul (Nat.odd_iff.mpr hx))

private theorem lpsm_root_pow_mul {u x k n : ℕ} (hu : u ^ k ≡ 1 [MOD n]) (hx : x ^ k ≡ 1 [MOD n])
    (a : ℕ) : (u ^ a * x) ^ k ≡ 1 [MOD n] := by
  have e : (u ^ a * x) ^ k = (u ^ k) ^ a * x ^ k := by ring
  rw [e]
  simpa using (hu.pow a).mul hx

private theorem lpsm_le_pow_mul {u x n i A : ℕ} (hu : u ≤ n) (hx : x ≤ n ^ i) (hi : i < A) :
    u ^ (A - i) * x ≤ n ^ A := by
  calc u ^ (A - i) * x ≤ n ^ (A - i) * n ^ i := Nat.mul_le_mul (Nat.pow_le_pow_left hu _) hx
    _ = n ^ A := by rw [← pow_add, Nat.sub_add_cancel hi.le]

private theorem lpsm_disjoint_of_tag {X Y : Finset (ℕ × ℕ)} (g : ℕ × ℕ → ℕ × ℕ) {a b : ℕ × ℕ}
    (hX : ∀ x ∈ X, g x = a) (hY : ∀ y ∈ Y, g y = b) (hab : a ≠ b) : Disjoint X Y :=
  Finset.disjoint_left.mpr fun x hx hy => hab ((hX x hx).symm.trans (hY x hy))

/-- The invariant of the pairs built from the senders in `s`. -/
private abbrev lpsmGood (P m j A B : ℕ) (s : Finset ℕ) (x : ℕ × ℕ) : Prop :=
  (∀ q, q.Prime → q ∉ s → ¬ q ∣ x.1 ∧ ¬ q ∣ x.2) ∧ Nat.Coprime x.1 x.2 ∧
    x.1 % 2 = 1 ∧ x.2 % 2 = 1 ∧ x.1 ^ (2 * m) ≡ 1 [MOD P ^ j] ∧
    x.2 ^ (2 * m) ≡ 1 [MOD P ^ j] ∧ x.1 ≤ (P - 1) ^ A ∧ x.2 ≤ (P - 1) ^ B

private theorem lpsm_exists_pairs {P m j : ℕ} (hP : P.Prime) (s : Finset ℕ)
    (hs : ∀ u ∈ s, u.Prime ∧ u % 2 = 1 ∧ u < P ∧ u ^ (2 * m) ≡ 1 [MOD P ^ j]) (A B : ℕ) :
    ∃ T : Finset (ℕ × ℕ), signedCount #s A B ≤ #T ∧ ∀ x ∈ T, lpsmGood P m j A B s x := by
  classical
  induction s using Finset.induction_on generalizing A B with
  | empty =>
    refine ⟨{(1, 1)}, by simp [signedCount], fun x hx => ?_⟩
    rw [Finset.mem_singleton.mp hx]
    have hP1 : 1 ≤ P - 1 := by have := hP.two_le; omega
    exact ⟨fun q hq _ => ⟨hq.not_dvd_one, hq.not_dvd_one⟩, Nat.coprime_one_left _, rfl, rfl,
      by rw [one_pow], by rw [one_pow], by simpa using Nat.pow_le_pow_left hP1 A,
      by simpa using Nat.pow_le_pow_left hP1 B⟩
  | insert u t hu ih =>
    have hst : ∀ v ∈ t, v.Prime ∧ v % 2 = 1 ∧ v < P ∧ v ^ (2 * m) ≡ 1 [MOD P ^ j] :=
      fun v hv => hs v (mem_insert_of_mem hv)
    obtain ⟨hup, hu2, huP, hud⟩ := hs u (mem_insert_self u t)
    choose T hTc hT using ih hst
    have hnd : ∀ i k, ∀ x ∈ T i k, ¬ u ∣ x.1 ∧ ¬ u ∣ x.2 := fun i k x hx =>
      (hT i k x hx).1 u hup hu
    have hne : ∀ i k, ∀ x ∈ T i k, x.1 ≠ 0 ∧ x.2 ≠ 0 := fun i k x hx => by
      have h1 := (hT i k x hx).2.2.1
      have h2 := (hT i k x hx).2.2.2.1
      omega
    have huP1 : u ≤ P - 1 := by omega
    let fN : ℕ → ℕ × ℕ → ℕ × ℕ := fun a x => (u ^ a * x.1, x.2)
    let fD : ℕ → ℕ × ℕ → ℕ × ℕ := fun c x => (x.1, u ^ c * x.2)
    let g : ℕ × ℕ → ℕ × ℕ := fun x => (x.1.factorization u, x.2.factorization u)
    let T1 := (range A).biUnion fun i => (T i B).image (fN (A - i))
    let T2 := (range B).biUnion fun i => (T A i).image (fD (B - i))
    have hg0 : ∀ i k, ∀ x ∈ T i k, g x = (0, 0) := fun i k x hx => by
      simp only [g, Nat.factorization_eq_zero_of_not_dvd (hnd i k x hx).1,
        Nat.factorization_eq_zero_of_not_dvd (hnd i k x hx).2]
    have hgN : ∀ i, ∀ y ∈ (T i B).image (fN (A - i)), g y = (A - i, 0) := fun i y hy => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      simp only [g, fN, lpsm_factorization_pow_mul hup (hne i B x hx).1 (hnd i B x hx).1,
        Nat.factorization_eq_zero_of_not_dvd (hnd i B x hx).2]
    have hgD : ∀ i, ∀ y ∈ (T A i).image (fD (B - i)), g y = (0, B - i) := fun i y hy => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      simp only [g, fD, lpsm_factorization_pow_mul hup (hne A i x hx).2 (hnd A i x hx).2,
        Nat.factorization_eq_zero_of_not_dvd (hnd A i x hx).1]
    have hpow0 : ∀ a, 0 < u ^ a := fun a => pow_pos hup.pos a
    have hcard1 : #T1 = ∑ i ∈ range A, #(T i B) := by
      rw [card_biUnion]
      · refine sum_congr rfl fun i _ => card_image_of_injective _ fun x y hxy => ?_
        simp only [fN, Prod.mk.injEq] at hxy
        exact Prod.ext (Nat.eq_of_mul_eq_mul_left (hpow0 _) hxy.1) hxy.2
      · intro i hi k hk hik
        simp only [Function.onFun]
        refine lpsm_disjoint_of_tag g (hgN i) (hgN k) ?_
        have := mem_range.mp hi
        have := mem_range.mp hk
        simp only [ne_eq, Prod.mk.injEq, and_true]
        omega
    have hcard2 : #T2 = ∑ i ∈ range B, #(T A i) := by
      rw [card_biUnion]
      · refine sum_congr rfl fun i _ => card_image_of_injective _ fun x y hxy => ?_
        simp only [fD, Prod.mk.injEq] at hxy
        exact Prod.ext hxy.1 (Nat.eq_of_mul_eq_mul_left (hpow0 _) hxy.2)
      · intro i hi k hk hik
        simp only [Function.onFun]
        refine lpsm_disjoint_of_tag g (hgD i) (hgD k) ?_
        have := mem_range.mp hi
        have := mem_range.mp hk
        simp only [ne_eq, Prod.mk.injEq, true_and]
        omega
    have hT1 : ∀ y ∈ T1, ∃ i < A, g y = (A - i, 0) := fun y hy => by
      obtain ⟨i, hi, hy⟩ := mem_biUnion.mp hy
      exact ⟨i, mem_range.mp hi, hgN i y hy⟩
    have hT2 : ∀ y ∈ T2, ∃ i < B, g y = (0, B - i) := fun y hy => by
      obtain ⟨i, hi, hy⟩ := mem_biUnion.mp hy
      exact ⟨i, mem_range.mp hi, hgD i y hy⟩
    have hd01 : Disjoint (T A B) T1 := Finset.disjoint_left.mpr fun x hx hy => by
      obtain ⟨i, hi, e⟩ := hT1 x hy
      rw [hg0 A B x hx, Prod.mk.injEq] at e
      omega
    have hd2 : Disjoint (T A B ∪ T1) T2 := by
      refine Finset.disjoint_left.mpr fun x hx hy => ?_
      obtain ⟨i, hi, e⟩ := hT2 x hy
      rcases Finset.mem_union.mp hx with hx | hx
      · rw [hg0 A B x hx, Prod.mk.injEq] at e
        omega
      · obtain ⟨k, hk, e'⟩ := hT1 x hx
        rw [e', Prod.mk.injEq] at e
        omega
    refine ⟨T A B ∪ T1 ∪ T2, ?_, ?_⟩
    · rw [card_union_of_disjoint hd2, card_union_of_disjoint hd01, hcard1, hcard2,
        card_insert_of_notMem hu, signedCount_succ]
      have k1 := hTc A B
      have k2 : ∑ i ∈ range A, signedCount #t i B ≤ ∑ i ∈ range A, #(T i B) :=
        sum_le_sum fun i _ => hTc i B
      have k3 : ∑ i ∈ range B, signedCount #t A i ≤ ∑ i ∈ range B, #(T A i) :=
        sum_le_sum fun i _ => hTc A i
      omega
    · intro y hy
      have hsupp : ∀ q, q.Prime → q ∉ insert u t → q ≠ u ∧ q ∉ t := fun q _ hq =>
        ⟨fun e => hq (e ▸ mem_insert_self u t), fun e => hq (mem_insert_of_mem e)⟩
      rcases Finset.mem_union.mp hy with hy | hy
      rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hT A B y hy
        refine ⟨fun q hq hqs => h1 q hq (hsupp q hq hqs).2, h2, h3, h4, h5, h6, h7, h8⟩
      · obtain ⟨i, hi, hy⟩ := mem_biUnion.mp hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        have hi' := mem_range.mp hi
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hT i B x hx
        refine ⟨fun q hq hqs => ⟨lpsm_not_dvd_pow_mul hq hup (hsupp q hq hqs).1
            (h1 q hq (hsupp q hq hqs).2).1 _, (h1 q hq (hsupp q hq hqs).2).2⟩,
          Nat.Coprime.mul_left (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hup).mpr
            (hnd i B x hx).2)) h2, lpsm_odd_pow_mul hu2 h3 _, h4, lpsm_root_pow_mul hud h5 _,
          h6, lpsm_le_pow_mul huP1 h7 hi', h8⟩
      · obtain ⟨i, hi, hy⟩ := mem_biUnion.mp hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        have hi' := mem_range.mp hi
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hT A i x hx
        refine ⟨fun q hq hqs => ⟨(h1 q hq (hsupp q hq hqs).2).1, lpsm_not_dvd_pow_mul hq hup
            (hsupp q hq hqs).1 (h1 q hq (hsupp q hq hqs).2).2 _⟩,
          Nat.Coprime.mul_right (Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hup).mpr
            (hnd A i x hx).1).symm) h2, h3, lpsm_odd_pow_mul hu2 h4 _, h5,
          lpsm_root_pow_mul hud h6 _, h7, lpsm_le_pow_mul huP1 h8 hi'⟩

/-- Signed senders at level `j`. Let `P` be prime with `P ∤ 2 m` and `j ≥ 1`, and let `s` be a
finite set of odd primes `u < P` with `u ^ (2 m) ≡ 1 (mod P ^ j)`. Then
`signedCount #s (j / 2) ((j + 1) / 2) ≤ m`: the pairs `(∏ u ^ a_u, ∏ u ^ c_u)` with
`∑ a ≤ j / 2`, `∑ c ≤ (j + 1) / 2` and `a_u c_u = 0` are distinct reduced pairs to which
`card_le_of_signed_reduced_pairs` applies. -/
theorem card_le_of_signed_senders {P m j : ℕ} (hP : P.Prime) (hPm : ¬ P ∣ 2 * m) (hj : 1 ≤ j)
    (s : Finset ℕ)
    (hs : ∀ u ∈ s, u.Prime ∧ u % 2 = 1 ∧ u < P ∧ u ^ (2 * m) ≡ 1 [MOD P ^ j]) :
    signedCount #s (j / 2) ((j + 1) / 2) ≤ m := by
  obtain ⟨T, hTc, hT⟩ := lpsm_exists_pairs hP s hs (j / 2) ((j + 1) / 2)
  have hP1 : 1 ≤ P - 1 := by have := hP.two_le; omega
  have hc := card_le_of_signed_reduced_pairs hP hPm hj T Prod.fst Prod.snd
    (fun x _ y _ h => Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
    (fun x hx => (hT x hx).2.1) (fun x hx => (hT x hx).2.2.1) (fun x hx => (hT x hx).2.2.2.1)
    (fun x hx => (hT x hx).2.2.2.2.1) (fun x hx => (hT x hx).2.2.2.2.2.1)
    (fun x hx y hy => by
      calc x.1 * y.2 ≤ (P - 1) ^ (j / 2) * (P - 1) ^ ((j + 1) / 2) :=
            Nat.mul_le_mul (hT x hx).2.2.2.2.2.2.1 (hT y hy).2.2.2.2.2.2.2
        _ = (P - 1) ^ j := by rw [← pow_add]; congr 1; omega
        _ < P ^ j := Nat.pow_lt_pow_left (by omega) (by omega))
  omega

/-- The level bound: if `P ∤ 2 m` and `j ≥ 1`, a finite set of odd primes `u < P` with
`u ^ (2 m) ≡ 1 (mod P ^ j)` has at most `signedMultiLevel m j` elements. -/
theorem card_le_signedMultiLevel {P m j : ℕ} (hP : P.Prime) (hPm : ¬ P ∣ 2 * m) (hj : 1 ≤ j)
    (s : Finset ℕ)
    (hs : ∀ u ∈ s, u.Prime ∧ u % 2 = 1 ∧ u < P ∧ u ^ (2 * m) ≡ 1 [MOD P ^ j]) :
    #s ≤ signedMultiLevel m j := by
  have h1 := card_le_of_signed_senders hP hPm hj s hs
  have h2 := lpsm_succ_le_signedCount #s (j / 2) (show 1 ≤ (j + 1) / 2 by omega)
  exact lpsm_le_search m _ _ h1 m 0 (Nat.zero_le _) (by omega)

/-! ## Senders into the largest prime factor -/

variable {N : ℕ}

private theorem lpsm_layer_cake {f n : ℕ} (h : f ≤ n) :
    f = ∑ j ∈ Finset.Icc 1 n, if j ≤ f then 1 else 0 := by
  rw [← Finset.card_filter]
  have : (Finset.Icc 1 n).filter (fun j => j ≤ f) = Finset.Icc 1 f := by
    ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [this, Nat.card_Icc]
  omega

private theorem lpsm_sum_senders (h : OddPerfect N) {P : ℕ} (hP : P ∈ N.primeFactors) :
    N.factorization P = ∑ p ∈ (N.primeFactors.erase P).filter
      (fun p => P ∣ σ 1 (p ^ N.factorization p)), padicValNat P (σ 1 (p ^ N.factorization p)) := by
  have hP2 : P ≠ 2 := by
    have := Nat.odd_iff.mp (h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hP))
    omega
  rw [factorization_eq_sum_erase h.perfect (Nat.prime_of_mem_primeFactors hP) hP2,
    Finset.sum_filter_of_ne]
  intro p _ hne
  by_contra hd
  exact hne (padicValNat.eq_zero_of_not_dvd hd)

/-- A sender `u` into the largest prime factor `P` with `P - 1 = 2 ^ a · m`, `m` odd, is an odd
prime below `P` of weight at most `φ(m) - 1`, with `u ^ (2 m) ≡ 1 (mod P ^ j)` for every `j`
up to its weight. -/
private theorem lpsm_sender_signed (h : OddPerfect N) {P a m : ℕ} (hP : P ∈ N.primeFactors)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hm : P - 1 = 2 ^ a * m) (hmo : Odd m)
    {u : ℕ} (hu : u ∈ N.primeFactors) (huP : u ≠ P) (hd : P ∣ σ 1 (u ^ N.factorization u)) :
    u.Prime ∧ u % 2 = 1 ∧ u < P ∧
      padicValNat P (σ 1 (u ^ N.factorization u)) ≤ m.totient - 1 ∧
      ∀ j, j ≤ padicValNat P (σ 1 (u ^ N.factorization u)) → u ^ (2 * m) ≡ 1 [MOD P ^ j] := by
  obtain ⟨hlt, hu2, ht, h4, hw⟩ := sender_largest_data h hP hmax hu huP hd
  have hup := Nat.prime_of_mem_primeFactors hu
  have hPp := Nat.prime_of_mem_primeFactors hP
  have : Fact P.Prime := ⟨hPp⟩
  have hu0 : (u : ZMod P) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hh
    have := Nat.le_of_dvd hup.pos hh
    omega
  have htP : orderOf (u : ZMod P) ∣ 2 ^ a * m := hm ▸ ZMod.orderOf_dvd_card_sub_one hu0
  have ht2m : orderOf (u : ZMod P) ∣ 2 * m := by
    rcases Nat.even_or_odd (orderOf (u : ZMod P)) with ⟨k, hk⟩ | hto
    · have hko : Odd k := Nat.odd_iff.mpr (by omega)
      have hkm : k ∣ m :=
        (Nat.Coprime.pow_right a ((Nat.coprime_two_right).mpr hko)).dvd_of_dvd_mul_left
          (Nat.dvd_trans ⟨2, by omega⟩ htP)
      rw [hk, ← two_mul]
      exact Nat.mul_dvd_mul_left 2 hkm
    · exact ((Nat.Coprime.pow_right a ((Nat.coprime_two_right).mpr hto)).dvd_of_dvd_mul_left
        htP).trans (dvd_mul_left m 2)
  refine ⟨hup, hu2, hlt, ?_, fun j hj => ?_⟩
  · have h1 := padicValNat_pow_orderOf_sub_one_lt_totient hup hPp hlt ht
    have h2 : (orderOf (u : ZMod P)).totient ≤ m.totient := by
      rw [← Nat.totient_two_mul_of_odd hmo]
      exact Nat.le_of_dvd (Nat.totient_pos.mpr (by have := hmo.pos; omega))
        (Nat.totient_dvd_of_dvd ht2m)
    rw [hw]
    omega
  · rw [hw] at hj
    have hpt : 1 ≤ u ^ orderOf (u : ZMod P) := Nat.one_le_pow _ _ hup.pos
    have hdvd : P ^ j ∣ u ^ orderOf (u : ZMod P) - 1 :=
      (pow_dvd_pow P hj).trans pow_padicValNat_dvd
    have hmod : u ^ orderOf (u : ZMod P) ≡ 1 [MOD P ^ j] :=
      ((Nat.modEq_iff_dvd' hpt).mpr hdvd).symm
    obtain ⟨k, hk⟩ := ht2m
    rw [hk, pow_mul]
    simpa using hmod.pow k

/-- Signed capacity of the largest prime factor with any number of senders. Let `P` be the
largest prime factor of an odd perfect number `N` and `P - 1 = 2 ^ a · m` with `m` odd. Then
`v_P(N) ≤ signedCapMulti m`: the senders of weight at least `j` number at most
`signedMultiLevel m j`. This holds for every odd perfect number; the odd part `m` is not
bounded, so no contradiction follows. -/
theorem factorization_largest_le_signedCapMulti (h : OddPerfect N) {P a m : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * m) (hmo : Odd m) : N.factorization P ≤ signedCapMulti m := by
  classical
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hPm : ¬ P ∣ 2 * m := by
    intro hd
    have hmpos := hmo.pos
    have ha : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    have hmP : m < P := by
      have := Nat.le_mul_of_pos_left m ha
      have := hPp.two_le
      omega
    rcases (Nat.Prime.dvd_mul hPp).mp hd with h2 | h2
    · have := Nat.le_of_dvd two_pos h2
      have hPodd : P % 2 = 1 :=
        Nat.odd_iff.mp (h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hP))
      have := hPp.two_le
      omega
    · have := Nat.le_of_dvd hmpos h2
      omega
  rw [lpsm_sum_senders h hP]
  set S := (N.primeFactors.erase P).filter (fun p => P ∣ σ 1 (p ^ N.factorization p)) with hS
  set w : ℕ → ℕ := fun u => padicValNat P (σ 1 (u ^ N.factorization u)) with hwdef
  have hdat : ∀ u ∈ S, u.Prime ∧ u % 2 = 1 ∧ u < P ∧ w u ≤ m.totient - 1 ∧
      ∀ j, j ≤ w u → u ^ (2 * m) ≡ 1 [MOD P ^ j] := by
    intro u hu
    rw [hS, Finset.mem_filter, Finset.mem_erase] at hu
    exact lpsm_sender_signed h hP hmax hm hmo hu.1.2 hu.1.1 hu.2
  calc ∑ u ∈ S, w u
      = ∑ u ∈ S, ∑ j ∈ Finset.Icc 1 (m.totient - 1), (if j ≤ w u then 1 else 0) :=
        Finset.sum_congr rfl fun u hu => lpsm_layer_cake (hdat u hu).2.2.2.1
    _ = ∑ j ∈ Finset.Icc 1 (m.totient - 1), #(S.filter (fun u => j ≤ w u)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => (Finset.card_filter _ _).symm
    _ ≤ signedCapMulti m := by
        unfold signedCapMulti
        refine Finset.sum_le_sum fun j hj => ?_
        refine card_le_signedMultiLevel hPp hPm (Finset.mem_Icc.mp hj).1 _ fun u hu => ?_
        obtain ⟨huS, hju⟩ := Finset.mem_filter.mp hu
        obtain ⟨h1, h2, h3, -, h5⟩ := hdat u huS
        exact ⟨h1, h2, h3, h5 j hju⟩

end OddPerfect

#print axioms OddPerfect.signedCountSum_eq
#print axioms OddPerfect.signedCount_succ
#print axioms OddPerfect.card_le_of_signed_senders
#print axioms OddPerfect.card_le_signedMultiLevel
#print axioms OddPerfect.factorization_largest_le_signedCapMulti
