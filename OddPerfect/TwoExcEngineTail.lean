import OddPerfect.TwoExcEngineState
import OddPerfect.RankinTailGeneral

/-!
# Soundness of the deficient leaf of the two exception checker

This module proves `defSound`: whenever `deficientB P ks x dd` accepts, no number satisfies the
state `(ks, x)`. It is a tool for the certificate checker of `OddPerfect.TwoExcEngine`; by itself
it proves nothing about odd perfect numbers.

## The counting argument

Let `N` be a member of the family with special prime `q` that satisfies the state. Since `N` is
perfect, `σ(N)/N = 2`, and this is the product of `σ(p^v)/p^v` over the prime factors `p` of `N`.

* Keys. The product over the keys is at most `H = hiProd P ks`: a square key gives exactly
  `(p^2 + p + 1)/p^2`, an exact free key with `kmin ≤ KCAP` gives exactly `σ(p^kmin)/p^kmin`, and
  every other key gives less than `p/(p - 1)`.
* Every prime factor that is not a key is at least `x`, since all prime factors below `x` are
  keys. The non keys fall into the following classes.
* (a) and (b): `q` if it is not a key (then no key has the role of `q`, so `a = 1`), and the
  exceptions that are not keys. The exception keys and these exceptions are distinct prime
  factors other than `q` with exponent other than 2, so there are at most `E - nexc ks` of
  the latter. Together this is the set `U` of at most `u = a + b` primes, and each contributes
  less than `x/(x - 1)`.
* The remaining non keys are squares `t` other than `q`. As `3` is a key and `N` is odd,
  `t ≡ 1` or `t ≡ 2 (mod 3)`, and each contributes `fv t ≤ fv x = (x^2 + x + 1)/x^2`.
* (c) A square `t ≡ 1 (mod 3)` sends a factor 3 to the budget of 3. By the conservation law
  `sigmaWeight_sum_eq`, the weights of the distinct components sending to 3 add up to at most
  `v_3(N) = b3`, where `b3 = budget3` of the role of the key 3: 2 for a square, `kmin` for an
  exception of exact exponent `kmin` (the role fixes the exponent; nothing else about 3 is
  used). The key components of 3 already use `csum cs3`, and the new squares are other
  components. So there are at most `c = b3 - csum cs3` of them.
* (d) A square `t ≡ 2 (mod 3)` whose row `t^2 + t + 1` has a prime factor `g` that is a square
  key `≡ 1 (mod 3)`, an exact free key `≡ 1 (mod 3)`, or a square of class (c). Each such `t`
  uses one unit of the budget of `g`: the remaining budget of a key is at most
  `v_g(N) - csum`, which is the summand of `dCap`, and a square of class (c) has budget 2. So
  there are at most `d = dCap ks + 2 c` of them.
* (e) Every other square `t ≡ 2 (mod 3)`. Each prime factor of its row is `≡ 1 (mod 3)`, divides
  `N`, and is neither of the kinds in (d), so it is a non exact free key `≡ 1 (mod 3)` (the set
  `K = genK ks`) or an element of `U`. If the row is a product of powers of `K` below `MHIT`,
  the enumeration visited it, found the square `4 n - 3 = (2 t + 1)^2` and counted `t` as a hit:
  the product over these `t` is at most `hn/hd`. Otherwise `t` lies in the set `T` of
  `prod_fv_le_of_rankin_tail_general`, whose hypotheses are the checks of `tailOK`, so the
  product over `T` is at most `1/(1 - S)`.

Hence `2 ≤ H (x/(x - 1))^u ((x^2 + x + 1)/x^2)^(c + d) (hn/hd)/(1 - S)`, and the last check of
`tailOK` says that this bound is below 2.

The enumeration needs no assumption on the parameters: running out of fuel sets the flag to
false, so an accepting run has visited every product of the generators below `MHIT`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace TwoExcEngine

open RestrainedFour (fv)

/-! ## The square filter -/

private def qrTest (m mask s : ℕ) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight mask (Nat.mod (Nat.mul s s) m)) 1) 1

private def qrRowAux (m mask : ℕ) (f : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun s ih => cond (qrTest m mask s) ih false) f

private def qrAll (l : List (ℕ × ℕ)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun mm _ ih => cond (Nat.blt 0 mm.1) (cond (qrRowAux mm.1 mm.2 mm.1) ih false) false) l

private theorem qrAll_ok : qrAll qrTable = true := by decide +kernel

private def qrPassL (l : List (ℕ × ℕ)) (z : ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun mm _ ih => cond (Nat.beq (Nat.land (Nat.shiftRight mm.2 (Nat.mod z mm.1)) 1) 1) ih false)
    l

private theorem qrRowAux_spec {m mask : ℕ} :
    ∀ f, qrRowAux m mask f = true → ∀ s < f, qrTest m mask s = true := by
  intro f
  induction f with
  | zero => intro _ s hs; omega
  | succ f ih =>
    intro h s hs
    have h' : cond (qrTest m mask f) (qrRowAux m mask f) false = true := h
    cases hq : qrTest m mask f
    · rw [hq] at h'; exact absurd h' Bool.false_ne_true
    · rw [hq] at h'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
      · exact ih h' s hs
      · subst hs; exact hq

private theorem qrPassL_sq : ∀ (l : List (ℕ × ℕ)), qrAll l = true → ∀ s, qrPassL l (s * s) = true := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons mm l ih =>
    intro h s
    have h' : cond (Nat.blt 0 mm.1) (cond (qrRowAux mm.1 mm.2 mm.1) (qrAll l) false) false = true := h
    cases h0 : Nat.blt 0 mm.1
    · rw [h0] at h'; exact absurd h' Bool.false_ne_true
    rw [h0] at h'
    cases h1 : qrRowAux mm.1 mm.2 mm.1
    · rw [h1] at h'; exact absurd h' Bool.false_ne_true
    rw [h1] at h'
    have hm : 0 < mm.1 := by simpa [Nat.blt_eq] using h0
    have ht := qrRowAux_spec mm.1 h1 (s % mm.1) (Nat.mod_lt _ hm)
    show cond (Nat.beq (Nat.land (Nat.shiftRight mm.2 (Nat.mod (s * s) mm.1)) 1) 1)
      (qrPassL l (s * s)) false = true
    have e : Nat.mod (s * s) mm.1 = Nat.mod (Nat.mul (s % mm.1) (s % mm.1)) mm.1 := by
      show (s * s) % mm.1 = (s % mm.1 * (s % mm.1)) % mm.1
      exact Nat.mul_mod _ _ _
    rw [e]
    have ht' : Nat.beq (Nat.land (Nat.shiftRight mm.2 (Nat.mod (Nat.mul (s % mm.1) (s % mm.1)) mm.1)) 1) 1 = true := ht
    rw [ht']
    exact ih h' s

private theorem qrPass_sq (s : ℕ) : qrPass (s * s) = true :=
  qrPassL_sq qrTable qrAll_ok s

/-! ## The enumeration -/

/-- A candidate that the enumeration must count as a hit. -/
private def Good (ks : List Key) (x t : ℕ) : Prop :=
  t.Prime ∧ x ≤ t ∧ t % 3 = 2 ∧ isKey ks t = false ∧ t % 2 = 1

private def ratio (acc : Acc) : ℚ := (acc.2.1 : ℚ) / acc.2.2

private def Mono (F : Acc → Acc) : Prop := ∀ acc, (F acc).1 = true → acc.1 = true

private def Cov (ks : List Key) (x : ℕ) (F : Acc → Acc) (C : ℕ → Prop) : Prop :=
  ∀ (acc : Acc) (A : Finset ℕ), (F acc).1 = true → (∀ t ∈ A, Good ks x t ∧ C (phi3 t)) →
    0 < acc.2.2 → 0 < (F acc).2.2 ∧ ratio acc * ∏ t ∈ A, fv t ≤ ratio (F acc)

private theorem fv_nonneg (t : ℕ) : 0 ≤ fv t := by unfold fv; positivity

private theorem ratio_nonneg (acc : Acc) : 0 ≤ ratio acc := by unfold ratio; positivity

private theorem cov_comp {ks : List Key} {x : ℕ} {F G : Acc → Acc} {C D : ℕ → Prop}
    (hF : Cov ks x F C) (hG : Cov ks x G D) (hGm : Mono G) :
    Cov ks x (fun acc => G (F acc)) (fun n => C n ∨ D n) := by
  classical
  intro acc A h hA h0
  have h1 := hGm _ h
  obtain ⟨p1, i1⟩ := hF acc (A.filter fun t => C (phi3 t)) h1
    (fun t ht => ⟨(hA t (Finset.mem_filter.1 ht).1).1, (Finset.mem_filter.1 ht).2⟩) h0
  obtain ⟨p2, i2⟩ := hG (F acc) (A.filter fun t => ¬ C (phi3 t)) h
    (fun t ht => ⟨(hA t (Finset.mem_filter.1 ht).1).1,
      (hA t (Finset.mem_filter.1 ht).1).2.resolve_left (Finset.mem_filter.1 ht).2⟩) p1
  refine ⟨p2, ?_⟩
  rw [← Finset.prod_filter_mul_prod_filter_not A (fun t => C (phi3 t))]
  have hA2 : 0 ≤ ∏ t ∈ A.filter (fun t => ¬ C (phi3 t)), fv t :=
    Finset.prod_nonneg fun t _ => fv_nonneg t
  calc ratio acc * ((∏ t ∈ A.filter (fun t => C (phi3 t)), fv t) *
        ∏ t ∈ A.filter (fun t => ¬ C (phi3 t)), fv t)
      = (ratio acc * ∏ t ∈ A.filter (fun t => C (phi3 t)), fv t) *
        ∏ t ∈ A.filter (fun t => ¬ C (phi3 t)), fv t := by ring
    _ ≤ ratio (F acc) * ∏ t ∈ A.filter (fun t => ¬ C (phi3 t)), fv t :=
        mul_le_mul_of_nonneg_right i1 hA2
    _ ≤ ratio (G (F acc)) := i2

private theorem cov_mono {ks : List Key} {x : ℕ} {F : Acc → Acc} {C D : ℕ → Prop}
    (hF : Cov ks x F C) (h : ∀ n, D n → C n) : Cov ks x F D := fun acc A h1 hA h0 =>
  hF acc A h1 (fun t ht => ⟨(hA t ht).1, h _ (hA t ht).2⟩) h0

private theorem cov_congr {ks : List Key} {x : ℕ} {F G : Acc → Acc} {C : ℕ → Prop}
    (hF : Cov ks x F C) (h : ∀ acc, G acc = F acc) : Cov ks x G C := by
  intro acc A h1 hA h0
  rw [h] at h1 ⊢
  exact hF acc A h1 hA h0

private theorem cov_id {ks : List Key} {x : ℕ} : Cov ks x (fun acc => acc) (fun _ => False) := by
  intro acc A _ hA h0
  have : A = ∅ := Finset.eq_empty_of_forall_notMem fun t ht => (hA t ht).2
  subst this
  simp [h0]

/-- The shape of one visit: unchanged, rejected, or multiplied by `n / t^2` with `t^2 ≤ n`. -/
private theorem visit_shape (ks : List Key) (x : ℕ) (comps : List (ℕ × ℕ)) (acc : Acc) (n : ℕ) :
    visit ks x comps acc n = acc ∨ (visit ks x comps acc n).1 = false ∨
      ∃ t, visit ks x comps acc n = (acc.1, acc.2.1 * n, acc.2.2 * (t * t)) ∧ 0 < t ∧
        t * t ≤ n := by
  unfold visit
  dsimp only
  cases hq : qrPass (Nat.sub (Nat.mul 4 n) 3)
  · left; rfl
  simp only [cond_true]
  unfold sqrtIfSq
  rw [hq]
  simp only [cond_true]
  generalize newton 400 _ _ = s
  cases hs : Nat.beq (Nat.mul s s) (Nat.sub (Nat.mul 4 n) 3)
  · simp only [cond_false]
    cases (Nat.blt (Nat.mul s s) (Nat.sub (Nat.mul 4 n) 3) &&
        Nat.blt (Nat.sub (Nat.mul 4 n) 3) (Nat.mul (Nat.add s 1) (Nat.add s 1)))
    · right; left; rfl
    · left; rfl
  simp only [cond_true]
  have hss : s * s = 4 * n - 3 := Nat.eq_of_beq_eq_true hs
  unfold visitSq
  dsimp only
  split_ifs with h1
  · left; rfl
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or,
    Decidable.not_not] at h1
  obtain ⟨⟨⟨h1a, -⟩, -⟩, -⟩ := h1
  split
  · split_ifs
    · left; rfl
    · right; left; rfl
  · right; right
    refine ⟨(s - 1) / 2, rfl, ?_, ?_⟩
    · omega
    · generalize ht : (s - 1) / 2 = t at h1a ⊢
      have h2 : 2 * t + 1 ≤ s := by omega
      have h3 : (2 * t + 1) * (2 * t + 1) ≤ s * s := Nat.mul_le_mul h2 h2
      have h4 : (2 * t + 1) * (2 * t + 1) = 4 * (t * t) + 4 * t + 1 := by ring
      omega

private theorem visit_mono (ks : List Key) (x : ℕ) (comps : List (ℕ × ℕ)) (n : ℕ) :
    Mono (fun acc => visit ks x comps acc n) := by
  intro acc h
  beta_reduce at h
  rcases visit_shape ks x comps acc n with e | e | ⟨t, e, -⟩
  · rwa [e] at h
  · rw [e] at h; exact absurd h Bool.false_ne_true
  · rw [e] at h; exact h

/-- A good candidate is a hit or makes the visit reject. -/
private theorem visit_good {ks : List Key} {x : ℕ} (comps : List (ℕ × ℕ)) (acc : Acc) {t : ℕ}
    (ht : Good ks x t) :
    (visit ks x comps acc (phi3 t)).1 = false ∨
      visit ks x comps acc (phi3 t) = (acc.1, acc.2.1 * phi3 t, acc.2.2 * (t * t)) := by
  obtain ⟨hp, hxt, h3, hk, h2⟩ := ht
  have hz : Nat.sub (Nat.mul 4 (phi3 t)) 3 = (2 * t + 1) * (2 * t + 1) := by
    show 4 * (t ^ 2 + t + 1) - 3 = _
    have : 4 * (t ^ 2 + t + 1) = (2 * t + 1) * (2 * t + 1) + 3 := by ring
    omega
  unfold visit
  dsimp only
  rw [hz, qrPass_sq]
  simp only [cond_true]
  unfold sqrtIfSq
  rw [qrPass_sq]
  simp only [cond_true]
  generalize newton 400 _ _ = s
  cases hs : Nat.beq (Nat.mul s s) ((2 * t + 1) * (2 * t + 1))
  · simp only [cond_false]
    cases hb : (Nat.blt (Nat.mul s s) ((2 * t + 1) * (2 * t + 1)) &&
        Nat.blt ((2 * t + 1) * (2 * t + 1)) (Nat.mul (Nat.add s 1) (Nat.add s 1)))
    · left; rfl
    · exfalso
      simp only [Bool.and_eq_true, Nat.blt_eq] at hb
      obtain ⟨hb1, hb2⟩ := hb
      have l1 : s < 2 * t + 1 := Nat.mul_self_lt_mul_self_iff.mp hb1
      have l2 : 2 * t + 1 < s + 1 := Nat.mul_self_lt_mul_self_iff.mp hb2
      omega
  simp only [cond_true]
  have hss : s = 2 * t + 1 := Nat.mul_self_inj.mp (Nat.eq_of_beq_eq_true hs)
  subst hss
  unfold visitSq
  dsimp only
  have e1 : (2 * t + 1 - 1) / 2 = t := by omega
  rw [e1]
  have hkey : (t % 2 == 0 || t % 3 != 2 || decide (t < x) || isKey ks t) = false := by
    rw [hk]
    simp only [Bool.or_false, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
      bne_eq_false_iff_eq, decide_eq_false_iff_not, not_lt]
    exact ⟨⟨by omega, h3⟩, hxt⟩
  rw [if_neg (by rw [hkey]; decide)]
  split
  · next w _ =>
    left
    rw [if_neg]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_and]
    intro ⟨hw1, hw2⟩ hw3
    have hdvd : w ∣ t := Nat.dvd_of_mod_eq_zero hw3
    rcases hp.eq_one_or_self_of_dvd w hdvd with h | h
    · omega
    · omega
  · right; rfl

private theorem cov_visit (ks : List Key) (x : ℕ) (comps : List (ℕ × ℕ)) (n : ℕ) :
    Cov ks x (fun acc => visit ks x comps acc n) (fun m => m = n) := by
  classical
  intro acc A h hA h0
  beta_reduce at h ⊢
  by_cases hne : A.Nonempty
  · obtain ⟨t, htA⟩ := hne
    obtain ⟨hg, hn⟩ := hA t htA
    have hAt : A = {t} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨htA, fun t' ht' => ?_⟩
      exact phi3_strictMono.injective ((hA t' ht').2.trans hn.symm)
    subst hAt hn
    rcases visit_good comps acc hg with e | e
    · rw [e] at h; exact absurd h Bool.false_ne_true
    rw [e]
    have ht0 : 0 < t := hg.1.pos
    refine ⟨Nat.mul_pos h0 (Nat.mul_pos ht0 ht0), ?_⟩
    rw [Finset.prod_singleton]
    unfold ratio fv phi3
    have : (0 : ℚ) < t := by exact_mod_cast ht0
    have : (0 : ℚ) < acc.2.2 := by exact_mod_cast h0
    push_cast
    rw [div_mul_div_comm]
    apply le_of_eq
    congr 1
    ring
  · have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst hAe
    rw [Finset.prod_empty, mul_one]
    rcases visit_shape ks x comps acc n with e | e | ⟨t, e, ht0, htn⟩
    · rw [e]; exact ⟨h0, le_rfl⟩
    · rw [e] at h; exact absurd h Bool.false_ne_true
    · rw [e]
      refine ⟨Nat.mul_pos h0 (Nat.mul_pos ht0 ht0), ?_⟩
      unfold ratio
      simp only
      have htt : (0 : ℚ) < ((t * t : ℕ) : ℚ) := by exact_mod_cast Nat.mul_pos ht0 ht0
      have hd : (0 : ℚ) < acc.2.2 := by exact_mod_cast h0
      have hle : ((t * t : ℕ) : ℚ) ≤ n := by exact_mod_cast htn
      rw [Nat.cast_mul, Nat.cast_mul acc.2.2, div_le_div_iff₀ hd (mul_pos hd htt)]
      have : (0 : ℚ) ≤ acc.2.1 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hle (mul_nonneg this hd.le)]

private theorem loopPow_succ (MH g : ℕ) (inner : ℕ → Acc → Acc) (f v : ℕ) (acc : Acc) :
    loopPow MH g inner (f + 1) v acc =
      cond (Nat.ble MH v) acc (loopPow MH g inner f (v * g) (inner v acc)) := rfl

private theorem cov_loopPow {ks : List Key} {x MH g : ℕ} (hg : 1 ≤ g) {inner : ℕ → Acc → Acc}
    {C : ℕ → ℕ → Prop} (hin : ∀ v, Cov ks x (inner v) (C v)) (hinm : ∀ v, Mono (inner v)) :
    ∀ f v, Cov ks x (loopPow MH g inner f v) (fun n => ∃ i, v * g ^ i < MH ∧ C (v * g ^ i) n) ∧
      Mono (loopPow MH g inner f v) := by
  intro f
  induction f with
  | zero =>
    intro v
    refine ⟨fun acc A h _ _ => absurd h (by show ¬ (false = true); decide),
      fun acc h => absurd h (by show ¬ (false = true); decide)⟩
  | succ f ih =>
    intro v
    by_cases hv : MH ≤ v
    · have e : ∀ acc, loopPow MH g inner (f + 1) v acc = acc := fun acc => by
        rw [loopPow_succ, Nat.ble_eq_true_of_le hv, cond_true]
      refine ⟨cov_congr (cov_mono cov_id ?_) e, fun acc h => by rwa [e] at h⟩
      rintro n ⟨i, hi, -⟩
      have : v ≤ v * g ^ i := Nat.le_mul_of_pos_right v (Nat.pow_pos (by omega))
      omega
    · have e : ∀ acc, loopPow MH g inner (f + 1) v acc =
          loopPow MH g inner f (v * g) (inner v acc) := fun acc => by
        have hb : Nat.ble MH v = false := by
          cases hb : Nat.ble MH v
          · rfl
          · exact absurd (Nat.le_of_ble_eq_true hb) hv
        rw [loopPow_succ, hb, cond_false]
      obtain ⟨ihc, ihm⟩ := ih (v * g)
      refine ⟨cov_congr (cov_mono (cov_comp (hin v) ihc ihm) ?_) e, fun acc h => ?_⟩
      · rintro n ⟨i, hi, hc⟩
        rcases i with _ | i
        · left; simpa using hc
        · right
          refine ⟨i, ?_, ?_⟩
          · have e2 : v * g * g ^ i = v * g ^ (i + 1) := by ring
            rwa [e2]
          · have e2 : v * g * g ^ i = v * g ^ (i + 1) := by ring
            rwa [e2]
      · rw [e] at h
        exact hinm v _ (ihm _ h)

/-- The values `v ∏ g ^ e_g` over a list of generators. -/
private def InGen : List ℕ → ℕ → ℕ → Prop
  | [], v, n => n = v
  | g :: gs, v, n => ∃ i, InGen gs (v * g ^ i) n

private theorem inGen_le : ∀ (gs : List ℕ), (∀ g ∈ gs, 1 ≤ g) → ∀ v n, InGen gs v n → v ≤ n := by
  intro gs
  induction gs with
  | nil => intro _ v n h; exact le_of_eq h.symm
  | cons g gs ih =>
    intro hg v n ⟨i, hi⟩
    have h1 := ih (fun g' hg' => hg g' (List.mem_cons_of_mem g hg')) _ _ hi
    have : v ≤ v * g ^ i :=
      Nat.le_mul_of_pos_right v (Nat.pow_pos (hg g List.mem_cons_self))
    omega

private theorem cov_enumG {ks : List Key} {x MH : ℕ} (comps : List (ℕ × ℕ)) :
    ∀ (gs : List ℕ), (∀ g ∈ gs, 1 ≤ g) → ∀ v,
      Cov ks x (enumG MH (visit ks x comps) gs v) (fun n => n < MH ∧ InGen gs v n) ∧
        Mono (enumG MH (visit ks x comps) gs v) := by
  intro gs
  induction gs with
  | nil =>
    intro _ v
    have e : ∀ acc, enumG MH (visit ks x comps) [] v acc = visit ks x comps acc v :=
      fun acc => by rw [enumG]
    refine ⟨cov_congr (cov_mono (cov_visit ks x comps v) fun n h => h.2) e, fun acc h => ?_⟩
    rw [e] at h
    exact visit_mono ks x comps v acc h
  | cons g gs ih =>
    intro hg v
    have hg1 : 1 ≤ g := hg g List.mem_cons_self
    have hgs : ∀ g' ∈ gs, 1 ≤ g' := fun g' hg' => hg g' (List.mem_cons_of_mem g hg')
    have e : ∀ acc, enumG MH (visit ks x comps) (g :: gs) v acc =
        loopPow MH g (enumG MH (visit ks x comps) gs) 200 v acc := fun acc => by rw [enumG]
    obtain ⟨hc, hm⟩ := cov_loopPow (MH := MH) hg1 (fun w => (ih hgs w).1) (fun w => (ih hgs w).2)
      200 v
    refine ⟨cov_congr (cov_mono hc ?_) e, fun acc h => by rw [e] at h; exact hm acc h⟩
    rintro n ⟨hn, i, hi⟩
    exact ⟨i, lt_of_le_of_lt (inGen_le gs hgs _ _ hi) hn, hn, hi⟩

private theorem inGen_of_primeFactors : ∀ (gs : List ℕ), (∀ g ∈ gs, 2 ≤ g) → ∀ v n, n ≠ 0 →
    n.primeFactors ⊆ gs.toFinset → InGen gs v (v * n) := by
  intro gs
  induction gs with
  | nil =>
    intro _ v n hn h
    have : n.primeFactors = ∅ := Finset.subset_empty.mp (by simpa using h)
    rcases Nat.primeFactors_eq_empty.mp this with h0 | h1
    · exact absurd h0 hn
    · subst h1; show v * 1 = v; ring
  | cons g gs ih =>
    intro hg v n hn h
    have hg2 := hg g List.mem_cons_self
    obtain ⟨i, m, hgm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn g (by omega)
    have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hnm; exact hn hnm
    refine ⟨i, ?_⟩
    have := ih (fun g' hg' => hg g' (List.mem_cons_of_mem g hg')) (v * g ^ i) m hm0 ?_
    · rwa [hnm, ← mul_assoc]
    · intro p hp
      have hpm := Nat.dvd_of_mem_primeFactors hp
      have hpn : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr
        ⟨Nat.prime_of_mem_primeFactors hp, hnm ▸ Dvd.dvd.mul_left hpm _, hn⟩
      have := h hpn
      rw [List.toFinset_cons, Finset.mem_insert] at this
      rcases this with rfl | h'
      · exact absurd hpm hgm
      · exact h'

/-- If the enumeration accepts, the hit product dominates the product of `fv` over any finite set
of good candidates whose rows are products of the generators below the limit. -/
private theorem enum_hits {ks : List Key} {x MH : ℕ} {comps : List (ℕ × ℕ)} {gs : List ℕ}
    (hgs : ∀ g ∈ gs, 2 ≤ g) {hn hd : ℕ}
    (h : enumG MH (visit ks x comps) gs 1 (true, 1, 1) = (true, hn, hd)) (A : Finset ℕ)
    (hA : ∀ t ∈ A, Good ks x t ∧ phi3 t < MH ∧ (phi3 t).primeFactors ⊆ gs.toFinset) :
    0 < hd ∧ ∏ t ∈ A, fv t ≤ (hn : ℚ) / hd := by
  obtain ⟨hc, -⟩ := cov_enumG (ks := ks) (x := x) (MH := MH) comps gs
    (fun g hg => by have := hgs g hg; omega) 1
  have := hc (true, 1, 1) A (by rw [h]) (fun t ht => ⟨(hA t ht).1, (hA t ht).2.1, by
    have := inGen_of_primeFactors gs hgs 1 (phi3 t) (by unfold phi3; omega) (hA t ht).2.2
    rwa [one_mul] at this⟩) Nat.one_pos
  rw [h] at this
  obtain ⟨h1, h2⟩ := this
  refine ⟨h1, ?_⟩
  unfold ratio at h2
  simpa using h2

/-! ## Keys -/

private theorem isKey_iff (ks : List Key) (p : ℕ) : isKey ks p = true ↔ p ∈ ks.map Key.p := by
  induction ks with
  | nil => show (false = true) ↔ p ∈ ([] : List Key).map Key.p; simp
  | cons k ks ih =>
    show cond (Nat.beq k.p p) true (isKey ks p) = true ↔ _
    cases h : Nat.beq k.p p
    · have hne := Nat.ne_of_beq_eq_false h
      rw [cond_false, ih, List.map_cons, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (h' | h')
        · exact absurd h'.symm hne
        · exact h'
    · have := Nat.eq_of_beq_eq_true h
      simp [this]

private theorem findKey_some {ks : List Key} {p : ℕ} {k : Key} (h : findKey p ks = some k) :
    k ∈ ks ∧ k.p = p := by
  induction ks with
  | nil => exact absurd h (by simp [findKey])
  | cons k' ks ih =>
    have h' : cond (Nat.beq k'.p p) (some k') (findKey p ks) = some k := h
    cases hb : Nat.beq k'.p p
    · rw [hb, cond_false] at h'
      obtain ⟨h1, h2⟩ := ih h'
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩
    · rw [hb, cond_true, Option.some.injEq] at h'
      subst h'
      exact ⟨List.mem_cons_self, Nat.eq_of_beq_eq_true hb⟩

private theorem csum_eq (l : List (ℕ × ℕ)) : csum l = (l.map Prod.snd).sum := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    show Nat.add e.2 (csum l) = _
    rw [ih, List.map_cons, List.sum_cons]
    rfl

private theorem list_sum_le {l : List (ℕ × ℕ)} {f g : ℕ × ℕ → ℕ} (h : ∀ e ∈ l, f e ≤ g e) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h e List.mem_cons_self)
      (ih fun e' he' => h e' (List.mem_cons_of_mem _ he'))

/-- The budget of an odd prime `g`: weights of distinct components plus one for each further
component sending to `g` add up to at most `v_g(N)`. -/
private theorem budget {N g : ℕ} (hN : N.Perfect) (hg : g.Prime) (hg2 : g ≠ 2)
    (cs : List (ℕ × ℕ))
    (hcs : ∀ e ∈ cs, e.1 ∈ N.primeFactors ∧ g ^ e.2 ∣ σ 1 (e.1 ^ N.factorization e.1))
    (hnd : (cs.map Prod.fst).Nodup) (F : Finset ℕ) (hF : F ⊆ N.primeFactors)
    (hFd : ∀ t ∈ F, g ∣ σ 1 (t ^ N.factorization t)) (hdisj : ∀ t ∈ F, t ∉ cs.map Prod.fst) :
    csum cs + F.card ≤ N.factorization g := by
  classical
  have hsig : ∀ c, c ∈ N.primeFactors → σ 1 (c ^ N.factorization c) ≠ 0 := fun c hc =>
    (sigma_pos 1 _ (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hc).ne_zero)).ne'
  have h1 : csum cs ≤ ((cs.map Prod.fst).toFinset).sum fun c => sigmaWeight N c g := by
    rw [csum_eq, List.sum_toFinset _ hnd, List.map_map]
    exact list_sum_le fun e he =>
      (hg.pow_dvd_iff_le_factorization (hsig _ (hcs e he).1)).mp (hcs e he).2
  have h2 : F.card ≤ F.sum fun t => sigmaWeight N t g := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun t ht =>
      (hg.dvd_iff_one_le_factorization (hsig t (hF ht))).mp (hFd t ht)
  have hdj : Disjoint (cs.map Prod.fst).toFinset F := by
    rw [Finset.disjoint_left]
    intro c hc hcF
    exact hdisj c hcF (List.mem_toFinset.mp hc)
  have hsub : (cs.map Prod.fst).toFinset ∪ F ⊆ N.primeFactors := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
      exact (hcs e he).1
    · exact hF hc
  have h3 : (((cs.map Prod.fst).toFinset ∪ F).sum fun t => sigmaWeight N t g) ≤
      N.primeFactors.sum fun t => sigmaWeight N t g :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _
  rw [Finset.sum_union hdj, sigmaWeight_sum_eq hN hg hg2] at h3
  omega

/-! ## Exceptions -/

private def isExc (k : Key) : Bool := match k.role with | .fr false _ _ _ _ => true | _ => false

private theorem nexc_eq (ks : List Key) : nexc ks = (ks.filter isExc).length := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    rcases k with ⟨p, r, cs⟩
    cases r with
    | sq => simp [nexc, isExc, ih]
    | fr i D n3 km ex =>
      cases i
      · simp [nexc, isExc, ih, List.filter_cons]; omega
      · simp [nexc, isExc, ih]

/-- Non key exceptions and exception keys together are at most `E`. -/
private theorem exc_card {P : Params} {N q : ℕ} {ks : List Key} {x : ℕ} (hH : Holds P N q ks x)
    (X : Finset ℕ)
    (hX : ∀ t ∈ X, t ∈ N.primeFactors ∧ t ∉ ks.map Key.p ∧ t ≠ q ∧ N.factorization t ≠ 2) :
    X.card + nexc ks ≤ P.E := by
  classical
  obtain ⟨⟨hN, -, -, -, hcard, -⟩, hK, hnd, -⟩ := hH
  set XK := ((ks.filter isExc).map Key.p).toFinset with hXK
  have hndX : ((ks.filter isExc).map Key.p).Nodup :=
    hnd.sublist (List.filter_sublist.map Key.p)
  have hXKc : XK.card = nexc ks := by rw [hXK, List.toFinset_card_of_nodup hndX, List.length_map,
    nexc_eq]
  have hdj : Disjoint X XK := by
    rw [Finset.disjoint_left]
    intro t ht htK
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp htK)
    exact (hX _ ht).2.1 (List.mem_map.mpr ⟨k, (List.mem_filter.mp hk).1, rfl⟩)
  have hsub : X ∪ XK ⊆ N.primeFactors.filter fun p => p ≠ q ∧ N.factorization p ≠ 2 := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · exact Finset.mem_filter.mpr ⟨(hX t ht).1, (hX t ht).2.2⟩
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
      obtain ⟨hkm, hke⟩ := List.mem_filter.mp hk
      obtain ⟨hp, hpN, hr, -, -⟩ := hK k hkm
      rcases k with ⟨p, r, cs⟩
      simp only at hp hpN hr ⊢
      cases r with
      | sq => simp [isExc] at hke
      | fr i D n3 km ex =>
        cases i
        · obtain ⟨hiq, -, -, -, -, -, hev⟩ := hr
          refine Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpN, hN.ne_zero⟩, ?_, ?_⟩
          · intro hpq; exact absurd (hiq.mpr hpq) (by decide)
          · have := (hev rfl).2; omega
        · simp [isExc] at hke
  have := (Finset.card_le_card hsub).trans hcard
  rw [Finset.card_union_of_disjoint hdj, hXKc] at this
  exact this

private theorem qDec_key {N q : ℕ} {ks : List Key} (hK : ∀ k ∈ ks, KeyHolds N q ks k)
    (h : qDec ks = true) : q ∈ ks.map Key.p := by
  unfold qDec at h
  obtain ⟨k, hk, hr⟩ := List.any_eq_true.mp h
  obtain ⟨-, -, hrole, -, -⟩ := hK k hk
  rcases k with ⟨p, r, cs⟩
  simp only at hr hrole
  cases r with
  | sq => simp at hr
  | fr i D n3 km ex =>
    cases i
    · simp at hr
    · exact List.mem_map.mpr ⟨_, hk, hrole.1.mp rfl⟩

private def uOf (P : Params) (ks : List Key) : ℕ := (if qDec ks then 0 else 1) + (P.E - nexc ks)

/-- The free non keys are at most `u`. -/
private theorem card_U {P : Params} {N q : ℕ} {ks : List Key} {x : ℕ} (hH : Holds P N q ks x)
    (U : Finset ℕ)
    (hU : ∀ t ∈ U, t ∈ N.primeFactors ∧ t ∉ ks.map Key.p ∧ (t = q ∨ N.factorization t ≠ 2)) :
    U.card ≤ uOf P ks := by
  classical
  have h1 := exc_card hH (U.filter (· ≠ q)) fun t ht => by
    obtain ⟨htU, htq⟩ := Finset.mem_filter.mp ht
    obtain ⟨a, b, c⟩ := hU t htU
    exact ⟨a, b, htq, c.resolve_left htq⟩
  have h2 : (U.filter (· = q)).card ≤ if qDec ks then 0 else 1 := by
    split_ifs with hq
    · have hqk := qDec_key hH.2.1 hq
      refine Nat.le_zero.mpr (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr ?_))
      intro t ht htq
      subst htq
      exact (hU _ ht).2.1 hqk
    · refine (Finset.card_le_card (t := {q}) ?_).trans (by simp)
      intro t ht
      rw [Finset.mem_singleton]
      exact (Finset.mem_filter.mp ht).2
  have h3 : U.card ≤ (U.filter (· = q)).card + (U.filter (· ≠ q)).card :=
    (Finset.card_le_card (fun t ht => by
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases h : t = q
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr ⟨ht, h⟩)).trans
      (Finset.card_union_le _ _)
  unfold uOf
  split_ifs at h2 ⊢ <;> omega

/-! ## The ratio of the keys -/

private theorem abund_sq {p : ℕ} (hp : p.Prime) : abundancy (p ^ 2) = fv p := by
  unfold abundancy fv
  rw [sigma_prime_sq hp]
  unfold phi3
  push_cast
  ring

private theorem abund_nonneg (n : ℕ) : 0 ≤ abundancy n := by unfold abundancy; positivity

private theorem sig_eq {p e : ℕ} (hp : p.Prime) : sig p e = σ 1 (p ^ e) := by
  rw [sigma_one_apply_prime_pow hp, Nat.geomSum_eq hp.two_le]
  rfl

private theorem hiPair_bound (P : Params) {k : Key} {N q : ℕ} (hp : k.p.Prime)
    (hr : RoleHolds k.role (N.factorization k.p) (k.p = q)) :
    0 < (hiPair P k).2 ∧
      abundancy (k.p ^ N.factorization k.p) ≤ ((hiPair P k).1 : ℚ) / (hiPair P k).2 := by
  rcases k with ⟨p, r, cs⟩
  simp only at hp hr ⊢
  cases r with
  | sq =>
    obtain ⟨-, hv⟩ := hr
    refine ⟨Nat.mul_pos hp.pos hp.pos, ?_⟩
    rw [hv, abund_sq hp]
    unfold fv
    simp only [hiPair]
    push_cast
    try (apply le_of_eq; ring)
  | fr i D n3 kmin ex =>
    obtain ⟨-, -, -, -, hex, -, -⟩ := hr
    simp only [hiPair]
    split_ifs with h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rw [hex h.1]
      refine ⟨pow_pos hp.pos _, ?_⟩
      unfold abundancy
      rw [sig_eq hp]
    · refine ⟨by have := hp.two_le; omega, ?_⟩
      have := abundancy_prime_pow_lt hp (N.factorization p)
      rw [Nat.cast_sub hp.one_lt.le]
      push_cast
      exact this.le

private theorem hiProd_bound (P : Params) {N q : ℕ} : ∀ (ks : List Key),
    (∀ k ∈ ks, k.p.Prime ∧ RoleHolds k.role (N.factorization k.p) (k.p = q)) →
    (ks.map Key.p).Nodup →
    0 < (hiProd P ks).2 ∧ ∏ g ∈ (ks.map Key.p).toFinset, abundancy (g ^ N.factorization g) ≤
      ((hiProd P ks).1 : ℚ) / (hiProd P ks).2
  | [], _, _ => by simp [hiProd]
  | k :: ks, h, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨h1, h2⟩ := hiPair_bound P (h k List.mem_cons_self).1 (h k List.mem_cons_self).2
    obtain ⟨h3, h4⟩ := hiProd_bound P ks (fun k' hk' => h k' (List.mem_cons_of_mem k hk')) hnd.2
    simp only [hiProd]
    refine ⟨Nat.mul_pos h1 h3, ?_⟩
    rw [List.map_cons, List.toFinset_cons, Finset.prod_insert (by simpa using hnd.1)]
    push_cast
    rw [mul_div_mul_comm]
    exact mul_le_mul h2 h4 (Finset.prod_nonneg fun _ _ => abund_nonneg _)
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

private theorem ab_le_x {t x e : ℕ} (ht : t.Prime) (hx : 2 ≤ x) (hxt : x ≤ t) :
    abundancy (t ^ e) ≤ (x : ℚ) / (x - 1) := by
  have h := abundancy_prime_pow_lt ht e
  have hx' : (2 : ℚ) ≤ x := by exact_mod_cast hx
  have hxt' : (x : ℚ) ≤ t := by exact_mod_cast hxt
  refine h.le.trans ?_
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

private theorem fv_anti {x t : ℕ} (hx : 1 ≤ x) (hxt : x ≤ t) : fv t ≤ fv x := by
  have hx' : (1 : ℚ) ≤ x := by exact_mod_cast hx
  have hxt' : (x : ℚ) ≤ t := by exact_mod_cast hxt
  unfold fv
  rw [div_le_div_iff₀ (pow_pos (by linarith) 2) (pow_pos (by linarith) 2)]
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℚ) ≤ x) (by linarith : (0 : ℚ) ≤ t))
    (sub_nonneg.mpr hxt'), mul_nonneg (sub_nonneg.mpr hxt') (by linarith : (0 : ℚ) ≤ t + x)]

private theorem one_le_fv' {s : ℕ} (hs : 1 ≤ s) : 1 ≤ fv s := by
  have hs' : (1 : ℚ) ≤ s := by exact_mod_cast hs
  unfold fv
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-! ## The capacity of slot (d) -/

private def dcK (k : Key) : ℕ :=
  if k.p % 3 == 1 then
    match k.role with
    | .sq => 2 - csum k.cs
    | .fr _ _ _ kmin ex => if ex then kmin - csum k.cs else 0
  else 0

private theorem dCap_cons (k : Key) (ks : List Key) : dCap (k :: ks) = dcK k + dCap ks := by
  rw [dCap]; rfl

private theorem sum_le_dCap : ∀ (ks : List Key), (ks.map Key.p).Nodup → ∀ (S : Finset ℕ),
    S ⊆ (ks.map Key.p).toFinset → ∀ f : ℕ → ℕ, (∀ k ∈ ks, k.p ∈ S → f k.p ≤ dcK k) →
    S.sum f ≤ dCap ks := by
  classical
  intro ks
  induction ks with
  | nil =>
    intro _ S hS f _
    have : S = ∅ := Finset.subset_empty.mp (by simpa using hS)
    rw [this]; simp
  | cons k ks ih =>
    intro hnd S hS f hf
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [dCap_cons]
    have hS' : S.erase k.p ⊆ (ks.map Key.p).toFinset := by
      intro g hg
      obtain ⟨hgk, hgS⟩ := Finset.mem_erase.mp hg
      have := hS hgS
      rw [List.map_cons, List.toFinset_cons, Finset.mem_insert] at this
      exact this.resolve_left hgk
    have h2 := ih hnd.2 (S.erase k.p) hS' f fun k' hk' hk'S =>
      hf k' (List.mem_cons_of_mem _ hk') (Finset.mem_of_mem_erase hk'S)
    by_cases hk : k.p ∈ S
    · rw [← Finset.add_sum_erase S f hk]
      exact Nat.add_le_add (hf k List.mem_cons_self hk) h2
    · rw [Finset.erase_eq_of_notMem hk] at h2
      omega

/-! ## The generators -/

private theorem mem_genK {ks : List Key} {g : ℕ} :
    g ∈ genK ks ↔ ∃ k ∈ ks, k.p = g ∧ (∃ i D n3 km, k.role = .fr i D n3 km false) ∧
      k.p % 3 = 1 := by
  unfold genK
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨k, hk, h⟩
    rcases k with ⟨p, r, cs⟩
    cases r with
    | sq => simp at h
    | fr i D n3 km ex =>
      cases ex
      · simp only at h
        by_cases h3 : (p % 3 == 1) = true
        · rw [if_pos h3, Option.some.injEq] at h
          exact ⟨_, hk, h, ⟨i, D, n3, km, rfl⟩, by simpa using h3⟩
        · rw [if_neg h3] at h; cases h
      · simp at h
  · rintro ⟨k, hk, rfl, ⟨i, D, n3, km, heq⟩, h3⟩
    refine ⟨k, hk, ?_⟩
    rw [heq]
    simp [h3]

private theorem genK_sublist : ∀ ks : List Key, (genK ks).Sublist (ks.map Key.p)
  | [] => by simp [genK]
  | k :: ks => by
    have ih := genK_sublist ks
    unfold genK at ih ⊢
    rw [List.filterMap_cons, List.map_cons]
    rcases k with ⟨p, r, cs⟩
    cases r with
    | sq => exact ih.cons _
    | fr i D n3 km ex =>
      cases ex
      · simp only
        by_cases h3 : (p % 3 == 1) = true
        · rw [if_pos h3]; exact ih.cons_cons _
        · rw [if_neg h3]; exact ih.cons _
      · exact ih.cons _

/-! ## The weights -/

private def rOf : List ℕ → List ℕ → ℕ → ℕ
  | g :: gs, r :: rs, y => if y = g then r else rOf gs rs y
  | _, _, _ => 0

private theorem alpha_facts {k B : ℕ} : ∀ (gs rs : List ℕ), alphaOK k B gs rs = true →
    gs.Nodup →
    (∀ g ∈ gs, B < rOf gs rs g ∧ rOf gs rs g ^ k ≤ B ^ k * g) ∧ 0 < (rs.map (· - B)).prod ∧
    ∏ g ∈ gs.toFinset, (1 / (1 - (B : ℚ) / rOf gs rs g)) =
      ((rs.prod : ℕ) : ℚ) / (((rs.map (· - B)).prod : ℕ) : ℚ)
  | [], [], _, _ => by simp
  | g :: gs, r :: rs, h, hnd => by
    simp only [alphaOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hBr, hrk⟩, h'⟩ := h
    rw [List.nodup_cons] at hnd
    obtain ⟨ih1, ih0, ih2⟩ := alpha_facts gs rs h' hnd.2
    have e : ∀ y ∈ gs, rOf (g :: gs) (r :: rs) y = rOf gs rs y := fun y hy => by
      simp only [rOf]
      rw [if_neg (show ¬ y = g from fun h => hnd.1 (h ▸ hy))]
    have eg : rOf (g :: gs) (r :: rs) g = r := by simp [rOf]
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · rw [eg]; exact ⟨hBr, hrk⟩
      · rw [e y hy]; exact ih1 y hy
    · simp only [List.map_cons, List.prod_cons]
      exact Nat.mul_pos (by omega) ih0
    · have e2 : ∏ y ∈ gs.toFinset, 1 / (1 - (B : ℚ) / rOf (g :: gs) (r :: rs) y) =
          ∏ y ∈ gs.toFinset, 1 / (1 - (B : ℚ) / rOf gs rs y) :=
        Finset.prod_congr rfl fun y hy => by rw [e y (List.mem_toFinset.mp hy)]
      rw [List.toFinset_cons, Finset.prod_insert (by simpa using hnd.1), eg, e2, ih2]
      simp only [List.map_cons, List.prod_cons]
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hBr.le]
      have hB' : (B : ℚ) < r := by exact_mod_cast hBr
      have hr : (0 : ℚ) < r := by linarith [(Nat.cast_nonneg B : (0 : ℚ) ≤ B)]
      have hrB : (0 : ℚ) < r - B := by linarith
      have e1 : 1 / (1 - (B : ℚ) / r) = r / (r - B) := by
        field_simp
      rw [e1, div_mul_div_comm]
  | [], _ :: _, h, _ => by simp [alphaOK] at h
  | _ :: _, [], h, _ => by simp [alphaOK] at h

/-! ## Counting the slots (c) and (d) -/

/-- The budget of 3 from its role: `budget3 r3 = some b3` gives `v_3(N) = b3`. -/
private theorem budget3_spec {r3 : Role} {b3 k : ℕ} {hq : Prop} (hr : RoleHolds r3 k hq)
    (hb : budget3 r3 = some b3) : k = b3 := by
  unfold budget3 at hb
  split at hb
  · cases hb; exact hr.2
  · cases hb; exact hr.2.2.2.2.1 rfl
  · cases hb

private theorem card_C3 {P : Params} {N q : ℕ} {ks : List Key} {x : ℕ} (hH : Holds P N q ks x)
    {r3 : Role} {b3 : ℕ} {cs3 : List (ℕ × ℕ)} (hk3 : (⟨3, r3, cs3⟩ : Key) ∈ ks)
    (hb : budget3 r3 = some b3) (C : Finset ℕ)
    (hC : ∀ t ∈ C, t ∈ N.primeFactors ∧ t ∉ ks.map Key.p ∧ N.factorization t = 2 ∧ t % 3 = 1) :
    C.card ≤ b3 - csum cs3 := by
  obtain ⟨⟨hN, -, -, -, -⟩, hK, -, -⟩ := hH
  obtain ⟨-, -, hr3, hcs, hcsnd⟩ := hK _ hk3
  simp only at hcs hcsnd hr3
  have h3 := budget3_spec hr3 hb
  have := budget hN.perfect Nat.prime_three (by decide) cs3
    (fun e he => ⟨Nat.mem_primeFactors.mpr ⟨(hcs e he).1, (hcs e he).2.1, hN.ne_zero⟩,
      (hcs e he).2.2.2⟩) hcsnd C (fun t ht => (hC t ht).1)
    (fun t ht => by
      rw [(hC t ht).2.2.1, sigma_prime_sq (Nat.prime_of_mem_primeFactors (hC t ht).1)]
      exact (three_dvd_phi3_iff t).2 (hC t ht).2.2.2)
    (fun t ht hmem => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmem
      exact (hC _ ht).2.1 (hcs e he).2.2.1)
  omega

private theorem key_fiber {P : Params} {N q : ℕ} {ks : List Key} {x : ℕ} (hH : Holds P N q ks x)
    {k : Key} (hk : k ∈ ks) (hk2 : k.p ≠ 2) (F : Finset ℕ)
    (hF : ∀ t ∈ F, t ∈ N.primeFactors ∧ t ∉ ks.map Key.p ∧ k.p ∣ σ 1 (t ^ N.factorization t)) :
    csum k.cs + F.card ≤ N.factorization k.p := by
  obtain ⟨⟨hN, -, -, -, -⟩, hK, -, -⟩ := hH
  obtain ⟨hp, -, -, hcs, hcsnd⟩ := hK _ hk
  exact budget hN.perfect hp hk2 k.cs
    (fun e he => ⟨Nat.mem_primeFactors.mpr ⟨(hcs e he).1, (hcs e he).2.1, hN.ne_zero⟩,
      (hcs e he).2.2.2⟩) hcsnd F (fun t ht => (hF t ht).1) (fun t ht => (hF t ht).2.2)
    (fun t ht hmem => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmem
      exact (hF _ ht).2.1 (hcs e he).2.2.1)

/-- Slot (d): rows of squares that use the budget of a square prime or an exact free prime
`≡ 1 (mod 3)`. -/
private theorem card_D {P : Params} {N q : ℕ} {ks : List Key} {x : ℕ} (hH : Holds P N q ks x)
    (C3 : Finset ℕ) (hC3 : ∀ g ∈ C3, g ∈ N.primeFactors ∧ N.factorization g = 2) (D : Finset ℕ)
    (hD : ∀ t ∈ D, t ∈ N.primeFactors ∧ t ∉ ks.map Key.p ∧ N.factorization t = 2 ∧
      ∃ g ∈ N.primeFactors, (g % 3 = 1 ∧ (g ∈ C3 ∨ ∃ k ∈ ks, k.p = g ∧
        (k.role = .sq ∨ ∃ i D' n3 km, k.role = .fr i D' n3 km true))) ∧ g ∣ phi3 t) :
    D.card ≤ dCap ks + 2 * C3.card := by
  classical
  have hN := hH.1.1
  have hnd := hH.2.2.1
  set W := N.primeFactors.filter fun g => g % 3 = 1 ∧ (g ∈ C3 ∨ ∃ k ∈ ks, k.p = g ∧
        (k.role = .sq ∨ ∃ i D' n3 km, k.role = .fr i D' n3 km true)) with hW
  have hsub : D ⊆ W.biUnion fun g => D.filter fun t => g ∣ phi3 t := by
    intro t ht
    obtain ⟨-, -, -, g, hg, hgW, hgd⟩ := hD t ht
    exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_filter.mpr ⟨hg, hgW⟩,
      Finset.mem_filter.mpr ⟨ht, hgd⟩⟩
  have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  rw [← Finset.sum_filter_add_sum_filter_not W (fun g => g ∈ C3)] at h1
  have hfib : ∀ g ∈ N.primeFactors, g ≠ 2 → ∀ (F : Finset ℕ), F ⊆ D →
      (∀ t ∈ F, g ∣ phi3 t) → F.card ≤ N.factorization g := by
    intro g hg hg2 F hFD hFg
    have := budget hN.perfect (Nat.prime_of_mem_primeFactors hg) hg2 [] (by simp) (by simp) F
      (fun t ht => (hD t (hFD ht)).1)
      (fun t ht => by
        rw [(hD t (hFD ht)).2.2.1, sigma_prime_sq (Nat.prime_of_mem_primeFactors (hD t (hFD ht)).1)]
        exact hFg t ht) (by simp)
    simpa [csum] using this
  have p1 : ∑ g ∈ W.filter (fun g => g ∈ C3), (D.filter fun t => g ∣ phi3 t).card ≤
      2 * C3.card := by
    calc ∑ g ∈ W.filter (fun g => g ∈ C3), (D.filter fun t => g ∣ phi3 t).card
        ≤ ∑ g ∈ W.filter (fun g => g ∈ C3), 2 := by
          refine Finset.sum_le_sum fun g hg => ?_
          obtain ⟨hgW, hgC⟩ := Finset.mem_filter.mp hg
          obtain ⟨hgN, hg3, -⟩ := Finset.mem_filter.mp hgW
          rw [← (hC3 g hgC).2]
          exact hfib g hgN (by omega) _ (Finset.filter_subset _ _)
            fun t ht => (Finset.mem_filter.mp ht).2
      _ = 2 * (W.filter (fun g => g ∈ C3)).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 2 * C3.card := Nat.mul_le_mul_left 2 (Finset.card_le_card fun g hg =>
          (Finset.mem_filter.mp hg).2)
  have p2 : ∑ g ∈ W.filter (fun g => g ∉ C3), (D.filter fun t => g ∣ phi3 t).card ≤ dCap ks := by
    refine sum_le_dCap ks hnd _ ?_ _ ?_
    · intro g hg
      obtain ⟨hgW, hgC⟩ := Finset.mem_filter.mp hg
      obtain ⟨-, -, h | ⟨k, hk, rfl, -⟩⟩ := Finset.mem_filter.mp hgW
      · exact absurd h hgC
      · exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨k, hk, rfl⟩)
    · intro k hk hkS
      obtain ⟨hgW, hgC⟩ := Finset.mem_filter.mp hkS
      obtain ⟨hgN, hg3, h | ⟨k', hk', hkp, hrole⟩⟩ := Finset.mem_filter.mp hgW
      · exact absurd h hgC
      have hkk : k' = k := List.inj_on_of_nodup_map hnd hk' hk hkp
      subst hkk
      have hfb := key_fiber hH hk (by omega) (D.filter fun t => k'.p ∣ phi3 t) fun t ht => by
        obtain ⟨htD, htg⟩ := Finset.mem_filter.mp ht
        refine ⟨(hD t htD).1, (hD t htD).2.1, ?_⟩
        rw [(hD t htD).2.2.1, sigma_prime_sq (Nat.prime_of_mem_primeFactors (hD t htD).1)]
        exact htg
      obtain ⟨-, -, hr, -, -⟩ := hH.2.1 k' hk'
      unfold dcK
      rw [if_pos (by simpa using hg3)]
      rcases hrole with h | ⟨i, D', n3, km, h⟩
      · rw [h] at hr ⊢
        have := hr.2
        simp only
        omega
      · rw [h] at hr ⊢
        have := hr.2.2.2.2.1 rfl
        simp only [if_true]
        omega
  omega

/-! ## The rational part -/

private def cdOf (ks : List Key) (b3 : ℕ) (cs3 : List (ℕ × ℕ)) : ℕ :=
  (b3 - csum cs3) + (dCap ks + 2 * (b3 - csum cs3))

/-- `S` of the tail bound as (numerator, denominator), computed as in `tailOK`. -/
private def sPair (P : Params) (ks : List Key) (x : ℕ) (dd : DefData) : ℕ × ℕ :=
  let B := dd.B
  let u := uOf P ks
  let Gn := dd.rs.prod
  let Gd := (dd.rs.map (· - B)).prod
  let gxn := dd.rx ^ u
  let gxd := (dd.rx - B) ^ u
  let t1n := dd.mL.1 * Gn * (gxn - gxd)
  let t1d := dd.mL.2 * Gd * gxd
  let t2n := dd.mM.1 * Gn
  let t2d := dd.mM.2 * Gd
  ((x + 1) ^ 2 * (t1n * t2d + t2n * t1d), x * x * (t1d * t2d))

private theorem tailOK_spec {P : Params} {ks : List Key} {x : ℕ} {dd : DefData}
    {b3 : ℕ} {cs3 : List (ℕ × ℕ)} {hn hd : ℕ} (h : tailOK P ks x dd b3 cs3 hn hd = true) :
    2 ≤ x ∧ 3 ≤ dd.k ∧ nexc ks ≤ P.E ∧ alphaOK dd.k dd.B (genK ks) dd.rs = true ∧
    dd.B < dd.rx ∧ dd.rx ^ dd.k ≤ dd.B ^ dd.k * x ∧ 0 < dd.mL.2 ∧ 0 < dd.mM.2 ∧
    dd.mL.2 ^ (2 * dd.k) ≤ dd.mL.1 ^ (2 * dd.k) * (x * x + x + 1) ^ (dd.k - 2) ∧
    dd.mM.2 ^ (2 * dd.k) ≤ dd.mM.1 ^ (2 * dd.k) * (max (x * x + x + 1) P.MHIT) ^ (dd.k - 2) ∧
    (sPair P ks x dd).1 < (sPair P ks x dd).2 ∧
    (hiProd P ks).1 * x ^ uOf P ks * (x * x + x + 1) ^ cdOf ks b3 cs3 * hn * (sPair P ks x dd).2 <
      2 * ((hiProd P ks).2 * (x - 1) ^ uOf P ks * x ^ (2 * cdOf ks b3 cs3) * hd *
        ((sPair P ks x dd).2 - (sPair P ks x dd).1)) := by
  unfold tailOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

private theorem S_eq (P : Params) (ks : List Key) (x : ℕ) (dd : DefData) (hx : 0 < x)
    (hB : dd.B < dd.rx) (hGd : 0 < (dd.rs.map (· - dd.B)).prod) (hmL : 0 < dd.mL.2)
    (hmM : 0 < dd.mM.2) :
    ((x + 1 : ℚ) / x) ^ 2 * ((dd.mL.1 : ℚ) / dd.mL.2 *
        (((dd.rs.prod : ℕ) : ℚ) / ((dd.rs.map (· - dd.B)).prod : ℕ)) *
        ((1 / (1 - (dd.B : ℚ) / dd.rx)) ^ uOf P ks - 1) +
      (dd.mM.1 : ℚ) / dd.mM.2 * (((dd.rs.prod : ℕ) : ℚ) / ((dd.rs.map (· - dd.B)).prod : ℕ))) =
    ((sPair P ks x dd).1 : ℚ) / (sPair P ks x dd).2 := by
  simp only [sPair]
  generalize uOf P ks = u
  generalize dd.rs.prod = Gn
  generalize (dd.rs.map (· - dd.B)).prod = Gd at hGd ⊢
  generalize dd.B = B at hB ⊢
  generalize dd.rx = rx at hB ⊢
  generalize dd.mL = mL at hmL ⊢
  generalize dd.mM = mM at hmM ⊢
  obtain ⟨a1, a2⟩ := mL
  obtain ⟨b1, b2⟩ := mM
  simp only at hmL hmM ⊢
  have hpow : (rx - B) ^ u ≤ rx ^ u := Nat.pow_le_pow_left (Nat.sub_le _ _) _
  push_cast [Nat.cast_sub hB.le, Nat.cast_sub hpow]
  have hB' : (B : ℚ) < rx := by exact_mod_cast hB
  have hrx : (0 : ℚ) < rx := lt_of_le_of_lt (Nat.cast_nonneg B) hB'
  have hrB : (0 : ℚ) < rx - B := by linarith
  have e1 : 1 / (1 - (B : ℚ) / rx) = rx / (rx - B) := by field_simp
  rw [e1, div_pow (rx : ℚ) _ u]
  have hx' : (0 : ℚ) < x := by exact_mod_cast hx
  have hGd' : (0 : ℚ) < Gd := by exact_mod_cast hGd
  have ha2 : (0 : ℚ) < a2 := by exact_mod_cast hmL
  have hb2 : (0 : ℚ) < b2 := by exact_mod_cast hmM
  have hp : (0 : ℚ) < (rx - B) ^ u := pow_pos hrB u
  generalize ((rx : ℚ) - B) ^ u = ρ at hp ⊢
  generalize ((rx : ℚ)) ^ u = Q
  field_simp

private theorem final_contra {H1 H2 x u cd hn hd Sn Sd : ℕ} (hx : 2 ≤ x) (hH2 : 0 < H2)
    (hhd : 0 < hd) (hS : Sn < Sd)
    (hlt : H1 * x ^ u * (x * x + x + 1) ^ cd * hn * Sd <
      2 * (H2 * (x - 1) ^ u * x ^ (2 * cd) * hd * (Sd - Sn)))
    (hprod : (2 : ℚ) ≤ (H1 : ℚ) / H2 * (((x : ℚ) / (x - 1)) ^ u * (fv x ^ cd *
      ((hn : ℚ) / hd * (1 / (1 - (Sn : ℚ) / Sd)))))) : False := by
  have hx' : (2 : ℚ) ≤ x := by exact_mod_cast hx
  have hx1 : (0 : ℚ) < x - 1 := by linarith
  have hx0 : (0 : ℚ) < x := by linarith
  have hH2' : (0 : ℚ) < H2 := by exact_mod_cast hH2
  have hhd' : (0 : ℚ) < hd := by exact_mod_cast hhd
  have hS' : (Sn : ℚ) < Sd := by exact_mod_cast hS
  have hSd : (0 : ℚ) < Sd := lt_of_le_of_lt (Nat.cast_nonneg Sn) hS'
  have hSS : (0 : ℚ) < Sd - Sn := sub_pos.mpr hS'
  have hlt' : ((H1 * x ^ u * (x * x + x + 1) ^ cd * hn * Sd : ℕ) : ℚ) <
      ((2 * (H2 * (x - 1) ^ u * x ^ (2 * cd) * hd * (Sd - Sn)) : ℕ) : ℚ) := by exact_mod_cast hlt
  push_cast [Nat.cast_sub (by omega : 1 ≤ x), Nat.cast_sub hS.le] at hlt'
  have e : (H1 : ℚ) / H2 * (((x : ℚ) / (x - 1)) ^ u * (fv x ^ cd *
      ((hn : ℚ) / hd * (1 / (1 - (Sn : ℚ) / Sd))))) =
      (H1 * x ^ u * (x * x + x + 1) ^ cd * hn * Sd) /
        (H2 * (x - 1) ^ u * x ^ (2 * cd) * hd * (Sd - Sn)) := by
    unfold fv
    rw [one_sub_div hSd.ne', one_div_div, div_pow, div_pow, ← pow_mul,
      show (x : ℚ) * x = x ^ 2 by ring]
    have hA : (0 : ℚ) < ((x : ℚ) - 1) ^ u := pow_pos hx1 u
    have hBq : (0 : ℚ) < (x : ℚ) ^ (2 * cd) := pow_pos hx0 _
    generalize ((x : ℚ) - 1) ^ u = A at hA ⊢
    generalize (x : ℚ) ^ (2 * cd) = Bq at hBq ⊢
    generalize ((x : ℚ) ^ 2 + x + 1) ^ cd = C
    generalize (x : ℚ) ^ u = X
    field_simp
  have hden : (0 : ℚ) < H2 * (x - 1) ^ u * x ^ (2 * cd) * hd * (Sd - Sn) :=
    mul_pos (mul_pos (mul_pos (mul_pos hH2' (pow_pos hx1 u)) (pow_pos hx0 _)) hhd') hSS
  rw [e, le_div_iff₀ hden] at hprod
  linarith

private theorem one_le_div_pow {a b c n : ℕ} (hb : 0 < b) (h : b ^ n ≤ a ^ n * c) :
    1 ≤ ((a : ℚ) / b) ^ n * c := by
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos hb' n), one_mul]
  exact_mod_cast h

/-! ## The deficient leaf -/

set_option maxHeartbeats 1000000 in
/-- **Soundness of the deficient leaf.** If the checker accepts a deficient leaf at the state
`(ks, x)`, then no member `N` of the family (with special prime `q`) satisfies that state. -/
theorem defSound (P : Params) : DefSound P := by
  classical
  intro ks x dd N q hdef hH
  have hH' := hH
  obtain ⟨⟨hN, -, -, -, -⟩, hK, hnd, hxk⟩ := hH'
  unfold deficientB at hdef
  split at hdef
  case h_2 => exact absurd hdef Bool.false_ne_true
  rename_i p3 r3 cs3 hfk
  split at hdef
  case h_2 => exact absurd hdef Bool.false_ne_true
  rename_i bud3 hb3
  obtain ⟨hk3, hp3⟩ := findKey_some hfk
  simp only at hp3
  subst hp3
  generalize hE : enumG P.MHIT (visit ks x dd.comps) (genK ks) 1 (true, 1, 1) = res at hdef
  obtain ⟨ok, hn, hd⟩ := res
  simp only [Bool.and_eq_true] at hdef
  obtain ⟨rfl, htail⟩ := hdef
  obtain ⟨hx2, hk, -, halpha, hBrx, hrxk, hmL2, hmM2, hmL, hmM, hSlt, hfin⟩ :=
    tailOK_spec htail
  have hN0 := hN.ne_zero
  set PF := N.primeFactors with hPF
  set KS := (ks.map Key.p).toFinset with hKS
  have hKSsub : KS ⊆ PF := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    obtain ⟨hp, hpN, -⟩ := hK k hk
    exact Nat.mem_primeFactors.mpr ⟨hp, hpN, hN0⟩
  have h3KS : (3 : ℕ) ∈ ks.map Key.p := List.mem_map.mpr ⟨_, hk3, rfl⟩
  set NK := PF \ KS with hNK
  have hNKm : ∀ t ∈ NK, t ∈ PF ∧ t.Prime ∧ t ∉ ks.map Key.p ∧ x ≤ t := by
    intro t ht
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp ht
    have htp := Nat.prime_of_mem_primeFactors h1
    have htk : t ∉ ks.map Key.p := fun h => h2 (List.mem_toFinset.mpr h)
    refine ⟨h1, htp, htk, ?_⟩
    by_contra hlt
    exact htk (hxk t htp (by omega) (Nat.dvd_of_mem_primeFactors h1))
  have hodd : ∀ t ∈ PF, t % 2 = 1 := fun t ht =>
    ((Nat.prime_of_mem_primeFactors ht).eq_two_or_odd).resolve_left fun h =>
      hN.not_two_dvd (h ▸ Nat.dvd_of_mem_primeFactors ht)
  have hrow : ∀ t ∈ PF, N.factorization t = 2 → ∀ g, g.Prime → g ∣ phi3 t → g ∈ PF := by
    intro t ht hv g hg hgd
    have hg2 : g ≠ 2 := by
      rintro rfl
      exact Nat.not_even_iff_odd.mpr (phi3_odd t) (even_iff_two_dvd.mpr hgd)
    refine mem_primeFactors_of_sigmaWeight_ne_zero hN.perfect ht hg2 ?_
    unfold sigmaWeight
    rw [hv, sigma_prime_sq (Nat.prime_of_mem_primeFactors ht)]
    have hne : phi3 t ≠ 0 := by unfold phi3; omega
    have := (hg.dvd_iff_one_le_factorization hne).mp hgd
    omega
  -- the classes
  set Ufs := NK.filter fun t => t = q ∨ N.factorization t ≠ 2 with hUfs
  set R1 := NK.filter fun t => ¬ (t = q ∨ N.factorization t ≠ 2) with hR1
  have hR1m : ∀ t ∈ R1, t ∈ PF ∧ t.Prime ∧ t ∉ ks.map Key.p ∧ x ≤ t ∧ t ≠ q ∧
      N.factorization t = 2 := by
    intro t ht
    obtain ⟨htN, hc⟩ := Finset.mem_filter.mp ht
    obtain ⟨a, b, c, d⟩ := hNKm t htN
    push Not at hc
    exact ⟨a, b, c, d, hc.1, hc.2⟩
  set C3 := R1.filter fun t => t % 3 = 1 with hC3
  set Wp : ℕ → Prop := fun g => g % 3 = 1 ∧ (g ∈ C3 ∨ ∃ k ∈ ks, k.p = g ∧
        (k.role = .sq ∨ ∃ i D' n3 km, k.role = .fr i D' n3 km true)) with hWp
  set CD := R1.filter fun t => t % 3 = 1 ∨ ∃ g ∈ PF, Wp g ∧ g ∣ phi3 t with hCD
  set R2 := R1.filter fun t => ¬ (t % 3 = 1 ∨ ∃ g ∈ PF, Wp g ∧ g ∣ phi3 t) with hR2
  set Kf := (genK ks).toFinset with hKf
  set Hits := R2.filter fun t => phi3 t < P.MHIT ∧ (phi3 t).primeFactors ⊆ Kf with hHits
  set T := R2.filter fun t => ¬ (phi3 t < P.MHIT ∧ (phi3 t).primeFactors ⊆ Kf) with hT
  have hR2m : ∀ t ∈ R2, t ∈ R1 ∧ t % 3 = 2 ∧ ∀ g ∈ PF, Wp g → ¬ g ∣ phi3 t := by
    intro t ht
    obtain ⟨htR, hc⟩ := Finset.mem_filter.mp ht
    push Not at hc
    obtain ⟨-, htp, htk, -⟩ := hR1m t htR
    have ht3 : t ≠ 3 := fun h => htk (h ▸ h3KS)
    have : t % 3 ≠ 0 := fun h => ht3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three htp).mp
      (Nat.dvd_of_mod_eq_zero h)).symm
    exact ⟨htR, by omega, hc.2⟩
  -- counts
  have cU : Ufs.card ≤ uOf P ks := card_U hH Ufs fun t ht => by
    obtain ⟨htN, hc⟩ := Finset.mem_filter.mp ht
    exact ⟨(hNKm t htN).1, (hNKm t htN).2.2.1, hc⟩
  have cC3 : C3.card ≤ bud3 - csum cs3 := card_C3 hH hk3 hb3 C3 fun t ht => by
    obtain ⟨htR, h1⟩ := Finset.mem_filter.mp ht
    obtain ⟨a, -, c, -, -, f⟩ := hR1m t htR
    exact ⟨a, c, f, h1⟩
  have cD : (R1.filter fun t => ¬ t % 3 = 1 ∧ ∃ g ∈ PF, Wp g ∧ g ∣ phi3 t).card ≤
      dCap ks + 2 * C3.card := by
    refine card_D hH C3 (fun g hg => ?_) _ fun t ht => ?_
    · obtain ⟨a, -, -, -, -, f⟩ := hR1m g (Finset.mem_filter.mp hg).1
      exact ⟨a, f⟩
    · obtain ⟨htR, -, hex⟩ := Finset.mem_filter.mp ht
      obtain ⟨a, -, c, -, -, f⟩ := hR1m t htR
      exact ⟨a, c, f, hex⟩
  have cCD : CD.card ≤ cdOf ks bud3 cs3 := by
    have hsub : CD ⊆ C3 ∪ R1.filter fun t => ¬ t % 3 = 1 ∧ ∃ g ∈ PF, Wp g ∧ g ∣ phi3 t := by
      intro t ht
      obtain ⟨htR, hc⟩ := Finset.mem_filter.mp ht
      by_cases h1 : t % 3 = 1
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨htR, h1⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨htR, h1, hc.resolve_left h1⟩)
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    unfold cdOf
    omega
  -- the product formula
  have hab : (2 : ℚ) = ∏ t ∈ PF, abundancy (t ^ N.factorization t) := by
    rw [← abundancy_eq_prod_primeFactors hN0]
    exact ((perfect_iff_abundancy_eq_two hN.pos).mp hN.perfect).symm
  have s1 : ∏ t ∈ PF, abundancy (t ^ N.factorization t) =
      (∏ t ∈ NK, abundancy (t ^ N.factorization t)) * ∏ t ∈ KS, abundancy (t ^ N.factorization t) :=
    (Finset.prod_sdiff hKSsub).symm
  have s2 : ∏ t ∈ NK, abundancy (t ^ N.factorization t) =
      (∏ t ∈ Ufs, abundancy (t ^ N.factorization t)) * ∏ t ∈ R1, abundancy (t ^ N.factorization t) :=
    (Finset.prod_filter_mul_prod_filter_not NK _ _).symm
  have s3 : ∏ t ∈ R1, abundancy (t ^ N.factorization t) = ∏ t ∈ R1, fv t :=
    Finset.prod_congr rfl fun t ht => by
      rw [(hR1m t ht).2.2.2.2.2, abund_sq (hR1m t ht).2.1]
  have s4 : ∏ t ∈ R1, fv t = (∏ t ∈ CD, fv t) * ∏ t ∈ R2, fv t :=
    (Finset.prod_filter_mul_prod_filter_not R1 _ _).symm
  have s5 : ∏ t ∈ R2, fv t = (∏ t ∈ Hits, fv t) * ∏ t ∈ T, fv t :=
    (Finset.prod_filter_mul_prod_filter_not R2 _ _).symm
  rw [s1, s2, s3, s4, s5] at hab
  -- the bounds
  have hx' : (2 : ℚ) ≤ x := by exact_mod_cast hx2
  obtain ⟨hH2, b1⟩ := hiProd_bound P ks (fun k hk => ⟨(hK k hk).1, (hK k hk).2.2.1⟩) hnd
  have b2 : ∏ t ∈ Ufs, abundancy (t ^ N.factorization t) ≤ ((x : ℚ) / (x - 1)) ^ uOf P ks := by
    have h1 : (1 : ℚ) ≤ x / (x - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
    calc ∏ t ∈ Ufs, abundancy (t ^ N.factorization t) ≤ ∏ t ∈ Ufs, ((x : ℚ) / (x - 1)) :=
          Finset.prod_le_prod (fun _ _ => abund_nonneg _) fun t ht => by
            obtain ⟨-, htp, -, hxt⟩ := hNKm t (Finset.mem_filter.mp ht).1
            exact ab_le_x htp hx2 hxt
      _ = ((x : ℚ) / (x - 1)) ^ Ufs.card := Finset.prod_const _
      _ ≤ _ := pow_le_pow_right₀ h1 cU
  have b3 : ∏ t ∈ CD, fv t ≤ fv x ^ cdOf ks bud3 cs3 := by
    calc ∏ t ∈ CD, fv t ≤ ∏ t ∈ CD, fv x :=
          Finset.prod_le_prod (fun t _ => fv_nonneg t) fun t ht =>
            fv_anti (by omega) (hR1m t (Finset.mem_filter.mp ht).1).2.2.2.1
      _ = fv x ^ CD.card := Finset.prod_const _
      _ ≤ _ := pow_le_pow_right₀ (one_le_fv' (by omega)) cCD
  have hgK : ∀ g ∈ genK ks, 2 ≤ g := fun g hg => by
    obtain ⟨k, hk, rfl, -⟩ := mem_genK.mp hg
    exact (hK k hk).1.two_le
  obtain ⟨hhd, b4⟩ := enum_hits hgK hE Hits fun t ht => by
    obtain ⟨htR2, hhit⟩ := Finset.mem_filter.mp ht
    obtain ⟨htR1, ht3, -⟩ := hR2m t htR2
    obtain ⟨htP, htp, htk, hxt, -, -⟩ := hR1m t htR1
    refine ⟨⟨htp, hxt, ht3, ?_, hodd t htP⟩, hhit⟩
    cases h : isKey ks t
    · rfl
    · exact absurd ((isKey_iff ks t).mp h) htk
  -- Rankin
  have hndK : (genK ks).Nodup := hnd.sublist (genK_sublist ks)
  obtain ⟨hal1, hGd, hG⟩ := alpha_facts (k := dd.k) (B := dd.B) (genK ks) dd.rs halpha hndK
  have hpf : ∀ t ∈ R2, ∀ g ∈ (phi3 t).primeFactors, g ∈ Kf ∨ g ∈ Ufs := by
    intro t ht g hg
    obtain ⟨htR1, ht3, hW⟩ := hR2m t ht
    obtain ⟨htP, htp, htk, hxt, -, hv⟩ := hR1m t htR1
    have hgp := Nat.prime_of_mem_primeFactors hg
    have hgd := Nat.dvd_of_mem_primeFactors hg
    have hgP := hrow t htP hv g hgp hgd
    have hg3 : g ≠ 3 := by
      rintro rfl
      have := (three_dvd_phi3_iff t).1 hgd
      omega
    have hg1 := prime_dvd_phi3_mod_three hgp hg3 hgd
    by_cases hgK : g ∈ ks.map Key.p
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hgK
      rcases k with ⟨p, r, cs⟩
      cases r with
      | sq => exact absurd hgd (hW _ hgP ⟨hg1, Or.inr ⟨_, hk, rfl, Or.inl rfl⟩⟩)
      | fr i D' n3 km ex =>
        cases ex
        · exact Or.inl (List.mem_toFinset.mpr (mem_genK.mpr ⟨_, hk, rfl, ⟨i, D', n3, km, rfl⟩, hg1⟩))
        · exact absurd hgd (hW _ hgP ⟨hg1, Or.inr ⟨_, hk, rfl, Or.inr ⟨i, D', n3, km, rfl⟩⟩⟩)
    · have hgNK : g ∈ NK := Finset.mem_sdiff.mpr ⟨hgP, fun h => hgK (List.mem_toFinset.mp h)⟩
      by_cases hgU : g = q ∨ N.factorization g ≠ 2
      · exact Or.inr (Finset.mem_filter.mpr ⟨hgNK, hgU⟩)
      · have hgC : g ∈ C3 := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hgNK, hgU⟩, hg1⟩
        exact absurd hgd (hW _ hgP ⟨hg1, Or.inl hgC⟩)
  have hSd : 0 < (sPair P ks x dd).2 := lt_of_le_of_lt (Nat.zero_le _) hSlt
  have b5 : ∏ t ∈ T, fv t ≤ 1 / (1 - ((sPair P ks x dd).1 : ℚ) / (sPair P ks x dd).2) := by
    refine prod_fv_le_of_rankin_tail_general T Kf Ufs (x := x) (k := dd.k)
      (M := max (x * x + x + 1) P.MHIT) (u := uOf P ks)
      (α := fun g => (dd.B : ℚ) / rOf (genK ks) dd.rs g) (αx := (dd.B : ℚ) / dd.rx)
      (mL := (dd.mL.1 : ℚ) / dd.mL.2) (mM := (dd.mM.1 : ℚ) / dd.mM.2) hx2 (by omega) ?_ cU
      (fun g _ => by positivity) (fun g hg => ?_) (fun g hg => ?_) (by positivity) ?_ ?_
      (fun g hg => (hNKm g (Finset.mem_filter.mp hg).1).2.2.2) (by positivity) ?_ (by positivity)
      ?_ ?_ (le_of_eq ?_) ?_
    · rw [Finset.disjoint_left]
      intro g hgK hgU
      obtain ⟨k, hk, rfl, -⟩ := mem_genK.mp (List.mem_toFinset.mp hgK)
      exact (hNKm _ (Finset.mem_filter.mp hgU).1).2.2.1 (List.mem_map.mpr ⟨k, hk, rfl⟩)
    · obtain ⟨h1, -⟩ := hal1 g (List.mem_toFinset.mp hg)
      exact (div_lt_one (by exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) h1)).mpr
        (by exact_mod_cast h1)
    · obtain ⟨h1, h2⟩ := hal1 g (List.mem_toFinset.mp hg)
      exact one_le_div_pow (lt_of_le_of_lt (Nat.zero_le _) h1) h2
    · exact (div_lt_one (by exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) hBrx)).mpr
        (by exact_mod_cast hBrx)
    · exact one_le_div_pow (lt_of_le_of_lt (Nat.zero_le _) hBrx) hrxk
    · have e : x ^ 2 + x + 1 = x * x + x + 1 := by ring
      have h := one_le_div_pow hmL2 hmL
      rw [Nat.cast_pow] at h
      rw [e]
      exact h
    · have h := one_le_div_pow hmM2 hmM
      rw [Nat.cast_pow] at h
      exact h
    · intro t ht
      obtain ⟨htR2, hnh⟩ := Finset.mem_filter.mp ht
      obtain ⟨htR1, -, -⟩ := hR2m t htR2
      obtain ⟨-, -, -, hxt, -, -⟩ := hR1m t htR1
      refine ⟨hxt, fun g hg => Finset.mem_union.mpr (hpf t htR2 g hg), fun hno => ?_⟩
      have hsubK : (phi3 t).primeFactors ⊆ Kf := fun g hg =>
        (hpf t htR2 g hg).resolve_right fun hgU => hno g hgU (Nat.dvd_of_mem_primeFactors hg)
      have hM : P.MHIT ≤ phi3 t := by
        by_contra hlt
        exact hnh ⟨by omega, hsubK⟩
      have hL : x * x + x + 1 ≤ phi3 t := by
        have e : x * x + x + 1 = phi3 x := by unfold phi3; ring
        rw [e]
        exact phi3_strictMono.monotone hxt
      exact max_le hL hM
    · rw [hG]
      exact S_eq P ks x dd (by omega) hBrx hGd hmL2 hmM2
    · rw [div_lt_one (by exact_mod_cast hSd)]
      exact_mod_cast hSlt
  -- assembly
  have n4 : 0 ≤ ∏ t ∈ T, fv t := Finset.prod_nonneg fun t _ => fv_nonneg t
  have n3 : 0 ≤ ∏ t ∈ Hits, fv t := Finset.prod_nonneg fun t _ => fv_nonneg t
  have n2 : 0 ≤ ∏ t ∈ CD, fv t := Finset.prod_nonneg fun t _ => fv_nonneg t
  have n1 : 0 ≤ ∏ t ∈ Ufs, abundancy (t ^ N.factorization t) :=
    Finset.prod_nonneg fun t _ => abund_nonneg _
  have hprod : (2 : ℚ) ≤ ((hiProd P ks).1 : ℚ) / (hiProd P ks).2 *
      (((x : ℚ) / (x - 1)) ^ uOf P ks * (fv x ^ cdOf ks bud3 cs3 *
        ((hn : ℚ) / hd * (1 / (1 - ((sPair P ks x dd).1 : ℚ) / (sPair P ks x dd).2))))) := by
    rw [hab, mul_comm]
    have hx1 : (0 : ℚ) ≤ (x : ℚ) / (x - 1) := div_nonneg (by linarith) (by linarith)
    exact mul_le_mul b1
      (mul_le_mul b2 (mul_le_mul b3 (mul_le_mul b4 b5 n4 (by positivity)) (mul_nonneg n3 n4)
        (pow_nonneg (fv_nonneg x) _)) (mul_nonneg n2 (mul_nonneg n3 n4)) (pow_nonneg hx1 _))
      (mul_nonneg n1 (mul_nonneg n2 (mul_nonneg n3 n4)))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  exact final_contra hx2 hH2 hhd hSlt hfin hprod

end TwoExcEngine

end OddPerfect

#print axioms OddPerfect.TwoExcEngine.defSound
