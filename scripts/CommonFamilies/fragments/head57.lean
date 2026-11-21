import OddPerfect.CommonFamily

/-!
# Common exponent families: `7 ∤ N` in the common `5` family

Let `N` be an odd perfect number with special prime `q`. A common `d` family means that `d`
divides `v_p(N) + 1` for every ordinary prime `p`. This file proves:

* primality by trial division up to the square root (`FamInst.sqPrime`);
* target forcing reach checks (`FamInst.reach`) whose blocked candidates are the source nodes
  satisfying an arbitrary Boolean predicate that holds at the special prime, with soundness
  `dvd_of_reach`; the kernel evaluates the bit mask at every step, and the reached mask is
  compared with the target mask once per blocked value, so the checks can be split into parts;
* an abundance checker `FamInst.abOK2` that compares every case with the two full products
  once, and the combined closer `false_of_reach`;
* in the common `5` family, `7 ∤ N` (known; Evans and Pearlman 2007).
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.EqChain (gm gm_eq)
open OddPerfect.CommonChain (maskOf testBit_maskOf)
open OddPerfect.CommonFam (geomS pPow pSig expL not_perfect_of_pSig)

/-! ## Trial division up to the square root -/

/-- `tdiv q f m` checks with fuel `f` that no `k ≥ m` of the parity of `m` with `k * k ≤ q`
divides `q`. -/
def tdiv (q : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, m => decide (q < m * m) || (q % m != 0 && tdiv q f (m + 2))

/-- Soundness of `tdiv`. -/
theorem tdiv_sound {q : ℕ} : ∀ f m, tdiv q f m = true →
    ∀ k, m ≤ k → k % 2 = m % 2 → k * k ≤ q → q % k ≠ 0
  | 0, _, h => by simp [tdiv] at h
  | f + 1, m, h => by
    intro k hmk hpar hkq
    simp only [tdiv, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne,
      ne_eq] at h
    rcases h with h | ⟨h1, h2⟩
    · exact absurd (lt_of_lt_of_le h (Nat.mul_le_mul hmk hmk)) (not_lt.mpr hkq)
    · rcases Nat.eq_or_lt_of_le hmk with rfl | hlt
      · exact h1
      · exact tdiv_sound f (m + 2) h2 k (by omega) (by omega) hkq

/-- Primality by trial division over odd numbers up to the square root. -/
def sqPrime (q : ℕ) : Bool := decide (2 ≤ q) && (q == 2 || (q % 2 != 0 && tdiv q q 3))

/-- Soundness of `sqPrime`. -/
theorem sqPrime_sound {q : ℕ} (h : sqPrime q = true) : q.Prime := by
  simp only [sqPrime, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
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
  exact tdiv_sound q 3 ht _ hm3 (by omega) (by simpa [pow_two] using hsq)
    (Nat.mod_eq_zero_of_dvd hdvd)

/-- Primality: listed in an accepted Pratt certificate, or trial division up to the square
root. -/
def isPS (pc : List (ℕ × ℕ × List ℕ)) (r : ℕ) : Bool :=
  (pc.map Prod.fst).contains r || sqPrime r

/-- Soundness of `isPS`. -/
theorem isPS_sound {pc : List (ℕ × ℕ × List ℕ)} (hpc : Pratt.check pc = true) {r : ℕ}
    (h : isPS pc r = true) : r.Prime := by
  simp only [isPS, Bool.or_eq_true, List.contains_iff_mem, List.mem_map] at h
  rcases h with ⟨e, he, rfl⟩ | h
  · exact Pratt.check_sound hpc e he
  · exact sqPrime_sound h

/-! ## The target forcing checker with a candidate predicate -/

/-- One in order pass over the rows: row `i` is used when bit `i` of `M` is set and the source
node `x` differs from the blocked value `b`; it then sets the bits of its receivers. The test
selects the recursive call, so the kernel evaluates the mask at every step. -/
def fpass (b : ℕ) : ℕ → List ℕ → List (List ℕ) → ℕ → ℕ
  | _, [], _, M => M
  | _, _ :: _, [], M => M
  | i, x :: xs, row :: rs, M =>
    if M.testBit i && x != b then fpass b (i + 1) xs rs (M ||| maskOf row)
    else fpass b (i + 1) xs rs M

/-- At most `n` passes over the table, stopping once every bit of `tm` is set. -/
def fiter (b : ℕ) (nodes : List ℕ) (rows : List (List ℕ)) (tm : ℕ) : ℕ → ℕ → ℕ
  | 0, M => M
  | n + 1, M => if M &&& tm == tm then M else fiter b nodes rows tm n (fpass b 0 nodes rows M)

/-- Reading the head of a suffix. -/
theorem drop_facts {nodes xs : List ℕ} {i x : ℕ} (hd : nodes.drop i = x :: xs) :
    nodes.getD i 0 = x ∧ x ∈ nodes ∧ nodes.drop (i + 1) = xs := by
  refine ⟨?_, List.mem_of_mem_drop (hd ▸ List.mem_cons_self), ?_⟩
  · have := congrArg (fun l : List ℕ => l[0]?) hd
    simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at this
    rw [List.getD_eq_getElem?_getD, this, Option.getD_some]
  · rw [← List.drop_drop, hd, List.drop_one, List.tail_cons]

/-- A pass preserves the property that every set bit indexes a divisor of `N`. The source
nodes are the first `rows.length` nodes, and only their steps are needed. -/
theorem fpass_good {N r b : ℕ} {nodes : List ℕ} {rows : List (List ℕ)}
    (hstep : ∀ x ∈ nodes.take rows.length, x ∣ N → x ≠ b → ∀ t ∈ nodes, gm x t r = 0 → t ∣ N)
    (hgm0 : ∀ x ∈ nodes, gm x 0 r ≠ 0) :
    ∀ (xs : List ℕ) (rs : List (List ℕ)) (i M : ℕ), nodes.drop i = xs → rows.drop i = rs →
      (∀ e ∈ xs.zip rs, ∀ j ∈ e.2, gm e.1 (nodes.getD j 0) r = 0) →
      (∀ k, M.testBit k = true → nodes.getD k 0 ∣ N) →
      ∀ k, (fpass b i xs rs M).testBit k = true → nodes.getD k 0 ∣ N
  | [], _, _, _, _, _, _, hM => hM
  | _ :: _, [], _, _, _, _, _, hM => hM
  | x :: xs, row :: rs, i, M, hd, hr, hz, hM => by
    obtain ⟨hxi, hxn, hd'⟩ := drop_facts hd
    have hr' : rows.drop (i + 1) = rs := by
      rw [← List.drop_drop, hr, List.drop_one, List.tail_cons]
    have hi : i < rows.length := by
      by_contra hc
      rw [List.drop_eq_nil_of_le (by omega)] at hr
      exact List.cons_ne_nil _ _ hr.symm
    have hin : i < nodes.length := by
      by_contra hc
      rw [List.drop_eq_nil_of_le (by omega)] at hd
      exact List.cons_ne_nil _ _ hd.symm
    have hxs : x ∈ nodes.take rows.length := by
      rw [List.getD_eq_getElem _ _ hin] at hxi
      exact List.mem_take_iff_getElem.mpr ⟨i, by omega, hxi⟩
    have hz' := fun e he => hz e (List.mem_cons_of_mem _ he)
    rw [fpass]
    split_ifs with hc
    · refine fpass_good hstep hgm0 xs rs (i + 1) _ hd' hr' hz' ?_
      intro k hk
      rw [Nat.testBit_lor, Bool.or_eq_true, testBit_maskOf] at hk
      rcases hk with hk | hk
      · exact hM k hk
      simp only [Bool.and_eq_true, bne_iff_ne] at hc
      have hg := hz (x, row) List.mem_cons_self k hk
      have hxN : x ∣ N := hxi ▸ hM i hc.1
      by_cases hkl : k < nodes.length
      · rw [List.getD_eq_getElem _ _ hkl] at hg ⊢
        exact hstep x hxs hxN hc.2 _ (List.getElem_mem hkl) hg
      · rw [List.getD_eq_default _ _ (by omega)] at hg
        exact absurd hg (hgm0 x hxn)
    · exact fpass_good hstep hgm0 xs rs (i + 1) _ hd' hr' hz' hM

/-- `fiter` preserves the same property. -/
theorem fiter_good {N r b tm : ℕ} {nodes : List ℕ} {rows : List (List ℕ)}
    (hstep : ∀ x ∈ nodes.take rows.length, x ∣ N → x ≠ b → ∀ t ∈ nodes, gm x t r = 0 → t ∣ N)
    (hgm0 : ∀ x ∈ nodes, gm x 0 r ≠ 0)
    (hz : ∀ e ∈ nodes.zip rows, ∀ j ∈ e.2, gm e.1 (nodes.getD j 0) r = 0) :
    ∀ (n M : ℕ), (∀ k, M.testBit k = true → nodes.getD k 0 ∣ N) →
      ∀ k, (fiter b nodes rows tm n M).testBit k = true → nodes.getD k 0 ∣ N
  | 0, _, hM => hM
  | n + 1, M, hM => by
    rw [fiter]
    split_ifs
    · exact hM
    · exact fiter_good hstep hgm0 hz n _
        (fpass_good hstep hgm0 nodes rows 0 M List.drop_zero List.drop_zero hz hM)

/-- All bits of the target mask `tm` are reached from the seeds (the first `ns` nodes) by
`passes` in order passes, when the rows whose source equals `b` are never used. -/
def reach (nodes : List ℕ) (rows : List (List ℕ)) (ns tm passes b : ℕ) : Bool :=
  fiter b nodes rows tm passes (2 ^ ns - 1) &&& tm == tm

/-- The divisibility check of the rows: every receiver `t` of the row of `s` divides
`1 + s + ... + s ^ (d - 1)`. -/
def rowChk (d : ℕ) (nodes : List ℕ) (e : ℕ × List ℕ) : Bool :=
  e.2.all fun j => gm e.1 (nodes.getD j 0) d == 0

/-- A Boolean statement over a list follows from the same statement over its parts. -/
theorem all_of_parts {α : Type} {L : List α} {f : α → Bool} (parts : List (List α))
    (hL : L = parts.flatten) (hp : ∀ c ∈ parts, c.all f = true) : ∀ b ∈ L, f b = true := by
  subst hL
  intro b hb
  obtain ⟨c, hc, hbc⟩ := List.mem_flatten.mp hb
  exact List.all_eq_true.mp (hp c hc) b hbc

/-- Distinctness by a bit mask of the values seen so far. -/
def ndM : List ℕ → ℕ → Bool
  | [], _ => true
  | a :: l, M => !M.testBit a && ndM l (M ||| 2 ^ a)

/-- Soundness of `ndM`. -/
theorem nodup_of_ndM : ∀ {l : List ℕ} {M : ℕ}, ndM l M = true →
    l.Nodup ∧ ∀ x ∈ l, M.testBit x = false
  | [], _, _ => ⟨List.nodup_nil, fun _ hx => absurd hx List.not_mem_nil⟩
  | a :: l, M, h => by
    simp only [ndM, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hnd, hl⟩ := nodup_of_ndM h.2
    have hl' : ∀ x ∈ l, x ≠ a ∧ M.testBit x = false := by
      intro x hx
      have := hl x hx
      rw [Nat.testBit_lor, Bool.or_eq_false_iff, Nat.testBit_two_pow] at this
      exact ⟨fun hxa => by simp [hxa] at this, this.1⟩
    refine ⟨List.nodup_cons.mpr ⟨fun ha => (hl' a ha).1 rfl, hnd⟩, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact (hl' x hx).2

/-! ## The abundance checker -/

/-- The abundance checker, with `P` and `G` standing for the products of `t ^ 4` and of
`1 + t + ... + t ^ 4` over `S`: for every `b ∈ S` with `cand b`, replacing `b ^ 4` by `b` gives
an abundant number, and so does the full product. -/
def abOK2 (S : List ℕ) (cand : ℕ → Bool) (P G : ℕ) : Bool :=
  (S.all fun b => !cand b || decide (2 * P * geomS b 4 < G * (b + 1) * b ^ 3)) &&
    decide (2 * P < G)

/-- Unfolding `expL` at a cons. -/
theorem expL_cons (t : ℕ) (S : List ℕ) (b : ℕ) :
    expL (t :: S) b = (t, if t = b then 1 else 4) :: expL S b := rfl

/-- `expL S b = expL S 0` when no element of `S` is `b` or `0`. -/
theorem expL_eq_of_forall_ne {S : List ℕ} {b : ℕ} (h : ∀ t ∈ S, t ≠ b ∧ t ≠ 0) :
    expL S b = expL S 0 := by
  unfold expL
  refine List.map_congr_left fun t ht => ?_
  simp [(h t ht).1, (h t ht).2]

/-- Splitting off one element: with `b ∈ S`, distinct nonzero elements, the full products
`pPow (expL S 0)` and `pSig (expL S 0)` relate to those with `b` to the first power. -/
theorem pPow_pSig_split : ∀ {S : List ℕ} {b : ℕ}, (∀ t ∈ S, t ≠ 0) → S.Nodup → b ∈ S →
    pPow (expL S 0) = pPow (expL S b) * b ^ 3 ∧
      pSig (expL S 0) * (b + 1) = pSig (expL S b) * geomS b 4
  | [], _, _, _, hb => absurd hb List.not_mem_nil
  | t :: S, b, h0, hnd, hb => by
    rw [List.nodup_cons] at hnd
    have ht0 : t ≠ 0 := h0 t List.mem_cons_self
    have h0' : ∀ u ∈ S, u ≠ 0 := fun u hu => h0 u (List.mem_cons_of_mem _ hu)
    rw [expL_cons, expL_cons]
    by_cases htb : t = b
    · subst htb
      have he : expL S t = expL S 0 :=
        expL_eq_of_forall_ne fun u hu => ⟨fun h => hnd.1 (h ▸ hu), h0' u hu⟩
      simp only [pPow, pSig, if_neg ht0, he, ↓reduceIte, geomS]
      constructor <;> ring
    · have hbS : b ∈ S := by
        rcases List.mem_cons.mp hb with h | h
        · exact absurd h.symm htb
        · exact h
      obtain ⟨e1, e2⟩ := pPow_pSig_split h0' hnd.2 hbS
      simp only [pPow, pSig, if_neg htb, if_neg ht0]
      constructor
      · rw [e1]; ring
      · rw [mul_assoc, e2]; ring

end FamInst

open FamInst CommonChain EqChain in
/-- Soundness of the reach checks. Let `N` be an odd perfect number and `q` a number such that
`d ∣ v_p(N) + 1` for every prime factor `p ≠ q`, where `d ≥ 1`, with `cand q`. Take a table with
odd prime nodes `nodes`, whose first `ns` nodes divide `N` (with `ns` at most the number of
nodes), and whose rows pass `rowChk`. If all bits of `tm` are reached for every blocked source
node `b` (one of the first `rows.length` nodes) with `cand b`, and for the blocked value `0`,
then every node whose index is a bit of `tm` divides `N`. -/
theorem dvd_of_reach {N q d ns passes tm : ℕ} {cand : ℕ → Bool} {nodes : List ℕ}
    {rows : List (List ℕ)} (h : OddPerfect N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → d ∣ N.factorization p + 1) (hd : 1 ≤ d)
    (hcq : cand q = true) (hP : ∀ t ∈ nodes, t.Prime) (h2 : ∀ t ∈ nodes, t ≠ 2)
    (hseed : ∀ t ∈ nodes.take ns, t ∣ N) (hns : ns ≤ nodes.length)
    (hrows : ∀ e ∈ nodes.zip rows, rowChk d nodes e = true)
    (hcand : ∀ b ∈ nodes.take rows.length, cand b = true →
      reach nodes rows ns tm passes b = true)
    (h0 : reach nodes rows ns tm passes 0 = true) :
    ∀ k, tm.testBit k = true → nodes.getD k 0 ∣ N := by
  have hmem : ∀ {p : ℕ}, p.Prime → p ∣ N → p ∈ N.primeFactors := fun hp hpN =>
    Nat.mem_primeFactors.mpr ⟨hp, hpN, h.ne_zero⟩
  have key : ∀ b, (∀ y ∈ nodes.take rows.length, y ≠ b → y ≠ q) →
      reach nodes rows ns tm passes b = true → ∀ k, tm.testBit k = true → nodes.getD k 0 ∣ N := by
    intro b hb hr
    have hstep : ∀ x ∈ nodes.take rows.length, x ∣ N → x ≠ b → ∀ t ∈ nodes, gm x t d = 0 →
        t ∣ N := by
      intro x hx hxN hxb t ht hg
      have hxp := hP x (List.mem_of_mem_take hx)
      exact dvd_of_dvd_geom_sum_of_dvd_succ h hxp hd (hexp x (hmem hxp hxN) (hb x hx hxb))
        (hP t ht) (h2 t ht) (Nat.dvd_of_mod_eq_zero (by rw [← gm_eq]; exact hg))
    have hgm0 : ∀ x ∈ nodes, gm x 0 d ≠ 0 := by
      intro x hx
      rw [gm_eq, Nat.mod_zero]
      exact (Finset.sum_pos (fun i _ => pow_pos (hP x hx).pos i)
        (Finset.nonempty_range_iff.mpr (by omega))).ne'
    have hz : ∀ e ∈ nodes.zip rows, ∀ j ∈ e.2, gm e.1 (nodes.getD j 0) d = 0 := by
      intro e he j hj
      have := List.all_eq_true.mp (hrows e he) j hj
      simpa using this
    have h1 : ∀ k, (2 ^ ns - 1).testBit k = true → nodes.getD k 0 ∣ N := by
      intro k hk
      rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq] at hk
      have hkl : k < nodes.length := by omega
      rw [List.getD_eq_getElem _ _ hkl]
      have hkt : k < (nodes.take ns).length := by simp; omega
      have : nodes[k] = (nodes.take ns)[k] := by simp
      rw [this]
      exact hseed _ (List.getElem_mem hkt)
    have hgood := fiter_good (tm := tm) hstep hgm0 hz passes _ h1
    intro k hk
    simp only [reach, beq_iff_eq] at hr
    apply hgood k
    rw [← hr, Nat.testBit_land, Bool.and_eq_true] at hk
    exact hk.1
  by_cases hqn : q ∈ nodes.take rows.length
  · exact key q (fun _ _ hy => hy) (hcand q hqn hcq)
  · exact key 0 (fun y hy _ hyq => hqn (hyq ▸ hy)) h0

open FamInst CommonFam in
/-- Soundness of `abOK2`. Let `N` be perfect, `S` a list of distinct primes dividing `N` with
`t ^ 4 ∣ N` for every `t ∈ S` other than `q`, and `cand q`. If `P` and `G` are the products of
`t ^ 4` and of `1 + t + ... + t ^ 4` over `S`, then `abOK2 S cand P G` fails. -/
theorem FamInst.abOK2_sound {N q P G : ℕ} {cand : ℕ → Bool} (hN : N.Perfect) {S : List ℕ}
    (hP : ∀ t ∈ S, t.Prime) (hnd : S.Nodup) (hS : ∀ t ∈ S, t ∣ N)
    (h4 : ∀ t ∈ S, t ≠ q → t ^ 4 ∣ N) (hcq : cand q = true)
    (hPG : pPow (expL S 0) = P ∧ pSig (expL S 0) = G) (hab : abOK2 S cand P G = true) :
    False := by
  rw [abOK2, Bool.and_eq_true] at hab
  have key : ∀ b, (∀ t ∈ S, t ≠ b → t ≠ q) → 2 * pPow (expL S b) < pSig (expL S b) →
      False := by
    intro b hb hb'
    have hfst : (expL S b).map Prod.fst = S := by simp [expL, Function.comp_def]
    refine not_perfect_of_pSig hN (expL S b) ?_ (by rw [hfst]; exact hnd) ?_ hb'
    · intro e he
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
      exact hP t ht
    · intro e he
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
      by_cases htb : t = b
      · simpa [htb] using hS t ht
      · simpa [htb] using h4 t ht (hb t ht htb)
  by_cases hqS : q ∈ S
  · have := (List.all_eq_true.mp hab.1) q hqS
    simp only [hcq, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
    obtain ⟨e1, e2⟩ := pPow_pSig_split (fun t ht => (hP t ht).ne_zero) hnd hqS
    refine key q (fun _ _ h => h) (Nat.lt_of_mul_lt_mul_right (a := q ^ 3 * geomS q 4) ?_)
    rw [← hPG.1, ← hPG.2, e1] at this
    calc 2 * pPow (expL S q) * (q ^ 3 * geomS q 4)
        = 2 * (pPow (expL S q) * q ^ 3) * geomS q 4 := by ring
      _ < pSig (expL S 0) * (q + 1) * q ^ 3 := this
      _ = pSig (expL S q) * (q ^ 3 * geomS q 4) := by rw [e2]; ring
  · refine key 0 (fun t ht _ htq => hqS (htq ▸ ht)) ?_
    rw [hPG.1, hPG.2]
    simpa using hab.2

open FamInst CommonFam CommonChain in
/-- The combined closer. Let `N` be an odd perfect number and `q` a number with `cand q` and
`cand' q`, such that `d ∣ v_p(N) + 1` for every prime factor `p ≠ q`, where `d ≥ 5`. A table as
in `dvd_of_reach`, whose selected target primes `vals` (the nodes whose index is a bit of `tm`)
pass `abOK2` with `cand'`, gives a contradiction. -/
theorem false_of_reach {N q d ns passes tm P G : ℕ} {cand cand' : ℕ → Bool}
    {nodes vals : List ℕ} {rows : List (List ℕ)} (h : OddPerfect N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → d ∣ N.factorization p + 1) (hd : 5 ≤ d)
    (hcq : cand q = true) (hcq' : cand' q = true) (hP : ∀ t ∈ nodes, t.Prime)
    (h2 : ∀ t ∈ nodes, t ≠ 2) (hseed : ∀ t ∈ nodes.take ns, t ∣ N) (hns : ns ≤ nodes.length)
    (hrows : ∀ e ∈ nodes.zip rows, rowChk d nodes e = true)
    (hcand : ∀ b ∈ nodes.take rows.length, cand b = true →
      reach nodes rows ns tm passes b = true)
    (h0 : reach nodes rows ns tm passes 0 = true) (hv : sel 0 tm 0 nodes = vals)
    (hnd : vals.Nodup) (hPG : pPow (expL vals 0) = P ∧ pSig (expL vals 0) = G)
    (hab : abOK2 vals cand' P G = true) : False := by
  have hT := dvd_of_reach h hexp (by omega) hcq hP h2 hseed hns hrows hcand h0
  have hS : ∀ t ∈ vals, t ∣ N := by
    rw [← hv]
    intro t ht
    obtain ⟨-, k, hk, rfl⟩ := mem_sel nodes 0 List.drop_zero t ht
    exact hT k hk
  have hPS : ∀ t ∈ vals, t.Prime := by
    rw [← hv]
    intro t ht
    exact hP t ((sel_sublist 0 tm 0 nodes).subset ht)
  have h4 : ∀ t ∈ vals, t ≠ q → t ^ 4 ∣ N := by
    intro t ht htq
    have hp := hPS t ht
    have hmem := Nat.mem_primeFactors.mpr ⟨hp, hS t ht, h.ne_zero⟩
    exact (hp.pow_dvd_iff_le_factorization h.ne_zero).mpr
      (by have := Nat.le_of_dvd (by omega) (hexp t hmem htq); omega)
  exact abOK2_sound h.perfect hPS hnd hS h4 hcq' hPG hab

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

