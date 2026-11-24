import OddPerfect.SpecialFiveCode

/-!
# Splitting a certificate for the special component `5 ^ 1` over several modules

The checker `OddPerfect.SpecialFive.check` evaluates one flat Pratt certificate, one fact table
and one tree. When a certificate is too large for one kernel check, it can be checked in pieces:

* a Pratt certificate `a ++ b` is accepted when `a` is accepted and `b` is accepted from a list
  `d` of known primes that all occur as primes of `a` (`check_append`);
* a table `t ++ u` is accepted when both parts are (`tabOK_append`);
* the tree check at a branch, a chain step and a chain end reduces to the checks of the
  children (`go_br`, `go_ord`, `go_stop`), so subtrees can be checked in separate modules with
  their states written out.

These lemmas only restate the definitions of `OddPerfect.SpecialFiveCode` in pieces; they carry
no data. The checker and its soundness theorem are used unchanged.
-/

namespace OddPerfect

namespace SpecialFiveMore

open DefectTree (Tab PCert tabOK)
open SpecialFive (Cert Mode go forcedB freshB)

/-- One Pratt entry stays accepted when the list of known primes grows. -/
theorem checkEntry_mono {k k' : List ℕ} (hk : ∀ q ∈ k, q ∈ k') {p a : ℕ} {fs : List ℕ}
    (h : Pratt.checkEntry k p a fs = true) : Pratt.checkEntry k' p a fs = true := by
  simp only [Pratt.checkEntry, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    List.contains_iff_mem] at h ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨⟨⟨h1, fun q hq => (h2 q hq).imp_left (hk q)⟩, h3⟩, h4⟩

/-- A Pratt certificate stays accepted when the list of known primes grows. -/
theorem checkAux_mono : ∀ {k k' : List ℕ} (c : PCert), (∀ q ∈ k, q ∈ k') →
    Pratt.checkAux k c = true → Pratt.checkAux k' c = true
  | _, _, [], _, _ => rfl
  | k, k', (p, a, fs) :: rest, hk, h => by
    simp only [Pratt.checkAux, Bool.and_eq_true] at h ⊢
    refine ⟨checkEntry_mono hk h.1, checkAux_mono rest ?_ h.2⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hk q hq)

/-- The check of a concatenation: the second part is checked with the primes of the first part
known. -/
theorem checkAux_append : ∀ (k : List ℕ) (a b : PCert), Pratt.checkAux k a = true →
    Pratt.checkAux ((a.map Prod.fst).reverse ++ k) b = true → Pratt.checkAux k (a ++ b) = true
  | _, [], _, _, hb => by simpa using hb
  | k, (p, x, fs) :: a, b, ha, hb => by
    simp only [Pratt.checkAux, Bool.and_eq_true, List.cons_append] at ha ⊢
    refine ⟨ha.1, checkAux_append (p :: k) a b ha.2 ?_⟩
    simpa [List.map_cons, List.reverse_cons, List.append_assoc] using hb

/-- A Pratt certificate `a ++ b` is accepted when `a` is accepted and `b` is accepted from a
list `d` of known primes that all occur as primes of `a`. -/
theorem check_append {a b : PCert} {d : List ℕ} (ha : Pratt.check a = true)
    (hb : Pratt.checkAux d b = true)
    (hd : (d.all fun q => (a.map Prod.fst).contains q) = true) :
    Pratt.check (a ++ b) = true := by
  refine checkAux_append [] a b ha (checkAux_mono b (fun q hq => ?_) hb)
  rw [List.all_eq_true] at hd
  have := List.contains_iff_mem.mp (hd q hq)
  exact List.mem_append_left _ (List.mem_reverse.mpr this)

/-- The table check of a concatenation. -/
theorem tabOK_append {pc : PCert} {t u : Tab} (ht : tabOK pc t = true)
    (hu : tabOK pc u = true) : tabOK pc (t ++ u) = true := by
  unfold tabOK at *
  rw [List.all_append, ht, hu]
  rfl

/-- The tree check at a branch. -/
theorem go_br {B : ℕ} {tab : Tab} {r : ℕ} {ch : Cert} {st : List (ℕ × ℕ)}
    (h : (forcedB tab st r && freshB st r && r != 5) = true)
    (hc : go B tab ch st (.chain r 2) = true) : go B tab (.br r ch) st .node = true := by
  change (forcedB tab st r && freshB st r && r != 5 && go B tab ch st (.chain r 2)) = true
  rw [h, hc]
  rfl

/-- The tree check at a step of a chain. -/
theorem go_ord {B : ℕ} {tab : Tab} {kid rest : Cert} {st : List (ℕ × ℕ)} {r e : ℕ}
    (hk : go B tab kid ((r, e) :: st) .node = true)
    (hr : go B tab rest st (.chain r (e + 2)) = true) :
    go B tab (.ord kid rest) st (.chain r e) = true := by
  change (go B tab kid ((r, e) :: st) .node && go B tab rest st (.chain r (e + 2))) = true
  rw [hk, hr]
  rfl

/-- The tree check at the end of a chain. -/
theorem go_stop {B : ℕ} {tab : Tab} {st : List (ℕ × ℕ)} {r e : ℕ} (h : B < r ^ e) :
    go B tab .stop st (.chain r e) = true := by
  change decide (B < r ^ e) = true
  exact decide_eq_true h

end SpecialFiveMore

end OddPerfect

#print axioms OddPerfect.SpecialFiveMore.checkEntry_mono
#print axioms OddPerfect.SpecialFiveMore.checkAux_mono
#print axioms OddPerfect.SpecialFiveMore.checkAux_append
#print axioms OddPerfect.SpecialFiveMore.check_append
#print axioms OddPerfect.SpecialFiveMore.tabOK_append
#print axioms OddPerfect.SpecialFiveMore.go_br
#print axioms OddPerfect.SpecialFiveMore.go_ord
#print axioms OddPerfect.SpecialFiveMore.go_stop
