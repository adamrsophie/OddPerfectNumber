import OddPerfect.DefectTreeCode

/-!
# Splitting the kernel check of a large defect tree certificate

Two equations used by the data modules of large certificates of `OddPerfect.DefectTreeCode`: the
Pratt check and the table check of a list split by `++` are the checks of the two parts, the
second Pratt part with the primes of the first part known. They let a data module check its
Pratt certificate and its fact table in pieces, one kernel evaluation per piece, which keeps the
memory of each evaluation small. They change nothing in the checker.
-/

namespace OddPerfect

namespace DefectTree

/-- The Pratt check of `l₁ ++ l₂` is the check of `l₁` and the check of `l₂` with the primes of
`l₁` known. -/
theorem checkAux_append (l₁ l₂ : PCert) : ∀ known : List ℕ,
    Pratt.checkAux known (l₁ ++ l₂) =
      (Pratt.checkAux known l₁ && Pratt.checkAux (l₁.reverse.map Prod.fst ++ known) l₂) := by
  induction l₁ with
  | nil => intro known; simp [Pratt.checkAux]
  | cons x t ih =>
    intro known
    obtain ⟨p, a, fs⟩ := x
    simp [Pratt.checkAux, ih, Bool.and_assoc]

/-- The table check of `a ++ b` is the check of `a` and the check of `b`. -/
theorem tabOK_append (pc : PCert) (a b : Tab) :
    tabOK pc (a ++ b) = (tabOK pc a && tabOK pc b) := by
  simp only [tabOK, List.all_append]

end DefectTree

end OddPerfect

#print axioms OddPerfect.DefectTree.checkAux_append
#print axioms OddPerfect.DefectTree.tabOK_append
