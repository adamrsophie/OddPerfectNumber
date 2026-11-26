import OddPerfect.ImpureRowTreeCheck

/-!
# Impure row tree certificates for the lengths 449, 457, 461, 463, 467, 479

Data for `OddPerfect.ImpTree.tableOK_sound`: for each length `l` a tree for the seed `3`
and a tree for the seed `5`, checked by kernel reduction. Restricted result (one odd prime
divides every ordinary index); no published source was checked; novelty not verified.
The odd perfect number conjecture remains open.
-/

namespace OddPerfect.ImpTree.ImpureRowTreeD09

open OddPerfect.ImpTree

/-- Pratt certificates for the large primes. -/
def pc : List (ℕ × ℕ × List ℕ) :=
  []

/-- The tree for the length `449` and the seed `3`. -/
def t449_3 : Tree :=
  Tree.split 449 (
    Tree.add 5 (
      Tree.leaf
        [(3, [Item.cof 3 1 2]), (5, [Item.cof 5 1 2])]
        [Item.cof 3 1 2, Item.cof 5 1 2])) (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (449, [Item.cof 449 1 2])]
      [Item.cof 3 1 2, Item.cof 449 1 2])

/-- The tree for the length `449` and the seed `5`. -/
def t449_5 : Tree :=
  Tree.split 449 (
    Tree.add 3 (
      Tree.leaf
        [(5, [Item.cof 5 1 2]), (3, [Item.cof 3 1 2])]
        [Item.cof 5 1 2, Item.cof 3 1 2])) (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (449, [Item.cof 449 1 2])]
      [Item.cof 5 1 2, Item.cof 449 1 2])

/-- The tree for the length `457` and the seed `3`. -/
def t457_3 : Tree :=
  Tree.split 457 (
    Tree.add 229 (
      Tree.leaf
        [(3, [Item.cof 3 1 2]), (229, [Item.cof 229 1 2])]
        [Item.cof 3 1 2, Item.cof 229 1 2])) (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (457, [Item.pr 457 98713, Item.cof 457 98713 0])]
      [Item.pr 457 98713, Item.cof 3 1 2, Item.cof 457 98713 2])

/-- The tree for the length `457` and the seed `5`. -/
def t457_5 : Tree :=
  Tree.split 457 (
    Tree.add 229 (
      Tree.leaf
        [(5, [Item.pr 5 13711, Item.cof 5 13711 0]), (229, [Item.cof 229 1 2])]
        [Item.pr 5 13711, Item.cof 5 13711 2, Item.cof 229 1 2])) (
    Tree.leaf
      [(5, [Item.pr 5 13711, Item.cof 5 13711 0]), (457, [Item.pr 457 98713, Item.cof 457 98713 0])]
      [Item.pr 5 13711, Item.pr 457 98713, Item.cof 5 13711 2, Item.cof 457 98713 2])

/-- The tree for the length `461` and the seed `3`. -/
def t461_3 : Tree :=
  Tree.split 461 (
    Tree.add 7 (
      Tree.add 11 (
        Tree.leaf
          [(3, [Item.pr 3 11987, Item.cof 3 11987 0]), (7, [Item.pr 7 13831, Item.cof 7 13831 0]),
              (11, [Item.pr 11 2767, Item.cof 11 2767 0])]
          [Item.pr 3 11987, Item.pr 7 13831, Item.pr 11 2767, Item.cof 3 11987 2,
              Item.cof 7 13831 2, Item.cof 11 2767 2]))) (
    Tree.leaf
      [(3, [Item.pr 3 11987, Item.cof 3 11987 0]), (461, [Item.pr 461 13831, Item.pr 461 133691])]
      [Item.pr 3 11987, Item.pr 461 13831, Item.pr 461 133691, Item.pr 461 363269,
          Item.cof 3 11987 2, Item.cof 461 671713522802449 2])

/-- The tree for the length `461` and the seed `5`. -/
def t461_5 : Tree :=
  Tree.split 461 (
    Tree.add 3 (
      Tree.add 7 (
        Tree.add 11 (
          Tree.leaf
            [(5, [Item.cof 5 1 2]), (3, [Item.pr 3 11987, Item.cof 3 11987 0]), (7,
                [Item.pr 7 13831, Item.cof 7 13831 0]), (11, [Item.pr 11 2767, Item.cof 11 2767 0])]
            [Item.pr 3 11987, Item.pr 7 13831, Item.pr 11 2767, Item.cof 5 1 2,
                Item.cof 3 11987 2, Item.cof 7 13831 2, Item.cof 11 2767 2])))) (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (461, [Item.pr 461 13831, Item.pr 461 133691])]
      [Item.pr 461 13831, Item.pr 461 133691, Item.pr 461 363269, Item.cof 5 1 2,
          Item.cof 461 671713522802449 2])

/-- The tree for the length `463` and the seed `3`. -/
def t463_3 : Tree :=
  Tree.add 463 (
    Tree.leaf
      [(3, [Item.pr 3 11113, Item.pr 3 83341]), (463, [Item.pr 463 5557, Item.pr 463 118529])]
      [Item.pr 3 11113, Item.pr 3 83341, Item.pr 3 155569, Item.pr 463 5557, Item.pr 463 118529,
          Item.pr 463 312989, Item.cof 3 144083112510277 2, Item.cof 463 206155104066817 2])

/-- The tree for the length `463` and the seed `5`. -/
def t463_5 : Tree :=
  Tree.add 463 (
    Tree.leaf
      [(5, [Item.pr 5 44449, Item.cof 5 44449 0]), (463, [Item.pr 463 5557, Item.pr 463 118529])]
      [Item.pr 5 44449, Item.pr 463 5557, Item.pr 463 118529, Item.pr 463 312989,
          Item.cof 5 44449 2, Item.cof 463 206155104066817 2])

/-- The tree for the length `467` and the seed `3`. -/
def t467_3 : Tree :=
  Tree.add 467 (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (467, [Item.pr 467 268993, Item.cof 467 268993 0])]
      [Item.pr 467 268993, Item.cof 3 1 2, Item.cof 467 268993 2])

/-- The tree for the length `467` and the seed `5`. -/
def t467_5 : Tree :=
  Tree.add 467 (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (467, [Item.pr 467 268993, Item.cof 467 268993 0])]
      [Item.pr 467 268993, Item.cof 5 1 2, Item.cof 467 268993 2])

/-- The tree for the length `479` and the seed `3`. -/
def t479_3 : Tree :=
  Tree.add 479 (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (479, [Item.pr 479 3833, Item.cof 479 3833 0])]
      [Item.pr 479 3833, Item.cof 3 1 2, Item.cof 479 3833 2])

/-- The tree for the length `479` and the seed `5`. -/
def t479_5 : Tree :=
  Tree.add 479 (
    Tree.leaf
      [(5, [Item.pr 5 48859, Item.cof 5 48859 0]), (479, [Item.pr 479 3833, Item.cof 479 3833 0])]
      [Item.pr 5 48859, Item.pr 479 3833, Item.cof 5 48859 2, Item.cof 479 3833 2])

/-- The table. -/
def tab : List (ℕ × Tree × Tree) :=
  [(449, t449_3, t449_5),
   (457, t457_3, t457_5),
   (461, t461_3, t461_5),
   (463, t463_3, t463_5),
   (467, t467_3, t467_5),
   (479, t479_3, t479_5)]

/-- The lengths of the table. -/
def ls : List ℕ := [449, 457, 461, 463, 467, 479]

theorem tab_ls : tab.map Prod.fst = ls := rfl

theorem ok449 : tableOK pc [(449, t449_3, t449_5)] = true := by
  decide +kernel

theorem ok457 : tableOK pc [(457, t457_3, t457_5)] = true := by
  decide +kernel

theorem ok461 : tableOK pc [(461, t461_3, t461_5)] = true := by
  decide +kernel

theorem ok463 : tableOK pc [(463, t463_3, t463_5)] = true := by
  decide +kernel

theorem ok467 : tableOK pc [(467, t467_3, t467_5)] = true := by
  decide +kernel

theorem ok479 : tableOK pc [(479, t479_3, t479_5)] = true := by
  decide +kernel

theorem tab_ok : tableOK pc tab = true :=
  tableOK_cons ok449 <|
  tableOK_cons ok457 <|
  tableOK_cons ok461 <|
  tableOK_cons ok463 <|
  tableOK_cons ok467 <|
  tableOK_cons ok479 <|
  tableOK_nil pc

end OddPerfect.ImpTree.ImpureRowTreeD09

#print axioms OddPerfect.ImpTree.ImpureRowTreeD09.tab_ls
#print axioms OddPerfect.ImpTree.ImpureRowTreeD09.tab_ok
#print axioms OddPerfect.ImpTree.ImpureRowTreeD09.ok449
#print axioms OddPerfect.ImpTree.ImpureRowTreeD09.ok457
#print axioms OddPerfect.ImpTree.ImpureRowTreeD09.ok461
#print axioms OddPerfect.ImpTree.ImpureRowTreeD09.ok463
#print axioms OddPerfect.ImpTree.ImpureRowTreeD09.ok467
#print axioms OddPerfect.ImpTree.ImpureRowTreeD09.ok479
