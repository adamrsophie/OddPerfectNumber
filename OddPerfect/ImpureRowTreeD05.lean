import OddPerfect.ImpureRowTreeCheck

/-!
# Impure row tree certificates for the lengths 307, 311, 313, 317, 331, 337

Data for `OddPerfect.ImpTree.tableOK_sound`: for each length `l` a tree for the seed `3`
and a tree for the seed `5`, checked by kernel reduction. Restricted result (one odd prime
divides every ordinary index); no published source was checked; novelty not verified.
The odd perfect number conjecture remains open.
-/

namespace OddPerfect.ImpTree.ImpureRowTreeD05

open OddPerfect.ImpTree

/-- Pratt certificates for the large primes. -/
def pc : List (ℕ × ℕ × List ℕ) :=
  []

/-- The tree for the length `307` and the seed `3`. -/
def t307_3 : Tree :=
  Tree.add 307 (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (307, [Item.pr 307 1229, Item.cof 307 1229 0])]
      [Item.pr 307 1229, Item.cof 3 1 2, Item.cof 307 1229 2])

/-- The tree for the length `307` and the seed `5`. -/
def t307_5 : Tree :=
  Tree.add 307 (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (307, [Item.pr 307 1229, Item.cof 307 1229 0])]
      [Item.pr 307 1229, Item.cof 5 1 2, Item.cof 307 1229 2])

/-- The tree for the length `311` and the seed `3`. -/
def t311_3 : Tree :=
  Tree.add 311 (
    Tree.leaf
      [(3, [Item.pr 3 3733, Item.cof 3 3733 0]), (311, [Item.cof 311 1 2])]
      [Item.pr 3 3733, Item.cof 3 3733 2, Item.cof 311 1 2])

/-- The tree for the length `311` and the seed `5`. -/
def t311_5 : Tree :=
  Tree.add 311 (
    Tree.leaf
      [(5, [Item.pr 5 263729, Item.cof 5 263729 0]), (311, [Item.cof 311 1 2])]
      [Item.pr 5 263729, Item.cof 5 263729 2, Item.cof 311 1 2])

/-- The tree for the length `313` and the seed `3`. -/
def t313_3 : Tree :=
  Tree.split 313 (
    Tree.add 157 (
      Tree.leaf
        [(3, [Item.cof 3 1 2]), (157, [Item.cof 157 1 2])]
        [Item.cof 3 1 2, Item.cof 157 1 2])) (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (313, [Item.pr 313 5009, Item.pr 313 182167])]
      [Item.pr 313 5009, Item.pr 313 182167, Item.pr 313 418169, Item.cof 3 1 2,
          Item.cof 313 381568550445007 2])

/-- The tree for the length `313` and the seed `5`. -/
def t313_5 : Tree :=
  Tree.split 313 (
    Tree.add 157 (
      Tree.leaf
        [(5, [Item.cof 5 1 2]), (157, [Item.cof 157 1 2])]
        [Item.cof 5 1 2, Item.cof 157 1 2])) (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (313, [Item.pr 313 5009, Item.pr 313 182167])]
      [Item.pr 313 5009, Item.pr 313 182167, Item.pr 313 418169, Item.cof 5 1 2,
          Item.cof 313 381568550445007 2])

/-- The tree for the length `317` and the seed `3`. -/
def t317_3 : Tree :=
  Tree.split 317 (
    Tree.add 53 (
      Tree.leaf
        [(3, [Item.cof 3 1 2]), (53, [Item.cof 53 1 2])]
        [Item.cof 3 1 2, Item.cof 53 1 2])) (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (317, [Item.cof 317 1 2])]
      [Item.cof 3 1 2, Item.cof 317 1 2])

/-- The tree for the length `317` and the seed `5`. -/
def t317_5 : Tree :=
  Tree.split 317 (
    Tree.add 3 (
      Tree.add 53 (
        Tree.leaf
          [(5, [Item.pr 5 34871, Item.cof 5 34871 0]), (3, [Item.cof 3 1 2]), (53,
              [Item.cof 53 1 2])]
          [Item.pr 5 34871, Item.cof 5 34871 2, Item.cof 3 1 2, Item.cof 53 1 2]))) (
    Tree.leaf
      [(5, [Item.pr 5 34871, Item.cof 5 34871 0]), (317, [Item.cof 317 1 2])]
      [Item.pr 5 34871, Item.cof 5 34871 2, Item.cof 317 1 2])

/-- The tree for the length `331` and the seed `3`. -/
def t331_3 : Tree :=
  Tree.add 331 (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (331, [Item.pr 331 29129, Item.pr 331 970493])]
      [Item.pr 331 29129, Item.pr 331 970493, Item.cof 3 1 2, Item.cof 331 28269490597 2])

/-- The tree for the length `331` and the seed `5`. -/
def t331_5 : Tree :=
  Tree.add 331 (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (331, [Item.pr 331 29129, Item.pr 331 970493])]
      [Item.pr 331 29129, Item.pr 331 970493, Item.cof 5 1 2, Item.cof 331 28269490597 2])

/-- The tree for the length `337` and the seed `3`. -/
def t337_3 : Tree :=
  Tree.split 337 (
    Tree.add 13 (
      Tree.leaf
        [(3, [Item.pr 3 8089, Item.cof 3 8089 0]), (13, [Item.cof 13 1 2])]
        [Item.pr 3 8089, Item.cof 3 8089 2, Item.cof 13 1 2])) (
    Tree.leaf
      [(3, [Item.pr 3 8089, Item.cof 3 8089 0]), (337, [Item.cof 337 1 2])]
      [Item.pr 3 8089, Item.cof 3 8089 2, Item.cof 337 1 2])

/-- The tree for the length `337` and the seed `5`. -/
def t337_5 : Tree :=
  Tree.split 337 (
    Tree.add 13 (
      Tree.leaf
        [(5, [Item.cof 5 1 2]), (13, [Item.cof 13 1 2])]
        [Item.cof 5 1 2, Item.cof 13 1 2])) (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (337, [Item.cof 337 1 2])]
      [Item.cof 5 1 2, Item.cof 337 1 2])

/-- The table. -/
def tab : List (ℕ × Tree × Tree) :=
  [(307, t307_3, t307_5),
   (311, t311_3, t311_5),
   (313, t313_3, t313_5),
   (317, t317_3, t317_5),
   (331, t331_3, t331_5),
   (337, t337_3, t337_5)]

/-- The lengths of the table. -/
def ls : List ℕ := [307, 311, 313, 317, 331, 337]

theorem tab_ls : tab.map Prod.fst = ls := rfl

theorem ok307 : tableOK pc [(307, t307_3, t307_5)] = true := by
  decide +kernel

theorem ok311 : tableOK pc [(311, t311_3, t311_5)] = true := by
  decide +kernel

theorem ok313 : tableOK pc [(313, t313_3, t313_5)] = true := by
  decide +kernel

theorem ok317 : tableOK pc [(317, t317_3, t317_5)] = true := by
  decide +kernel

theorem ok331 : tableOK pc [(331, t331_3, t331_5)] = true := by
  decide +kernel

theorem ok337 : tableOK pc [(337, t337_3, t337_5)] = true := by
  decide +kernel

theorem tab_ok : tableOK pc tab = true :=
  tableOK_cons ok307 <|
  tableOK_cons ok311 <|
  tableOK_cons ok313 <|
  tableOK_cons ok317 <|
  tableOK_cons ok331 <|
  tableOK_cons ok337 <|
  tableOK_nil pc

end OddPerfect.ImpTree.ImpureRowTreeD05

#print axioms OddPerfect.ImpTree.ImpureRowTreeD05.tab_ls
#print axioms OddPerfect.ImpTree.ImpureRowTreeD05.tab_ok
#print axioms OddPerfect.ImpTree.ImpureRowTreeD05.ok307
#print axioms OddPerfect.ImpTree.ImpureRowTreeD05.ok311
#print axioms OddPerfect.ImpTree.ImpureRowTreeD05.ok313
#print axioms OddPerfect.ImpTree.ImpureRowTreeD05.ok317
#print axioms OddPerfect.ImpTree.ImpureRowTreeD05.ok331
#print axioms OddPerfect.ImpTree.ImpureRowTreeD05.ok337
