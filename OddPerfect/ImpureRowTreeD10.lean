import OddPerfect.ImpureRowTreeCheck

/-!
# Impure row tree certificates for the lengths 487, 491, 499, 503, 509, 521

Data for `OddPerfect.ImpTree.tableOK_sound`: for each length `l` a tree for the seed `3`
and a tree for the seed `5`, checked by kernel reduction. Restricted result (one odd prime
divides every ordinary index); no published source was checked; novelty not verified.
The odd perfect number conjecture remains open.
-/

namespace OddPerfect.ImpTree.ImpureRowTreeD10

open OddPerfect.ImpTree

/-- Pratt certificates for the large primes. -/
def pc : List (ℕ × ℕ × List ℕ) :=
  []

/-- The tree for the length `487` and the seed `3`. -/
def t487_3 : Tree :=
  Tree.add 487 (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (487, [Item.pr 487 1949, Item.cof 487 1949 0])]
      [Item.pr 487 1949, Item.cof 3 1 2, Item.cof 487 1949 2])

/-- The tree for the length `487` and the seed `5`. -/
def t487_5 : Tree :=
  Tree.add 487 (
    Tree.leaf
      [(5, [Item.pr 5 1949, Item.pr 5 949651]), (487, [Item.pr 487 1949, Item.cof 487 1949 0])]
      [Item.pr 5 1949, Item.pr 5 949651, Item.cof 5 1850869799 0, Item.cof 487 1949 2])

/-- The tree for the length `491` and the seed `3`. -/
def t491_3 : Tree :=
  Tree.add 491 (
    Tree.leaf
      [(3, [Item.pr 3 983, Item.pr 3 24551]), (491, [Item.pr 491 58921, Item.cof 491 58921 0])]
      [Item.pr 3 983, Item.pr 3 24551, Item.pr 491 58921, Item.cof 3 24133633 2,
          Item.cof 491 58921 2])

/-- The tree for the length `491` and the seed `5`. -/
def t491_5 : Tree :=
  Tree.add 491 (
    Tree.leaf
      [(5, [Item.pr 5 111949, Item.pr 5 372179]), (491, [Item.pr 491 58921, Item.cof 491 58921 0])]
      [Item.pr 5 111949, Item.pr 5 372179, Item.pr 491 58921, Item.cof 5 41665066871 2,
          Item.cof 491 58921 2])

/-- The tree for the length `499` and the seed `3`. -/
def t499_3 : Tree :=
  Tree.add 499 (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (499, [Item.pr 499 1997, Item.cof 499 1997 0])]
      [Item.pr 499 1997, Item.cof 3 1 2, Item.cof 499 1997 2])

/-- The tree for the length `499` and the seed `5`. -/
def t499_5 : Tree :=
  Tree.add 499 (
    Tree.leaf
      [(5, [Item.pr 5 20959, Item.cof 5 20959 0]), (499, [Item.pr 499 1997, Item.cof 499 1997 0])]
      [Item.pr 5 20959, Item.pr 499 1997, Item.cof 5 20959 2, Item.cof 499 1997 2])

/-- The tree for the length `503` and the seed `3`. -/
def t503_3 : Tree :=
  Tree.add 503 (
    Tree.leaf
      [(3, [Item.pr 3 7043, Item.pr 3 12073]), (503, [Item.pr 503 191141, Item.cof 503 191141 0])]
      [Item.pr 3 7043, Item.pr 3 12073, Item.pr 503 191141, Item.cof 3 85030139 2,
          Item.cof 503 191141 2])

/-- The tree for the length `503` and the seed `5`. -/
def t503_5 : Tree :=
  Tree.add 503 (
    Tree.leaf
      [(5, [Item.pr 5 30181, Item.cof 5 30181 0]), (503, [Item.pr 503 191141,
          Item.cof 503 191141 0])]
      [Item.pr 5 30181, Item.pr 503 191141, Item.cof 5 30181 2, Item.cof 503 191141 2])

/-- The tree for the length `509` and the seed `3`. -/
def t509_3 : Tree :=
  Tree.split 509 (
    Tree.add 5 (
      Tree.add 17 (
        Tree.leaf
          [(3, [Item.pr 3 1019, Item.pr 3 7127]), (5, [Item.pr 5 1019, Item.pr 5 219889]), (17,
              [Item.pr 17 1019, Item.pr 17 10181])]
          [Item.pr 3 1019, Item.pr 3 7127, Item.pr 3 54973, Item.pr 3 97729, Item.pr 5 219889,
              Item.pr 17 10181, Item.pr 17 27487, Item.pr 17 91621,
              Item.cof 3 39016996598512921 2, Item.cof 5 224066891 2,
              Item.cof 17 26126846365339453 2]))) (
    Tree.leaf
      [(3, [Item.pr 3 1019, Item.pr 3 7127]), (509, [Item.pr 509 1019, Item.cof 509 1019 0])]
      [Item.pr 3 1019, Item.pr 3 7127, Item.pr 3 54973, Item.pr 3 97729,
          Item.cof 3 39016996598512921 2, Item.cof 509 1019 2])

/-- The tree for the length `509` and the seed `5`. -/
def t509_5 : Tree :=
  Tree.split 509 (
    Tree.add 3 (
      Tree.add 17 (
        Tree.leaf
          [(5, [Item.pr 5 1019, Item.pr 5 219889]), (3, [Item.pr 3 1019, Item.pr 3 7127]), (17,
              [Item.pr 17 1019, Item.pr 17 10181])]
          [Item.pr 5 1019, Item.pr 5 219889, Item.pr 3 7127, Item.pr 3 54973, Item.pr 3 97729,
              Item.pr 17 10181, Item.pr 17 27487, Item.pr 17 91621, Item.cof 5 224066891 2,
              Item.cof 3 39016996598512921 2, Item.cof 17 26126846365339453 2]))) (
    Tree.leaf
      [(5, [Item.pr 5 1019, Item.pr 5 219889]), (509, [Item.pr 509 1019, Item.cof 509 1019 0])]
      [Item.pr 5 1019, Item.pr 5 219889, Item.cof 5 224066891 2, Item.cof 509 1019 2])

/-- The tree for the length `521` and the seed `3`. -/
def t521_3 : Tree :=
  Tree.split 521 (
    Tree.add 29 (
      Tree.leaf
        [(3, [Item.cof 3 1 2]), (29, [Item.cof 29 1 2])]
        [Item.cof 3 1 2, Item.cof 29 1 2])) (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (521, [Item.cof 521 1 2])]
      [Item.cof 3 1 2, Item.cof 521 1 2])

/-- The tree for the length `521` and the seed `5`. -/
def t521_5 : Tree :=
  Tree.split 521 (
    Tree.add 3 (
      Tree.add 29 (
        Tree.leaf
          [(5, [Item.cof 5 1 2]), (3, [Item.cof 3 1 2]), (29, [Item.cof 29 1 2])]
          [Item.cof 5 1 2, Item.cof 3 1 2, Item.cof 29 1 2]))) (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (521, [Item.cof 521 1 2])]
      [Item.cof 5 1 2, Item.cof 521 1 2])

/-- The table. -/
def tab : List (ℕ × Tree × Tree) :=
  [(487, t487_3, t487_5),
   (491, t491_3, t491_5),
   (499, t499_3, t499_5),
   (503, t503_3, t503_5),
   (509, t509_3, t509_5),
   (521, t521_3, t521_5)]

/-- The lengths of the table. -/
def ls : List ℕ := [487, 491, 499, 503, 509, 521]

theorem tab_ls : tab.map Prod.fst = ls := rfl

theorem ok487 : tableOK pc [(487, t487_3, t487_5)] = true := by
  decide +kernel

theorem ok491 : tableOK pc [(491, t491_3, t491_5)] = true := by
  decide +kernel

theorem ok499 : tableOK pc [(499, t499_3, t499_5)] = true := by
  decide +kernel

theorem ok503 : tableOK pc [(503, t503_3, t503_5)] = true := by
  decide +kernel

theorem ok509 : tableOK pc [(509, t509_3, t509_5)] = true := by
  decide +kernel

theorem ok521 : tableOK pc [(521, t521_3, t521_5)] = true := by
  decide +kernel

theorem tab_ok : tableOK pc tab = true :=
  tableOK_cons ok487 <|
  tableOK_cons ok491 <|
  tableOK_cons ok499 <|
  tableOK_cons ok503 <|
  tableOK_cons ok509 <|
  tableOK_cons ok521 <|
  tableOK_nil pc

end OddPerfect.ImpTree.ImpureRowTreeD10

#print axioms OddPerfect.ImpTree.ImpureRowTreeD10.tab_ls
#print axioms OddPerfect.ImpTree.ImpureRowTreeD10.tab_ok
#print axioms OddPerfect.ImpTree.ImpureRowTreeD10.ok487
#print axioms OddPerfect.ImpTree.ImpureRowTreeD10.ok491
#print axioms OddPerfect.ImpTree.ImpureRowTreeD10.ok499
#print axioms OddPerfect.ImpTree.ImpureRowTreeD10.ok503
#print axioms OddPerfect.ImpTree.ImpureRowTreeD10.ok509
#print axioms OddPerfect.ImpTree.ImpureRowTreeD10.ok521
