import OddPerfect.ImpureRowTreeCheck

/-!
# Impure row tree certificates for the lengths 379, 383, 389, 397, 401, 409

Data for `OddPerfect.ImpTree.tableOK_sound`: for each length `l` a tree for the seed `3`
and a tree for the seed `5`, checked by kernel reduction. Restricted result (one odd prime
divides every ordinary index); no published source was checked; novelty not verified.
The odd perfect number conjecture remains open.
-/

namespace OddPerfect.ImpTree.ImpureRowTreeD07

open OddPerfect.ImpTree

/-- Pratt certificates for the large primes. -/
def pc : List (ℕ × ℕ × List ℕ) :=
  []

/-- The tree for the length `379` and the seed `3`. -/
def t379_3 : Tree :=
  Tree.add 379 (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (379, [Item.cof 379 1 2])]
      [Item.cof 3 1 2, Item.cof 379 1 2])

/-- The tree for the length `379` and the seed `5`. -/
def t379_5 : Tree :=
  Tree.add 379 (
    Tree.leaf
      [(5, [Item.pr 5 15919, Item.pr 5 19709]), (379, [Item.cof 379 1 2])]
      [Item.pr 5 15919, Item.pr 5 19709, Item.cof 5 313747571 2, Item.cof 379 1 2])

/-- The tree for the length `383` and the seed `3`. -/
def t383_3 : Tree :=
  Tree.add 383 (
    Tree.leaf
      [(3, [Item.pr 3 23747, Item.cof 3 23747 0]), (383, [Item.cof 383 1 2])]
      [Item.pr 3 23747, Item.cof 3 23747 2, Item.cof 383 1 2])

/-- The tree for the length `383` and the seed `5`. -/
def t383_5 : Tree :=
  Tree.add 383 (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (383, [Item.cof 383 1 2])]
      [Item.cof 5 1 2, Item.cof 383 1 2])

/-- The tree for the length `389` and the seed `3`. -/
def t389_3 : Tree :=
  Tree.split 389 (
    Tree.add 5 (
      Tree.add 13 (
        Tree.leaf
          [(3, [Item.pr 3 51349, Item.cof 3 51349 0]), (5, [Item.pr 5 179719,
              Item.cof 5 179719 0]), (13, [Item.cof 13 1 2])]
          [Item.pr 3 51349, Item.pr 5 179719, Item.cof 3 51349 2, Item.cof 5 179719 2,
              Item.cof 13 1 2]))) (
    Tree.leaf
      [(3, [Item.pr 3 51349, Item.cof 3 51349 0]), (389, [Item.pr 389 16339, Item.pr 389 101141])]
      [Item.pr 3 51349, Item.pr 389 16339, Item.pr 389 101141, Item.cof 3 51349 2,
          Item.cof 389 1652542799 2])

/-- The tree for the length `389` and the seed `5`. -/
def t389_5 : Tree :=
  Tree.split 389 (
    Tree.add 3 (
      Tree.add 13 (
        Tree.leaf
          [(5, [Item.pr 5 179719, Item.cof 5 179719 0]), (3, [Item.pr 3 51349,
              Item.cof 3 51349 0]), (13, [Item.cof 13 1 2])]
          [Item.pr 5 179719, Item.pr 3 51349, Item.cof 5 179719 2, Item.cof 3 51349 2,
              Item.cof 13 1 2]))) (
    Tree.leaf
      [(5, [Item.pr 5 179719, Item.cof 5 179719 0]), (389, [Item.pr 389 16339, Item.pr 389 101141])]
      [Item.pr 5 179719, Item.pr 389 16339, Item.pr 389 101141, Item.cof 5 179719 2,
          Item.cof 389 1652542799 2])

/-- The tree for the length `397` and the seed `3`. -/
def t397_3 : Tree :=
  Tree.split 397 (
    Tree.add 199 (
      Tree.leaf
        [(3, [Item.pr 3 366829, Item.cof 3 366829 0]), (199, [Item.cof 199 1 2])]
        [Item.pr 3 366829, Item.cof 3 366829 2, Item.cof 199 1 2])) (
    Tree.leaf
      [(3, [Item.pr 3 366829, Item.cof 3 366829 0]), (397, [Item.pr 397 2383, Item.pr 397 11117])]
      [Item.pr 3 366829, Item.pr 397 2383, Item.pr 397 11117, Item.pr 397 25409,
          Item.cof 3 366829 2, Item.cof 397 673130425699 2])

/-- The tree for the length `397` and the seed `5`. -/
def t397_5 : Tree :=
  Tree.split 397 (
    Tree.add 199 (
      Tree.leaf
        [(5, [Item.cof 5 1 2]), (199, [Item.cof 199 1 2])]
        [Item.cof 5 1 2, Item.cof 199 1 2])) (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (397, [Item.pr 397 2383, Item.pr 397 11117])]
      [Item.pr 397 2383, Item.pr 397 11117, Item.pr 397 25409, Item.cof 5 1 2,
          Item.cof 397 673130425699 2])

/-- The tree for the length `401` and the seed `3`. -/
def t401_3 : Tree :=
  Tree.split 401 (
    Tree.add 67 (
      Tree.leaf
        [(3, [Item.cof 3 1 2]), (67, [Item.pr 67 4813, Item.cof 67 4813 0])]
        [Item.pr 67 4813, Item.cof 3 1 2, Item.cof 67 4813 2])) (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (401, [Item.pr 401 16843, Item.cof 401 16843 0])]
      [Item.pr 401 16843, Item.cof 3 1 2, Item.cof 401 16843 2])

/-- The tree for the length `401` and the seed `5`. -/
def t401_5 : Tree :=
  Tree.split 401 (
    Tree.add 3 (
      Tree.add 67 (
        Tree.leaf
          [(5, [Item.cof 5 1 2]), (3, [Item.cof 3 1 2]), (67, [Item.pr 67 4813,
              Item.cof 67 4813 0])]
          [Item.pr 67 4813, Item.cof 5 1 2, Item.cof 3 1 2, Item.cof 67 4813 2]))) (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (401, [Item.pr 401 16843, Item.cof 401 16843 0])]
      [Item.pr 401 16843, Item.cof 5 1 2, Item.cof 401 16843 2])

/-- The tree for the length `409` and the seed `3`. -/
def t409_3 : Tree :=
  Tree.split 409 (
    Tree.add 5 (
      Tree.add 41 (
        Tree.leaf
          [(3, [Item.cof 3 1 2]), (5, [Item.pr 5 4909, Item.cof 5 4909 0])]
          [Item.pr 5 4909, Item.cof 3 1 2, Item.cof 5 4909 2, Item.cof 41 1 0]))) (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (409, [Item.pr 409 1637, Item.cof 409 1637 0])]
      [Item.pr 409 1637, Item.cof 3 1 2, Item.cof 409 1637 2])

/-- The tree for the length `409` and the seed `5`. -/
def t409_5 : Tree :=
  Tree.split 409 (
    Tree.add 41 (
      Tree.leaf
        [(5, [Item.pr 5 4909, Item.cof 5 4909 0])]
        [Item.pr 5 4909, Item.cof 5 4909 2, Item.cof 41 1 0])) (
    Tree.leaf
      [(5, [Item.pr 5 4909, Item.cof 5 4909 0]), (409, [Item.pr 409 1637, Item.cof 409 1637 0])]
      [Item.pr 5 4909, Item.pr 409 1637, Item.cof 5 4909 2, Item.cof 409 1637 2])

/-- The table. -/
def tab : List (ℕ × Tree × Tree) :=
  [(379, t379_3, t379_5),
   (383, t383_3, t383_5),
   (389, t389_3, t389_5),
   (397, t397_3, t397_5),
   (401, t401_3, t401_5),
   (409, t409_3, t409_5)]

/-- The lengths of the table. -/
def ls : List ℕ := [379, 383, 389, 397, 401, 409]

theorem tab_ls : tab.map Prod.fst = ls := rfl

theorem ok379 : tableOK pc [(379, t379_3, t379_5)] = true := by
  decide +kernel

theorem ok383 : tableOK pc [(383, t383_3, t383_5)] = true := by
  decide +kernel

theorem ok389 : tableOK pc [(389, t389_3, t389_5)] = true := by
  decide +kernel

theorem ok397 : tableOK pc [(397, t397_3, t397_5)] = true := by
  decide +kernel

theorem ok401 : tableOK pc [(401, t401_3, t401_5)] = true := by
  decide +kernel

theorem ok409 : tableOK pc [(409, t409_3, t409_5)] = true := by
  decide +kernel

theorem tab_ok : tableOK pc tab = true :=
  tableOK_cons ok379 <|
  tableOK_cons ok383 <|
  tableOK_cons ok389 <|
  tableOK_cons ok397 <|
  tableOK_cons ok401 <|
  tableOK_cons ok409 <|
  tableOK_nil pc

end OddPerfect.ImpTree.ImpureRowTreeD07

#print axioms OddPerfect.ImpTree.ImpureRowTreeD07.tab_ls
#print axioms OddPerfect.ImpTree.ImpureRowTreeD07.tab_ok
#print axioms OddPerfect.ImpTree.ImpureRowTreeD07.ok379
#print axioms OddPerfect.ImpTree.ImpureRowTreeD07.ok383
#print axioms OddPerfect.ImpTree.ImpureRowTreeD07.ok389
#print axioms OddPerfect.ImpTree.ImpureRowTreeD07.ok397
#print axioms OddPerfect.ImpTree.ImpureRowTreeD07.ok401
#print axioms OddPerfect.ImpTree.ImpureRowTreeD07.ok409
