import OddPerfect.ImpureRowTreeCheck

/-!
# Impure row tree certificates for the lengths 347, 349, 353, 359, 367, 373

Data for `OddPerfect.ImpTree.tableOK_sound`: for each length `l` a tree for the seed `3`
and a tree for the seed `5`, checked by kernel reduction. Restricted result (one odd prime
divides every ordinary index); no published source was checked; novelty not verified.
The odd perfect number conjecture remains open.
-/

namespace OddPerfect.ImpTree.ImpureRowTreeD06

open OddPerfect.ImpTree

/-- Pratt certificates for the large primes. -/
def pc : List (ℕ × ℕ × List ℕ) :=
  []

/-- The tree for the length `347` and the seed `3`. -/
def t347_3 : Tree :=
  Tree.add 347 (
    Tree.leaf
      [(3, [Item.pr 3 291481, Item.cof 3 291481 0]), (347, [Item.pr 347 152681,
          Item.cof 347 152681 0])]
      [Item.pr 3 291481, Item.pr 347 152681, Item.cof 3 291481 2, Item.cof 347 152681 2])

/-- The tree for the length `347` and the seed `5`. -/
def t347_5 : Tree :=
  Tree.add 347 (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (347, [Item.pr 347 152681, Item.cof 347 152681 0])]
      [Item.pr 347 152681, Item.cof 5 1 2, Item.cof 347 152681 2])

/-- The tree for the length `349` and the seed `3`. -/
def t349_3 : Tree :=
  Tree.split 349 (
    Tree.add 5 (
      Tree.add 7 (
        Tree.leaf
          [(3, [Item.cof 3 1 2]), (5, [Item.cof 5 1 2]), (7, [Item.pr 7 81667, Item.pr 7 127037])]
          [Item.pr 7 81667, Item.pr 7 127037, Item.cof 3 1 2, Item.cof 5 1 2,
              Item.cof 7 10374730679 2]))) (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (349, [Item.pr 349 3491, Item.pr 349 8377])]
      [Item.pr 349 3491, Item.pr 349 8377, Item.pr 349 259657, Item.cof 3 1 2,
          Item.cof 349 7593437091299 2])

/-- The tree for the length `349` and the seed `5`. -/
def t349_5 : Tree :=
  Tree.split 349 (
    Tree.add 7 (
      Tree.leaf
        [(5, [Item.cof 5 1 2]), (7, [Item.pr 7 81667, Item.pr 7 127037])]
        [Item.pr 7 81667, Item.pr 7 127037, Item.cof 5 1 2, Item.cof 7 10374730679 2])) (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (349, [Item.pr 349 3491, Item.pr 349 8377])]
      [Item.pr 349 3491, Item.pr 349 8377, Item.pr 349 259657, Item.cof 5 1 2,
          Item.cof 349 7593437091299 2])

/-- The tree for the length `353` and the seed `3`. -/
def t353_3 : Tree :=
  Tree.split 353 (
    Tree.add 59 (
      Tree.leaf
        [(3, [Item.pr 3 509027, Item.cof 3 509027 0]), (59, [Item.cof 59 1 2])]
        [Item.pr 3 509027, Item.cof 3 509027 2, Item.cof 59 1 2])) (
    Tree.leaf
      [(3, [Item.pr 3 509027, Item.cof 3 509027 0]), (353, [Item.pr 353 4943, Item.cof 353 4943 0])]
      [Item.pr 3 509027, Item.pr 353 4943, Item.cof 3 509027 2, Item.cof 353 4943 2])

/-- The tree for the length `353` and the seed `5`. -/
def t353_5 : Tree :=
  Tree.split 353 (
    Tree.add 3 (
      Tree.add 59 (
        Tree.leaf
          [(5, [Item.pr 5 235099, Item.cof 5 235099 0]), (3, [Item.pr 3 509027,
              Item.cof 3 509027 0]), (59, [Item.cof 59 1 2])]
          [Item.pr 5 235099, Item.pr 3 509027, Item.cof 5 235099 2, Item.cof 3 509027 2,
              Item.cof 59 1 2]))) (
    Tree.leaf
      [(5, [Item.pr 5 235099, Item.cof 5 235099 0]), (353, [Item.pr 353 4943, Item.cof 353 4943 0])]
      [Item.pr 5 235099, Item.pr 353 4943, Item.cof 5 235099 2, Item.cof 353 4943 2])

/-- The tree for the length `359` and the seed `3`. -/
def t359_3 : Tree :=
  Tree.add 359 (
    Tree.leaf
      [(3, [Item.pr 3 719, Item.cof 3 719 0]), (359, [Item.cof 359 1 2])]
      [Item.pr 3 719, Item.cof 3 719 2, Item.cof 359 1 2])

/-- The tree for the length `359` and the seed `5`. -/
def t359_5 : Tree :=
  Tree.add 359 (
    Tree.leaf
      [(5, [Item.pr 5 719, Item.cof 5 719 0]), (359, [Item.cof 359 1 2])]
      [Item.pr 5 719, Item.cof 5 719 2, Item.cof 359 1 2])

/-- The tree for the length `367` and the seed `3`. -/
def t367_3 : Tree :=
  Tree.add 367 (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (367, [Item.cof 367 1 2])]
      [Item.cof 3 1 2, Item.cof 367 1 2])

/-- The tree for the length `367` and the seed `5`. -/
def t367_5 : Tree :=
  Tree.add 367 (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (367, [Item.cof 367 1 2])]
      [Item.cof 5 1 2, Item.cof 367 1 2])

/-- The tree for the length `373` and the seed `3`. -/
def t373_3 : Tree :=
  Tree.split 373 (
    Tree.add 11 (
      Tree.add 17 (
        Tree.leaf
          [(3, [Item.cof 3 1 2]), (11, [Item.cof 11 1 2]), (17, [Item.cof 17 1 2])]
          [Item.cof 3 1 2, Item.cof 11 1 2, Item.cof 17 1 2]))) (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (373, [Item.pr 373 1493, Item.pr 373 2239])]
      [Item.pr 373 1493, Item.pr 373 2239, Item.pr 373 20143, Item.pr 373 26111,
          Item.pr 373 31333, Item.pr 373 229769, Item.pr 373 255133, Item.cof 3 1 2,
          Item.cof 373 3229398263240280538657236603011 2])

/-- The tree for the length `373` and the seed `5`. -/
def t373_5 : Tree :=
  Tree.split 373 (
    Tree.add 11 (
      Tree.add 17 (
        Tree.leaf
          [(5, [Item.pr 5 2239, Item.cof 5 2239 0]), (11, [Item.cof 11 1 2]), (17,
              [Item.cof 17 1 2])]
          [Item.pr 5 2239, Item.cof 5 2239 2, Item.cof 11 1 2, Item.cof 17 1 2]))) (
    Tree.leaf
      [(5, [Item.pr 5 2239, Item.cof 5 2239 0]), (373, [Item.pr 373 1493, Item.pr 373 2239])]
      [Item.pr 5 2239, Item.pr 373 1493, Item.pr 373 20143, Item.pr 373 26111, Item.pr 373 31333,
          Item.pr 373 229769, Item.pr 373 255133, Item.cof 5 2239 2,
          Item.cof 373 3229398263240280538657236603011 2])

/-- The table. -/
def tab : List (ℕ × Tree × Tree) :=
  [(347, t347_3, t347_5),
   (349, t349_3, t349_5),
   (353, t353_3, t353_5),
   (359, t359_3, t359_5),
   (367, t367_3, t367_5),
   (373, t373_3, t373_5)]

/-- The lengths of the table. -/
def ls : List ℕ := [347, 349, 353, 359, 367, 373]

theorem tab_ls : tab.map Prod.fst = ls := rfl

theorem ok347 : tableOK pc [(347, t347_3, t347_5)] = true := by
  decide +kernel

theorem ok349 : tableOK pc [(349, t349_3, t349_5)] = true := by
  decide +kernel

theorem ok353 : tableOK pc [(353, t353_3, t353_5)] = true := by
  decide +kernel

theorem ok359 : tableOK pc [(359, t359_3, t359_5)] = true := by
  decide +kernel

theorem ok367 : tableOK pc [(367, t367_3, t367_5)] = true := by
  decide +kernel

theorem ok373 : tableOK pc [(373, t373_3, t373_5)] = true := by
  decide +kernel

theorem tab_ok : tableOK pc tab = true :=
  tableOK_cons ok347 <|
  tableOK_cons ok349 <|
  tableOK_cons ok353 <|
  tableOK_cons ok359 <|
  tableOK_cons ok367 <|
  tableOK_cons ok373 <|
  tableOK_nil pc

end OddPerfect.ImpTree.ImpureRowTreeD06

#print axioms OddPerfect.ImpTree.ImpureRowTreeD06.tab_ls
#print axioms OddPerfect.ImpTree.ImpureRowTreeD06.tab_ok
#print axioms OddPerfect.ImpTree.ImpureRowTreeD06.ok347
#print axioms OddPerfect.ImpTree.ImpureRowTreeD06.ok349
#print axioms OddPerfect.ImpTree.ImpureRowTreeD06.ok353
#print axioms OddPerfect.ImpTree.ImpureRowTreeD06.ok359
#print axioms OddPerfect.ImpTree.ImpureRowTreeD06.ok367
#print axioms OddPerfect.ImpTree.ImpureRowTreeD06.ok373
