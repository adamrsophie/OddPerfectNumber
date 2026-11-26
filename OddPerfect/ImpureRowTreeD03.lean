import OddPerfect.ImpureRowTreeCheck

/-!
# Impure row tree certificates for the lengths 233, 239, 241, 251, 257, 263

Data for `OddPerfect.ImpTree.tableOK_sound`: for each length `l` a tree for the seed `3`
and a tree for the seed `5`, checked by kernel reduction. Restricted result (one odd prime
divides every ordinary index); no published source was checked; novelty not verified.
The odd perfect number conjecture remains open.
-/

namespace OddPerfect.ImpTree.ImpureRowTreeD03

open OddPerfect.ImpTree

/-- Pratt certificates for the large primes. -/
def pc : List (ℕ × ℕ × List ℕ) :=
  []

/-- The tree for the length `233` and the seed `3`. -/
def t233_3 : Tree :=
  Tree.split 233 (
    Tree.add 13 (
      Tree.leaf
        [(3, [Item.pr 3 467, Item.cof 3 467 0]), (13, [Item.pr 13 467, Item.pr 13 647741])]
        [Item.pr 3 467, Item.pr 13 647741, Item.pr 13 712981, Item.cof 3 467 2,
            Item.cof 13 215673221105107 2])) (
    Tree.leaf
      [(3, [Item.pr 3 467, Item.cof 3 467 0]), (233, [Item.pr 233 467, Item.pr 233 1399])]
      [Item.pr 3 467, Item.pr 233 1399, Item.pr 233 2797, Item.cof 3 467 2,
          Item.cof 233 1827372401 2])

/-- The tree for the length `233` and the seed `5`. -/
def t233_5 : Tree :=
  Tree.split 233 (
    Tree.add 3 (
      Tree.add 13 (
        Tree.leaf
          [(5, [Item.cof 5 1 2]), (3, [Item.pr 3 467, Item.cof 3 467 0]), (13, [Item.pr 13 467,
              Item.pr 13 647741])]
          [Item.pr 3 467, Item.pr 13 647741, Item.pr 13 712981, Item.cof 5 1 2, Item.cof 3 467 2,
              Item.cof 13 215673221105107 2]))) (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (233, [Item.pr 233 467, Item.pr 233 1399])]
      [Item.pr 233 467, Item.pr 233 1399, Item.pr 233 2797, Item.cof 5 1 2,
          Item.cof 233 1827372401 2])

/-- The tree for the length `239` and the seed `3`. -/
def t239_3 : Tree :=
  Tree.add 239 (
    Tree.leaf
      [(3, [Item.pr 3 479, Item.pr 3 17209]), (239, [Item.cof 239 1 2])]
      [Item.pr 3 479, Item.pr 3 17209, Item.cof 3 8243111 2, Item.cof 239 1 2])

/-- The tree for the length `239` and the seed `5`. -/
def t239_5 : Tree :=
  Tree.add 239 (
    Tree.leaf
      [(5, [Item.pr 5 479, Item.cof 5 479 0]), (239, [Item.cof 239 1 2])]
      [Item.pr 5 479, Item.cof 5 479 2, Item.cof 239 1 2])

/-- The tree for the length `241` and the seed `3`. -/
def t241_3 : Tree :=
  Tree.split 241 (
    Tree.add 11 (
      Tree.leaf
        [(3, [Item.cof 3 1 2]), (11, [Item.cof 11 1 2])]
        [Item.cof 3 1 2, Item.cof 11 1 2])) (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (241, [Item.pr 241 1447, Item.pr 241 191837])]
      [Item.pr 241 1447, Item.pr 241 191837, Item.cof 3 1 2, Item.cof 241 277588139 2])

/-- The tree for the length `241` and the seed `5`. -/
def t241_5 : Tree :=
  Tree.split 241 (
    Tree.add 11 (
      Tree.leaf
        [(5, [Item.pr 5 79531, Item.pr 5 578401]), (11, [Item.cof 11 1 2])]
        [Item.pr 5 79531, Item.pr 5 578401, Item.pr 5 882061, Item.cof 5 40575520408547791 2,
            Item.cof 11 1 2])) (
    Tree.leaf
      [(5, [Item.pr 5 79531, Item.pr 5 578401]), (241, [Item.pr 241 1447, Item.pr 241 191837])]
      [Item.pr 5 79531, Item.pr 5 578401, Item.pr 5 882061, Item.pr 241 1447, Item.pr 241 191837,
          Item.cof 5 40575520408547791 2, Item.cof 241 277588139 2])

/-- The tree for the length `251` and the seed `3`. -/
def t251_3 : Tree :=
  Tree.add 251 (
    Tree.leaf
      [(3, [Item.pr 3 503, Item.cof 3 503 0]), (251, [Item.cof 251 1 2])]
      [Item.pr 3 503, Item.cof 3 503 2, Item.cof 251 1 2])

/-- The tree for the length `251` and the seed `5`. -/
def t251_5 : Tree :=
  Tree.add 251 (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (251, [Item.cof 251 1 2])]
      [Item.cof 5 1 2, Item.cof 251 1 2])

/-- The tree for the length `257` and the seed `3`. -/
def t257_3 : Tree :=
  Tree.split 257 (
    Tree.add 43 (
      Tree.leaf
        [(3, [Item.pr 3 120277, Item.cof 3 120277 0]), (43, [Item.cof 43 1 2])]
        [Item.pr 3 120277, Item.cof 3 120277 2, Item.cof 43 1 2])) (
    Tree.leaf
      [(3, [Item.pr 3 120277, Item.cof 3 120277 0]), (257, [Item.pr 257 21589,
          Item.cof 257 21589 0])]
      [Item.pr 3 120277, Item.pr 257 21589, Item.cof 3 120277 2, Item.cof 257 21589 2])

/-- The tree for the length `257` and the seed `5`. -/
def t257_5 : Tree :=
  Tree.split 257 (
    Tree.add 3 (
      Tree.add 43 (
        Tree.leaf
          [(5, [Item.cof 5 1 2]), (3, [Item.pr 3 120277, Item.cof 3 120277 0]), (43,
              [Item.cof 43 1 2])]
          [Item.pr 3 120277, Item.cof 5 1 2, Item.cof 3 120277 2, Item.cof 43 1 2]))) (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (257, [Item.pr 257 21589, Item.cof 257 21589 0])]
      [Item.pr 257 21589, Item.cof 5 1 2, Item.cof 257 21589 2])

/-- The tree for the length `263` and the seed `3`. -/
def t263_3 : Tree :=
  Tree.add 263 (
    Tree.leaf
      [(3, [Item.pr 3 53653, Item.pr 3 78901]), (263, [Item.cof 263 1 2])]
      [Item.pr 3 53653, Item.pr 3 78901, Item.cof 3 4233275353 2, Item.cof 263 1 2])

/-- The tree for the length `263` and the seed `5`. -/
def t263_5 : Tree :=
  Tree.add 263 (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (263, [Item.cof 263 1 2])]
      [Item.cof 5 1 2, Item.cof 263 1 2])

/-- The table. -/
def tab : List (ℕ × Tree × Tree) :=
  [(233, t233_3, t233_5),
   (239, t239_3, t239_5),
   (241, t241_3, t241_5),
   (251, t251_3, t251_5),
   (257, t257_3, t257_5),
   (263, t263_3, t263_5)]

/-- The lengths of the table. -/
def ls : List ℕ := [233, 239, 241, 251, 257, 263]

theorem tab_ls : tab.map Prod.fst = ls := rfl

theorem ok233 : tableOK pc [(233, t233_3, t233_5)] = true := by
  decide +kernel

theorem ok239 : tableOK pc [(239, t239_3, t239_5)] = true := by
  decide +kernel

theorem ok241 : tableOK pc [(241, t241_3, t241_5)] = true := by
  decide +kernel

theorem ok251 : tableOK pc [(251, t251_3, t251_5)] = true := by
  decide +kernel

theorem ok257 : tableOK pc [(257, t257_3, t257_5)] = true := by
  decide +kernel

theorem ok263 : tableOK pc [(263, t263_3, t263_5)] = true := by
  decide +kernel

theorem tab_ok : tableOK pc tab = true :=
  tableOK_cons ok233 <|
  tableOK_cons ok239 <|
  tableOK_cons ok241 <|
  tableOK_cons ok251 <|
  tableOK_cons ok257 <|
  tableOK_cons ok263 <|
  tableOK_nil pc

end OddPerfect.ImpTree.ImpureRowTreeD03

#print axioms OddPerfect.ImpTree.ImpureRowTreeD03.tab_ls
#print axioms OddPerfect.ImpTree.ImpureRowTreeD03.tab_ok
#print axioms OddPerfect.ImpTree.ImpureRowTreeD03.ok233
#print axioms OddPerfect.ImpTree.ImpureRowTreeD03.ok239
#print axioms OddPerfect.ImpTree.ImpureRowTreeD03.ok241
#print axioms OddPerfect.ImpTree.ImpureRowTreeD03.ok251
#print axioms OddPerfect.ImpTree.ImpureRowTreeD03.ok257
#print axioms OddPerfect.ImpTree.ImpureRowTreeD03.ok263
