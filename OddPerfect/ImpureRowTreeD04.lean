import OddPerfect.ImpureRowTreeCheck

/-!
# Impure row tree certificates for the lengths 269, 271, 277, 281, 283, 293

Data for `OddPerfect.ImpTree.tableOK_sound`: for each length `l` a tree for the seed `3`
and a tree for the seed `5`, checked by kernel reduction. Restricted result (one odd prime
divides every ordinary index); no published source was checked; novelty not verified.
The odd perfect number conjecture remains open.
-/

namespace OddPerfect.ImpTree.ImpureRowTreeD04

open OddPerfect.ImpTree

/-- Pratt certificates for the large primes. -/
def pc : List (ℕ × ℕ × List ℕ) :=
  []

/-- The tree for the length `269` and the seed `3`. -/
def t269_3 : Tree :=
  Tree.split 269 (
    Tree.add 5 (
      Tree.leaf
        [(3, [Item.pr 3 10223, Item.pr 3 262007]), (5, [Item.pr 5 3229, Item.cof 5 3229 0])]
        [Item.pr 3 10223, Item.pr 3 262007, Item.pr 5 3229, Item.cof 3 2678497561 2,
            Item.cof 5 3229 2])) (
    Tree.leaf
      [(3, [Item.pr 3 10223, Item.pr 3 262007]), (269, [Item.pr 269 108677, Item.cof 269 108677 0])]
      [Item.pr 3 10223, Item.pr 3 262007, Item.pr 269 108677, Item.cof 3 2678497561 2,
          Item.cof 269 108677 2])

/-- The tree for the length `269` and the seed `5`. -/
def t269_5 : Tree :=
  Tree.split 269 (
    Tree.add 3 (
      Tree.leaf
        [(5, [Item.pr 5 3229, Item.cof 5 3229 0]), (3, [Item.pr 3 10223, Item.pr 3 262007])]
        [Item.pr 5 3229, Item.pr 3 10223, Item.pr 3 262007, Item.cof 5 3229 2,
            Item.cof 3 2678497561 2])) (
    Tree.leaf
      [(5, [Item.pr 5 3229, Item.cof 5 3229 0]), (269, [Item.pr 269 108677, Item.cof 269 108677 0])]
      [Item.pr 5 3229, Item.pr 269 108677, Item.cof 5 3229 2, Item.cof 269 108677 2])

/-- The tree for the length `271` and the seed `3`. -/
def t271_3 : Tree :=
  Tree.add 271 (
    Tree.leaf
      [(3, [Item.pr 3 3253, Item.cof 3 3253 0]), (271, [Item.pr 271 4337, Item.cof 271 4337 0])]
      [Item.pr 3 3253, Item.pr 271 4337, Item.cof 3 3253 2, Item.cof 271 4337 2])

/-- The tree for the length `271` and the seed `5`. -/
def t271_5 : Tree :=
  Tree.add 271 (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (271, [Item.pr 271 4337, Item.cof 271 4337 0])]
      [Item.pr 271 4337, Item.cof 5 1 2, Item.cof 271 4337 2])

/-- The tree for the length `277` and the seed `3`. -/
def t277_3 : Tree :=
  Tree.split 277 (
    Tree.add 139 (
      Tree.leaf
        [(3, [Item.cof 3 1 2]), (139, [Item.pr 139 1109, Item.cof 139 1109 0])]
        [Item.pr 139 1109, Item.cof 3 1 2, Item.cof 139 1109 2])) (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (277, [Item.pr 277 1109, Item.cof 277 1109 0])]
      [Item.pr 277 1109, Item.cof 3 1 2, Item.cof 277 1109 2])

/-- The tree for the length `277` and the seed `5`. -/
def t277_5 : Tree :=
  Tree.split 277 (
    Tree.add 139 (
      Tree.leaf
        [(5, [Item.cof 5 1 2]), (139, [Item.pr 139 1109, Item.cof 139 1109 0])]
        [Item.pr 139 1109, Item.cof 5 1 2, Item.cof 139 1109 2])) (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (277, [Item.pr 277 1109, Item.cof 277 1109 0])]
      [Item.pr 277 1109, Item.cof 5 1 2, Item.cof 277 1109 2])

/-- The tree for the length `281` and the seed `3`. -/
def t281_3 : Tree :=
  Tree.split 281 (
    Tree.add 47 (
      Tree.leaf
        [(3, [Item.pr 3 563, Item.pr 3 3373]), (47, [Item.pr 47 563, Item.pr 47 558629])]
        [Item.pr 3 563, Item.pr 3 3373, Item.pr 3 422063, Item.pr 3 434989, Item.pr 47 558629,
            Item.cof 3 348642472028230693 2, Item.cof 47 314508127 2])) (
    Tree.leaf
      [(3, [Item.pr 3 563, Item.pr 3 3373]), (281, [Item.pr 281 563, Item.pr 281 3373])]
      [Item.pr 3 563, Item.pr 3 3373, Item.pr 3 422063, Item.pr 3 434989,
          Item.cof 3 348642472028230693 2, Item.cof 281 1898999 2])

/-- The tree for the length `281` and the seed `5`. -/
def t281_5 : Tree :=
  Tree.split 281 (
    Tree.add 3 (
      Tree.add 47 (
        Tree.leaf
          [(5, [Item.cof 5 1 2]), (3, [Item.pr 3 563, Item.pr 3 3373]), (47, [Item.pr 47 563,
              Item.pr 47 558629])]
          [Item.pr 3 563, Item.pr 3 3373, Item.pr 3 422063, Item.pr 3 434989, Item.pr 47 558629,
              Item.cof 5 1 2, Item.cof 3 348642472028230693 2, Item.cof 47 314508127 2]))) (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (281, [Item.pr 281 563, Item.pr 281 3373])]
      [Item.pr 281 563, Item.pr 281 3373, Item.cof 5 1 2, Item.cof 281 1898999 2])

/-- The tree for the length `283` and the seed `3`. -/
def t283_3 : Tree :=
  Tree.add 283 (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (283, [Item.pr 283 14717, Item.pr 283 45281])]
      [Item.pr 283 14717, Item.pr 283 45281, Item.pr 283 227533, Item.pr 283 238853,
          Item.cof 3 1 2, Item.cof 283 36216826505583812573 2])

/-- The tree for the length `283` and the seed `5`. -/
def t283_5 : Tree :=
  Tree.add 283 (
    Tree.leaf
      [(5, [Item.pr 5 1699, Item.pr 5 451669]), (283, [Item.pr 283 14717, Item.pr 283 45281])]
      [Item.pr 5 1699, Item.pr 5 451669, Item.pr 283 14717, Item.pr 283 45281, Item.pr 283 227533,
          Item.pr 283 238853, Item.cof 5 767385631 2, Item.cof 283 36216826505583812573 2])

/-- The tree for the length `293` and the seed `3`. -/
def t293_3 : Tree :=
  Tree.split 293 (
    Tree.add 7 (
      Tree.leaf
        [(3, [Item.pr 3 587, Item.cof 3 587 0]), (7, [Item.pr 7 587, Item.pr 7 15823])]
        [Item.pr 3 587, Item.pr 7 15823, Item.cof 3 587 2, Item.cof 7 9288101 0])) (
    Tree.leaf
      [(3, [Item.pr 3 587, Item.cof 3 587 0]), (293, [Item.pr 293 587, Item.pr 293 202757])]
      [Item.pr 3 587, Item.pr 293 202757, Item.pr 293 431297, Item.cof 3 587 2,
          Item.cof 293 51332261181623 2])

/-- The tree for the length `293` and the seed `5`. -/
def t293_5 : Tree :=
  Tree.split 293 (
    Tree.add 3 (
      Tree.add 7 (
        Tree.leaf
          [(5, [Item.pr 5 1759, Item.pr 5 520369]), (3, [Item.pr 3 587, Item.cof 3 587 0]), (7,
              [Item.pr 7 587, Item.pr 7 15823])]
          [Item.pr 5 1759, Item.pr 5 520369, Item.pr 3 587, Item.pr 7 15823,
              Item.cof 5 915329071 2, Item.cof 3 587 2, Item.cof 7 9288101 0]))) (
    Tree.leaf
      [(5, [Item.pr 5 1759, Item.pr 5 520369]), (293, [Item.pr 293 587, Item.pr 293 202757])]
      [Item.pr 5 1759, Item.pr 5 520369, Item.pr 293 587, Item.pr 293 202757, Item.pr 293 431297,
          Item.cof 5 915329071 2, Item.cof 293 51332261181623 2])

/-- The table. -/
def tab : List (ℕ × Tree × Tree) :=
  [(269, t269_3, t269_5),
   (271, t271_3, t271_5),
   (277, t277_3, t277_5),
   (281, t281_3, t281_5),
   (283, t283_3, t283_5),
   (293, t293_3, t293_5)]

/-- The lengths of the table. -/
def ls : List ℕ := [269, 271, 277, 281, 283, 293]

theorem tab_ls : tab.map Prod.fst = ls := rfl

theorem ok269 : tableOK pc [(269, t269_3, t269_5)] = true := by
  decide +kernel

theorem ok271 : tableOK pc [(271, t271_3, t271_5)] = true := by
  decide +kernel

theorem ok277 : tableOK pc [(277, t277_3, t277_5)] = true := by
  decide +kernel

theorem ok281 : tableOK pc [(281, t281_3, t281_5)] = true := by
  decide +kernel

theorem ok283 : tableOK pc [(283, t283_3, t283_5)] = true := by
  decide +kernel

theorem ok293 : tableOK pc [(293, t293_3, t293_5)] = true := by
  decide +kernel

theorem tab_ok : tableOK pc tab = true :=
  tableOK_cons ok269 <|
  tableOK_cons ok271 <|
  tableOK_cons ok277 <|
  tableOK_cons ok281 <|
  tableOK_cons ok283 <|
  tableOK_cons ok293 <|
  tableOK_nil pc

end OddPerfect.ImpTree.ImpureRowTreeD04

#print axioms OddPerfect.ImpTree.ImpureRowTreeD04.tab_ls
#print axioms OddPerfect.ImpTree.ImpureRowTreeD04.tab_ok
#print axioms OddPerfect.ImpTree.ImpureRowTreeD04.ok269
#print axioms OddPerfect.ImpTree.ImpureRowTreeD04.ok271
#print axioms OddPerfect.ImpTree.ImpureRowTreeD04.ok277
#print axioms OddPerfect.ImpTree.ImpureRowTreeD04.ok281
#print axioms OddPerfect.ImpTree.ImpureRowTreeD04.ok283
#print axioms OddPerfect.ImpTree.ImpureRowTreeD04.ok293
