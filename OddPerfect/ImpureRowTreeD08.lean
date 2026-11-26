import OddPerfect.ImpureRowTreeCheck

/-!
# Impure row tree certificates for the lengths 419, 421, 431, 433, 439, 443

Data for `OddPerfect.ImpTree.tableOK_sound`: for each length `l` a tree for the seed `3`
and a tree for the seed `5`, checked by kernel reduction. Restricted result (one odd prime
divides every ordinary index); no published source was checked; novelty not verified.
The odd perfect number conjecture remains open.
-/

namespace OddPerfect.ImpTree.ImpureRowTreeD08

open OddPerfect.ImpTree

/-- Pratt certificates for the large primes. -/
def pc : List (ℕ × ℕ × List ℕ) :=
  []

/-- The tree for the length `419` and the seed `3`. -/
def t419_3 : Tree :=
  Tree.add 419 (
    Tree.leaf
      [(3, [Item.pr 3 839, Item.cof 3 839 0]), (419, [Item.cof 419 1 2])]
      [Item.pr 3 839, Item.cof 3 839 2, Item.cof 419 1 2])

/-- The tree for the length `419` and the seed `5`. -/
def t419_5 : Tree :=
  Tree.add 419 (
    Tree.leaf
      [(5, [Item.pr 5 839, Item.cof 5 839 0]), (419, [Item.cof 419 1 2])]
      [Item.pr 5 839, Item.cof 5 839 2, Item.cof 419 1 2])

/-- The tree for the length `421` and the seed `3`. -/
def t421_3 : Tree :=
  Tree.split 421 (
    Tree.add 211 (
      Tree.leaf
        [(3, [Item.cof 3 1 2]), (211, [Item.pr 211 88411, Item.cof 211 88411 0])]
        [Item.pr 211 88411, Item.cof 3 1 2, Item.cof 211 88411 2])) (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (421, [Item.pr 421 6737, Item.cof 421 6737 0])]
      [Item.pr 421 6737, Item.cof 3 1 2, Item.cof 421 6737 2])

/-- The tree for the length `421` and the seed `5`. -/
def t421_5 : Tree :=
  Tree.split 421 (
    Tree.add 211 (
      Tree.leaf
        [(211, [Item.pr 211 88411, Item.cof 211 88411 0])]
        [Item.pr 211 88411, Item.cof 5 1 0, Item.cof 211 88411 2])) (
    Tree.leaf
      [(421, [Item.pr 421 6737, Item.cof 421 6737 0])]
      [Item.pr 421 6737, Item.cof 5 1 0, Item.cof 421 6737 2])

/-- The tree for the length `431` and the seed `3`. -/
def t431_3 : Tree :=
  Tree.add 431 (
    Tree.leaf
      [(3, [Item.pr 3 863, Item.pr 3 31033]), (431, [Item.cof 431 1 2])]
      [Item.pr 3 863, Item.pr 3 31033, Item.cof 3 26781479 2, Item.cof 431 1 2])

/-- The tree for the length `431` and the seed `5`. -/
def t431_5 : Tree :=
  Tree.add 431 (
    Tree.leaf
      [(5, [Item.pr 5 3449, Item.pr 5 494789]), (431, [Item.cof 431 1 2])]
      [Item.pr 5 3449, Item.pr 5 494789, Item.pr 5 598229, Item.cof 5 1020894096820769 2,
          Item.cof 431 1 2])

/-- The tree for the length `433` and the seed `3`. -/
def t433_3 : Tree :=
  Tree.split 433 (
    Tree.add 7 (
      Tree.add 31 (
        Tree.leaf
          [(3, [Item.pr 3 218233, Item.cof 3 218233 0]), (7, [Item.pr 7 1733, Item.pr 7 885919]),
              (31, [Item.pr 31 1733, Item.pr 31 49363])]
          [Item.pr 3 218233, Item.pr 7 1733, Item.pr 7 885919, Item.pr 31 49363,
              Item.cof 3 218233 2, Item.cof 7 1535297627 2, Item.cof 31 85546079 2]))) (
    Tree.leaf
      [(3, [Item.pr 3 218233, Item.cof 3 218233 0]), (433, [Item.pr 433 1733, Item.pr 433 28579])]
      [Item.pr 3 218233, Item.pr 433 1733, Item.pr 433 28579, Item.pr 433 53693,
          Item.cof 3 218233 2, Item.cof 433 2659275064051 2])

/-- The tree for the length `433` and the seed `5`. -/
def t433_5 : Tree :=
  Tree.split 433 (
    Tree.add 7 (
      Tree.add 31 (
        Tree.leaf
          [(5, [Item.pr 5 25981, Item.cof 5 25981 0]), (7, [Item.pr 7 1733, Item.pr 7 885919]),
              (31, [Item.pr 31 1733, Item.pr 31 49363])]
          [Item.pr 5 25981, Item.pr 7 1733, Item.pr 7 885919, Item.pr 31 49363,
              Item.cof 5 25981 0, Item.cof 7 1535297627 2, Item.cof 31 85546079 2]))) (
    Tree.leaf
      [(5, [Item.pr 5 25981, Item.cof 5 25981 0]), (433, [Item.pr 433 1733, Item.pr 433 28579])]
      [Item.pr 5 25981, Item.pr 433 1733, Item.pr 433 28579, Item.pr 433 53693,
          Item.cof 5 25981 0, Item.cof 433 2659275064051 2])

/-- The tree for the length `439` and the seed `3`. -/
def t439_3 : Tree :=
  Tree.add 439 (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (439, [Item.cof 439 1 2])]
      [Item.cof 3 1 2, Item.cof 439 1 2])

/-- The tree for the length `439` and the seed `5`. -/
def t439_5 : Tree :=
  Tree.add 439 (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (439, [Item.cof 439 1 2])]
      [Item.cof 5 1 2, Item.cof 439 1 2])

/-- The tree for the length `443` and the seed `3`. -/
def t443_3 : Tree :=
  Tree.add 443 (
    Tree.leaf
      [(3, [Item.pr 3 887, Item.pr 3 298583]), (443, [Item.cof 443 1 2])]
      [Item.pr 3 887, Item.pr 3 298583, Item.cof 3 264843121 2, Item.cof 443 1 2])

/-- The tree for the length `443` and the seed `5`. -/
def t443_5 : Tree :=
  Tree.add 443 (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (443, [Item.cof 443 1 2])]
      [Item.cof 5 1 2, Item.cof 443 1 2])

/-- The table. -/
def tab : List (ℕ × Tree × Tree) :=
  [(419, t419_3, t419_5),
   (421, t421_3, t421_5),
   (431, t431_3, t431_5),
   (433, t433_3, t433_5),
   (439, t439_3, t439_5),
   (443, t443_3, t443_5)]

/-- The lengths of the table. -/
def ls : List ℕ := [419, 421, 431, 433, 439, 443]

theorem tab_ls : tab.map Prod.fst = ls := rfl

theorem ok419 : tableOK pc [(419, t419_3, t419_5)] = true := by
  decide +kernel

theorem ok421 : tableOK pc [(421, t421_3, t421_5)] = true := by
  decide +kernel

theorem ok431 : tableOK pc [(431, t431_3, t431_5)] = true := by
  decide +kernel

theorem ok433 : tableOK pc [(433, t433_3, t433_5)] = true := by
  decide +kernel

theorem ok439 : tableOK pc [(439, t439_3, t439_5)] = true := by
  decide +kernel

theorem ok443 : tableOK pc [(443, t443_3, t443_5)] = true := by
  decide +kernel

theorem tab_ok : tableOK pc tab = true :=
  tableOK_cons ok419 <|
  tableOK_cons ok421 <|
  tableOK_cons ok431 <|
  tableOK_cons ok433 <|
  tableOK_cons ok439 <|
  tableOK_cons ok443 <|
  tableOK_nil pc

end OddPerfect.ImpTree.ImpureRowTreeD08

#print axioms OddPerfect.ImpTree.ImpureRowTreeD08.tab_ls
#print axioms OddPerfect.ImpTree.ImpureRowTreeD08.tab_ok
#print axioms OddPerfect.ImpTree.ImpureRowTreeD08.ok419
#print axioms OddPerfect.ImpTree.ImpureRowTreeD08.ok421
#print axioms OddPerfect.ImpTree.ImpureRowTreeD08.ok431
#print axioms OddPerfect.ImpTree.ImpureRowTreeD08.ok433
#print axioms OddPerfect.ImpTree.ImpureRowTreeD08.ok439
#print axioms OddPerfect.ImpTree.ImpureRowTreeD08.ok443
