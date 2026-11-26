import OddPerfect.ImpureRowTreeCheck

/-!
# Impure row tree certificates for the lengths 127, 131, 137, 139, 149, 151, 157, 163, 167, 173,
    179, 181, 191, 193, 197, 199, 211, 223, 227, 229

Data for `OddPerfect.ImpTree.tableOK_sound`: for each length `l` a tree for the seed `3`
and a tree for the seed `5`, checked by kernel reduction. Restricted result (one odd prime
divides every ordinary index); no published source was checked; novelty not verified.
The odd perfect number conjecture remains open.
-/

namespace OddPerfect.ImpTree.ImpureRowTreeD02

open OddPerfect.ImpTree

/-- Pratt certificates for the large primes. -/
def pc : List (ℕ × ℕ × List ℕ) :=
  []

/-- The tree for the length `127` and the seed `3`. -/
def t127_3 : Tree :=
  Tree.add 127 (
    Tree.leaf
      [(3, [Item.pr 3 5843, Item.pr 3 681229]), (127, [Item.pr 127 509, Item.pr 127 22861])]
      [Item.pr 3 5843, Item.pr 3 681229, Item.pr 127 509, Item.pr 127 22861,
          Item.cof 3 3980421047 2, Item.cof 127 11636249 2])

/-- The tree for the length `127` and the seed `5`. -/
def t127_5 : Tree :=
  Tree.add 127 (
    Tree.leaf
      [(127, [Item.pr 127 509, Item.pr 127 22861])]
      [Item.pr 127 509, Item.pr 127 22861, Item.cof 5 1 0, Item.cof 127 11636249 2])

/-- The tree for the length `131` and the seed `3`. -/
def t131_3 : Tree :=
  Tree.add 131 (
    Tree.leaf
      [(3, [Item.pr 3 263, Item.cof 3 263 0]), (131, [Item.pr 131 1049, Item.cof 131 1049 0])]
      [Item.pr 3 263, Item.pr 131 1049, Item.cof 3 263 0, Item.cof 131 1049 2])

/-- The tree for the length `131` and the seed `5`. -/
def t131_5 : Tree :=
  Tree.add 131 (
    Tree.leaf
      [(5, [Item.pr 5 2621, Item.cof 5 2621 0]), (131, [Item.pr 131 1049, Item.cof 131 1049 0])]
      [Item.pr 5 2621, Item.pr 131 1049, Item.cof 5 2621 2, Item.cof 131 1049 2])

/-- The tree for the length `137` and the seed `3`. -/
def t137_3 : Tree :=
  Tree.split 137 (
    Tree.add 23 (
      Tree.leaf
        [(3, [Item.pr 3 4933, Item.cof 3 4933 0]), (23, [Item.pr 23 47129, Item.cof 23 47129 0])]
        [Item.pr 3 4933, Item.pr 23 47129, Item.cof 3 4933 2, Item.cof 23 47129 0])) (
    Tree.leaf
      [(3, [Item.pr 3 4933, Item.cof 3 4933 0]), (137, [Item.pr 137 1097, Item.pr 137 124123])]
      [Item.pr 3 4933, Item.pr 137 1097, Item.pr 137 124123, Item.cof 3 4933 2,
          Item.cof 137 136162931 2])

/-- The tree for the length `137` and the seed `5`. -/
def t137_5 : Tree :=
  Tree.split 137 (
    Tree.add 3 (
      Tree.add 23 (
        Tree.leaf
          [(5, [Item.pr 5 20551, Item.pr 5 603349]), (3, [Item.pr 3 4933, Item.cof 3 4933 0]),
              (23, [Item.pr 23 47129, Item.cof 23 47129 0])]
          [Item.pr 5 20551, Item.pr 5 603349, Item.pr 3 4933, Item.pr 23 47129,
              Item.cof 5 12399425299 2, Item.cof 3 4933 2, Item.cof 23 47129 0]))) (
    Tree.leaf
      [(5, [Item.pr 5 20551, Item.pr 5 603349]), (137, [Item.pr 137 1097, Item.pr 137 124123])]
      [Item.pr 5 20551, Item.pr 5 603349, Item.pr 137 1097, Item.pr 137 124123,
          Item.cof 5 12399425299 2, Item.cof 137 136162931 2])

/-- The tree for the length `139` and the seed `3`. -/
def t139_3 : Tree :=
  Tree.add 139 (
    Tree.leaf
      [(3, [Item.pr 3 1669, Item.cof 3 1669 0]), (139, [Item.pr 139 557, Item.cof 139 557 0])]
      [Item.pr 3 1669, Item.pr 139 557, Item.cof 3 1669 2, Item.cof 139 557 2])

/-- The tree for the length `139` and the seed `5`. -/
def t139_5 : Tree :=
  Tree.add 139 (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (139, [Item.pr 139 557, Item.cof 139 557 0])]
      [Item.pr 139 557, Item.cof 5 1 2, Item.cof 139 557 2])

/-- The tree for the length `149` and the seed `3`. -/
def t149_3 : Tree :=
  Tree.split 149 (
    Tree.add 5 (
      Tree.leaf
        [(3, [Item.pr 3 7451, Item.cof 3 7451 0])]
        [Item.pr 3 7451, Item.cof 3 7451 2, Item.cof 5 1 0])) (
    Tree.leaf
      [(3, [Item.pr 3 7451, Item.cof 3 7451 0]), (149, [Item.pr 149 1193, Item.cof 149 1193 0])]
      [Item.pr 3 7451, Item.pr 149 1193, Item.cof 3 7451 2, Item.cof 149 1193 2])

/-- The tree for the length `149` and the seed `5`. -/
def t149_5 : Tree :=
  Tree.split 149 (
    Tree.add 3 (
      Tree.leaf
        [(3, [Item.pr 3 7451, Item.cof 3 7451 0])]
        [Item.pr 3 7451, Item.cof 5 1 0, Item.cof 3 7451 2])) (
    Tree.leaf
      [(149, [Item.pr 149 1193, Item.cof 149 1193 0])]
      [Item.pr 149 1193, Item.cof 5 1 0, Item.cof 149 1193 2])

/-- The tree for the length `151` and the seed `3`. -/
def t151_3 : Tree :=
  Tree.add 151 (
    Tree.leaf
      [(3, [Item.pr 3 1511, Item.cof 3 1511 0]), (151, [Item.pr 151 2417, Item.pr 151 15101])]
      [Item.pr 3 1511, Item.pr 151 2417, Item.pr 151 15101, Item.cof 3 1511 2,
          Item.cof 151 36499117 2])

/-- The tree for the length `151` and the seed `5`. -/
def t151_5 : Tree :=
  Tree.add 151 (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (151, [Item.pr 151 2417, Item.pr 151 15101])]
      [Item.pr 151 2417, Item.pr 151 15101, Item.cof 5 1 2, Item.cof 151 36499117 2])

/-- The tree for the length `157` and the seed `3`. -/
def t157_3 : Tree :=
  Tree.split 157 (
    Tree.add 79 (
      Tree.leaf
        [(3, [Item.pr 3 9421, Item.cof 3 9421 0]), (79, [Item.pr 79 1571, Item.cof 79 1571 0])]
        [Item.pr 3 9421, Item.pr 79 1571, Item.cof 3 9421 2, Item.cof 79 1571 2])) (
    Tree.leaf
      [(3, [Item.pr 3 9421, Item.cof 3 9421 0]), (157, [Item.pr 157 86351, Item.cof 157 86351 0])]
      [Item.pr 3 9421, Item.pr 157 86351, Item.cof 3 9421 2, Item.cof 157 86351 2])

/-- The tree for the length `157` and the seed `5`. -/
def t157_5 : Tree :=
  Tree.split 157 (
    Tree.add 79 (
      Tree.leaf
        [(5, [Item.pr 5 32029, Item.cof 5 32029 0]), (79, [Item.pr 79 1571, Item.cof 79 1571 0])]
        [Item.pr 5 32029, Item.pr 79 1571, Item.cof 5 32029 2, Item.cof 79 1571 2])) (
    Tree.leaf
      [(5, [Item.pr 5 32029, Item.cof 5 32029 0]), (157, [Item.pr 157 86351, Item.cof 157 86351 0])]
      [Item.pr 5 32029, Item.pr 157 86351, Item.cof 5 32029 2, Item.cof 157 86351 2])

/-- The tree for the length `163` and the seed `3`. -/
def t163_3 : Tree :=
  Tree.add 163 (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (163, [Item.pr 163 653, Item.pr 163 2609])]
      [Item.pr 163 653, Item.pr 163 2609, Item.pr 163 41729, Item.cof 3 1 2,
          Item.cof 163 71092737533 2])

/-- The tree for the length `163` and the seed `5`. -/
def t163_5 : Tree :=
  Tree.add 163 (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (163, [Item.pr 163 653, Item.pr 163 2609])]
      [Item.pr 163 653, Item.pr 163 2609, Item.pr 163 41729, Item.cof 5 1 2,
          Item.cof 163 71092737533 2])

/-- The tree for the length `167` and the seed `3`. -/
def t167_3 : Tree :=
  Tree.add 167 (
    Tree.leaf
      [(3, [Item.pr 3 58451, Item.pr 3 88177]), (167, [Item.pr 167 16033, Item.cof 167 16033 0])]
      [Item.pr 3 58451, Item.pr 3 88177, Item.pr 167 16033, Item.cof 3 5154033827 2,
          Item.cof 167 16033 2])

/-- The tree for the length `167` and the seed `5`. -/
def t167_5 : Tree :=
  Tree.add 167 (
    Tree.leaf
      [(5, [Item.pr 5 18371, Item.pr 5 53441]), (167, [Item.pr 167 16033, Item.cof 167 16033 0])]
      [Item.pr 5 18371, Item.pr 5 53441, Item.pr 167 16033, Item.cof 5 981764611 0,
          Item.cof 167 16033 2])

/-- The tree for the length `173` and the seed `3`. -/
def t173_3 : Tree :=
  Tree.split 173 (
    Tree.add 29 (
      Tree.leaf
        [(3, [Item.pr 3 347, Item.pr 3 762239]), (29, [Item.pr 29 347, Item.pr 29 58129])]
        [Item.pr 3 347, Item.pr 3 762239, Item.pr 29 58129, Item.cof 3 264496933 2,
            Item.cof 29 20170763 2])) (
    Tree.leaf
      [(3, [Item.pr 3 347, Item.pr 3 762239]), (173, [Item.pr 173 347, Item.pr 173 685081])]
      [Item.pr 3 347, Item.pr 3 762239, Item.pr 173 685081, Item.cof 3 264496933 2,
          Item.cof 173 237723107 2])

/-- The tree for the length `173` and the seed `5`. -/
def t173_5 : Tree :=
  Tree.split 173 (
    Tree.add 3 (
      Tree.add 29 (
        Tree.leaf
          [(5, [Item.pr 5 1039, Item.pr 5 3461]), (3, [Item.pr 3 347, Item.pr 3 762239]), (29,
              [Item.pr 29 347, Item.pr 29 58129])]
          [Item.pr 5 1039, Item.pr 5 3461, Item.pr 3 347, Item.pr 3 762239, Item.pr 29 58129,
              Item.cof 5 3595979 2, Item.cof 3 264496933 2, Item.cof 29 20170763 2]))) (
    Tree.leaf
      [(5, [Item.pr 5 1039, Item.pr 5 3461]), (173, [Item.pr 173 347, Item.pr 173 685081])]
      [Item.pr 5 1039, Item.pr 5 3461, Item.pr 173 347, Item.pr 173 685081, Item.cof 5 3595979 2,
          Item.cof 173 237723107 2])

/-- The tree for the length `179` and the seed `3`. -/
def t179_3 : Tree :=
  Tree.add 179 (
    Tree.leaf
      [(3, [Item.pr 3 359, Item.pr 3 56207]), (179, [Item.cof 179 1 2])]
      [Item.pr 3 359, Item.pr 3 56207, Item.pr 3 100957, Item.cof 3 2037141945541 2,
          Item.cof 179 1 2])

/-- The tree for the length `179` and the seed `5`. -/
def t179_5 : Tree :=
  Tree.add 179 (
    Tree.leaf
      [(5, [Item.pr 5 359, Item.pr 5 3581]), (179, [Item.cof 179 1 2])]
      [Item.pr 5 359, Item.pr 5 3581, Item.pr 5 75539, Item.cof 5 97111352081 2, Item.cof 179 1 2])

/-- The tree for the length `181` and the seed `3`. -/
def t181_3 : Tree :=
  Tree.split 181 (
    Tree.add 7 (
      Tree.add 13 (
        Tree.leaf
          [(3, [Item.pr 3 90863, Item.pr 3 890159]), (7, [Item.pr 7 1811, Item.cof 7 1811 0]),
              (13, [Item.pr 13 5431, Item.pr 13 23531])]
          [Item.pr 3 90863, Item.pr 3 890159, Item.pr 7 1811, Item.pr 13 5431, Item.pr 13 23531,
              Item.pr 13 30047, Item.pr 13 423541, Item.cof 3 80882517217 0, Item.cof 7 1811 2,
              Item.cof 13 1626360288028355647 2]))) (
    Tree.leaf
      [(3, [Item.pr 3 90863, Item.pr 3 890159]), (181, [Item.pr 181 1087, Item.pr 181 2897])]
      [Item.pr 3 90863, Item.pr 3 890159, Item.pr 181 1087, Item.pr 181 2897,
          Item.cof 3 80882517217 0, Item.cof 181 3149039 2])

/-- The tree for the length `181` and the seed `5`. -/
def t181_5 : Tree :=
  Tree.split 181 (
    Tree.add 7 (
      Tree.add 13 (
        Tree.leaf
          [(7, [Item.pr 7 1811, Item.cof 7 1811 0]), (13, [Item.pr 13 5431, Item.pr 13 23531])]
          [Item.pr 7 1811, Item.pr 13 5431, Item.pr 13 23531, Item.pr 13 30047, Item.pr 13 423541,
              Item.cof 5 1 0, Item.cof 7 1811 2, Item.cof 13 1626360288028355647 2]))) (
    Tree.leaf
      [(181, [Item.pr 181 1087, Item.pr 181 2897])]
      [Item.pr 181 1087, Item.pr 181 2897, Item.cof 5 1 0, Item.cof 181 3149039 2])

/-- The tree for the length `191` and the seed `3`. -/
def t191_3 : Tree :=
  Tree.add 191 (
    Tree.leaf
      [(3, [Item.pr 3 383, Item.pr 3 311713]), (191, [Item.pr 191 236077, Item.cof 191 236077 0])]
      [Item.pr 3 383, Item.pr 3 311713, Item.pr 191 236077, Item.cof 3 119386079 2,
          Item.cof 191 236077 2])

/-- The tree for the length `191` and the seed `5`. -/
def t191_5 : Tree :=
  Tree.add 191 (
    Tree.leaf
      [(5, [Item.pr 5 112691, Item.cof 5 112691 0]), (191, [Item.pr 191 236077,
          Item.cof 191 236077 0])]
      [Item.pr 5 112691, Item.pr 191 236077, Item.cof 5 112691 2, Item.cof 191 236077 2])

/-- The tree for the length `193` and the seed `3`. -/
def t193_3 : Tree :=
  Tree.split 193 (
    Tree.add 97 (
      Tree.leaf
        [(3, [Item.pr 3 6563, Item.pr 3 29723]), (97, [Item.pr 97 31267, Item.pr 97 37057])]
        [Item.pr 3 6563, Item.pr 3 29723, Item.pr 97 31267, Item.pr 97 37057,
            Item.cof 3 195072049 2, Item.cof 97 1158661219 2])) (
    Tree.leaf
      [(3, [Item.pr 3 6563, Item.pr 3 29723]), (193, [Item.pr 193 773, Item.pr 193 1931])]
      [Item.pr 3 6563, Item.pr 3 29723, Item.pr 193 773, Item.pr 193 1931, Item.pr 193 148997,
          Item.cof 3 195072049 2, Item.cof 193 222402309011 2])

/-- The tree for the length `193` and the seed `5`. -/
def t193_5 : Tree :=
  Tree.split 193 (
    Tree.add 97 (
      Tree.leaf
        [(5, [Item.cof 5 1 2]), (97, [Item.pr 97 31267, Item.pr 97 37057])]
        [Item.pr 97 31267, Item.pr 97 37057, Item.cof 5 1 2, Item.cof 97 1158661219 2])) (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (193, [Item.pr 193 773, Item.pr 193 1931])]
      [Item.pr 193 773, Item.pr 193 1931, Item.pr 193 148997, Item.cof 5 1 2,
          Item.cof 193 222402309011 2])

/-- The tree for the length `197` and the seed `3`. -/
def t197_3 : Tree :=
  Tree.split 197 (
    Tree.add 11 (
      Tree.leaf
        [(3, [Item.pr 3 9851, Item.cof 3 9851 0]), (11, [Item.cof 11 1 2])]
        [Item.pr 3 9851, Item.cof 3 9851 2, Item.cof 11 1 2])) (
    Tree.leaf
      [(3, [Item.pr 3 9851, Item.cof 3 9851 0]), (197, [Item.cof 197 1 2])]
      [Item.pr 3 9851, Item.cof 3 9851 2, Item.cof 197 1 2])

/-- The tree for the length `197` and the seed `5`. -/
def t197_5 : Tree :=
  Tree.split 197 (
    Tree.add 3 (
      Tree.add 11 (
        Tree.leaf
          [(5, [Item.cof 5 1 2]), (3, [Item.pr 3 9851, Item.cof 3 9851 0]), (11, [Item.cof 11 1 2])]
          [Item.pr 3 9851, Item.cof 5 1 2, Item.cof 3 9851 2, Item.cof 11 1 2]))) (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (197, [Item.cof 197 1 2])]
      [Item.cof 5 1 2, Item.cof 197 1 2])

/-- The tree for the length `199` and the seed `3`. -/
def t199_3 : Tree :=
  Tree.add 199 (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (199, [Item.pr 199 797, Item.cof 199 797 0])]
      [Item.pr 199 797, Item.cof 3 1 2, Item.cof 199 797 2])

/-- The tree for the length `199` and the seed `5`. -/
def t199_5 : Tree :=
  Tree.add 199 (
    Tree.leaf
      [(5, [Item.pr 5 53731, Item.cof 5 53731 0]), (199, [Item.pr 199 797, Item.cof 199 797 0])]
      [Item.pr 5 53731, Item.pr 199 797, Item.cof 5 53731 0, Item.cof 199 797 2])

/-- The tree for the length `211` and the seed `3`. -/
def t211_3 : Tree :=
  Tree.add 211 (
    Tree.leaf
      [(3, [Item.pr 3 2111, Item.cof 3 2111 0]), (211, [Item.pr 211 25321, Item.cof 211 25321 0])]
      [Item.pr 3 2111, Item.pr 211 25321, Item.cof 3 2111 2, Item.cof 211 25321 2])

/-- The tree for the length `211` and the seed `5`. -/
def t211_5 : Tree :=
  Tree.add 211 (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (211, [Item.pr 211 25321, Item.cof 211 25321 0])]
      [Item.pr 211 25321, Item.cof 5 1 2, Item.cof 211 25321 2])

/-- The tree for the length `223` and the seed `3`. -/
def t223_3 : Tree :=
  Tree.add 223 (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (223, [Item.cof 223 1 2])]
      [Item.cof 3 1 2, Item.cof 223 1 2])

/-- The tree for the length `223` and the seed `5`. -/
def t223_5 : Tree :=
  Tree.add 223 (
    Tree.leaf
      [(5, [Item.pr 5 355909, Item.cof 5 355909 0]), (223, [Item.cof 223 1 2])]
      [Item.pr 5 355909, Item.cof 5 355909 0, Item.cof 223 1 2])

/-- The tree for the length `227` and the seed `3`. -/
def t227_3 : Tree :=
  Tree.add 227 (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (227, [Item.cof 227 1 2])]
      [Item.cof 3 1 2, Item.cof 227 1 2])

/-- The tree for the length `227` and the seed `5`. -/
def t227_5 : Tree :=
  Tree.add 227 (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (227, [Item.cof 227 1 2])]
      [Item.cof 5 1 2, Item.cof 227 1 2])

/-- The tree for the length `229` and the seed `3`. -/
def t229_3 : Tree :=
  Tree.split 229 (
    Tree.add 5 (
      Tree.add 23 (
        Tree.leaf
          [(3, [Item.cof 3 1 2]), (5, [Item.pr 5 2749, Item.pr 5 53129]), (23, [Item.cof 23 1 2])]
          [Item.pr 5 2749, Item.pr 5 53129, Item.cof 3 1 2, Item.cof 5 146051621 2,
              Item.cof 23 1 2]))) (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (229, [Item.cof 229 1 2])]
      [Item.cof 3 1 2, Item.cof 229 1 2])

/-- The tree for the length `229` and the seed `5`. -/
def t229_5 : Tree :=
  Tree.split 229 (
    Tree.add 23 (
      Tree.leaf
        [(5, [Item.pr 5 2749, Item.pr 5 53129]), (23, [Item.cof 23 1 2])]
        [Item.pr 5 2749, Item.pr 5 53129, Item.cof 5 146051621 2, Item.cof 23 1 2])) (
    Tree.leaf
      [(5, [Item.pr 5 2749, Item.pr 5 53129]), (229, [Item.cof 229 1 2])]
      [Item.pr 5 2749, Item.pr 5 53129, Item.cof 5 146051621 2, Item.cof 229 1 2])

/-- The table. -/
def tab : List (ℕ × Tree × Tree) :=
  [(127, t127_3, t127_5),
   (131, t131_3, t131_5),
   (137, t137_3, t137_5),
   (139, t139_3, t139_5),
   (149, t149_3, t149_5),
   (151, t151_3, t151_5),
   (157, t157_3, t157_5),
   (163, t163_3, t163_5),
   (167, t167_3, t167_5),
   (173, t173_3, t173_5),
   (179, t179_3, t179_5),
   (181, t181_3, t181_5),
   (191, t191_3, t191_5),
   (193, t193_3, t193_5),
   (197, t197_3, t197_5),
   (199, t199_3, t199_5),
   (211, t211_3, t211_5),
   (223, t223_3, t223_5),
   (227, t227_3, t227_5),
   (229, t229_3, t229_5)]

/-- The lengths of the table. -/
def ls : List ℕ := [127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197,
    199, 211, 223, 227, 229]

theorem tab_ls : tab.map Prod.fst = ls := rfl

theorem ok127 : tableOK pc [(127, t127_3, t127_5)] = true := by
  decide +kernel

theorem ok131 : tableOK pc [(131, t131_3, t131_5)] = true := by
  decide +kernel

theorem ok137 : tableOK pc [(137, t137_3, t137_5)] = true := by
  decide +kernel

theorem ok139 : tableOK pc [(139, t139_3, t139_5)] = true := by
  decide +kernel

theorem ok149 : tableOK pc [(149, t149_3, t149_5)] = true := by
  decide +kernel

theorem ok151 : tableOK pc [(151, t151_3, t151_5)] = true := by
  decide +kernel

theorem ok157 : tableOK pc [(157, t157_3, t157_5)] = true := by
  decide +kernel

theorem ok163 : tableOK pc [(163, t163_3, t163_5)] = true := by
  decide +kernel

theorem ok167 : tableOK pc [(167, t167_3, t167_5)] = true := by
  decide +kernel

theorem ok173 : tableOK pc [(173, t173_3, t173_5)] = true := by
  decide +kernel

theorem ok179 : tableOK pc [(179, t179_3, t179_5)] = true := by
  decide +kernel

theorem ok181 : tableOK pc [(181, t181_3, t181_5)] = true := by
  decide +kernel

theorem ok191 : tableOK pc [(191, t191_3, t191_5)] = true := by
  decide +kernel

theorem ok193 : tableOK pc [(193, t193_3, t193_5)] = true := by
  decide +kernel

theorem ok197 : tableOK pc [(197, t197_3, t197_5)] = true := by
  decide +kernel

theorem ok199 : tableOK pc [(199, t199_3, t199_5)] = true := by
  decide +kernel

theorem ok211 : tableOK pc [(211, t211_3, t211_5)] = true := by
  decide +kernel

theorem ok223 : tableOK pc [(223, t223_3, t223_5)] = true := by
  decide +kernel

theorem ok227 : tableOK pc [(227, t227_3, t227_5)] = true := by
  decide +kernel

theorem ok229 : tableOK pc [(229, t229_3, t229_5)] = true := by
  decide +kernel

theorem tab_ok : tableOK pc tab = true :=
  tableOK_cons ok127 <|
  tableOK_cons ok131 <|
  tableOK_cons ok137 <|
  tableOK_cons ok139 <|
  tableOK_cons ok149 <|
  tableOK_cons ok151 <|
  tableOK_cons ok157 <|
  tableOK_cons ok163 <|
  tableOK_cons ok167 <|
  tableOK_cons ok173 <|
  tableOK_cons ok179 <|
  tableOK_cons ok181 <|
  tableOK_cons ok191 <|
  tableOK_cons ok193 <|
  tableOK_cons ok197 <|
  tableOK_cons ok199 <|
  tableOK_cons ok211 <|
  tableOK_cons ok223 <|
  tableOK_cons ok227 <|
  tableOK_cons ok229 <|
  tableOK_nil pc

end OddPerfect.ImpTree.ImpureRowTreeD02

#print axioms OddPerfect.ImpTree.ImpureRowTreeD02.tab_ls
#print axioms OddPerfect.ImpTree.ImpureRowTreeD02.tab_ok
#print axioms OddPerfect.ImpTree.ImpureRowTreeD02.ok127
#print axioms OddPerfect.ImpTree.ImpureRowTreeD02.ok131
#print axioms OddPerfect.ImpTree.ImpureRowTreeD02.ok137
#print axioms OddPerfect.ImpTree.ImpureRowTreeD02.ok139
#print axioms OddPerfect.ImpTree.ImpureRowTreeD02.ok149
#print axioms OddPerfect.ImpTree.ImpureRowTreeD02.ok151
#print axioms OddPerfect.ImpTree.ImpureRowTreeD02.ok157
#print axioms OddPerfect.ImpTree.ImpureRowTreeD02.ok163
#print axioms OddPerfect.ImpTree.ImpureRowTreeD02.ok167
#print axioms OddPerfect.ImpTree.ImpureRowTreeD02.ok173
#print axioms OddPerfect.ImpTree.ImpureRowTreeD02.ok179
#print axioms OddPerfect.ImpTree.ImpureRowTreeD02.ok181
#print axioms OddPerfect.ImpTree.ImpureRowTreeD02.ok191
#print axioms OddPerfect.ImpTree.ImpureRowTreeD02.ok193
#print axioms OddPerfect.ImpTree.ImpureRowTreeD02.ok197
#print axioms OddPerfect.ImpTree.ImpureRowTreeD02.ok199
#print axioms OddPerfect.ImpTree.ImpureRowTreeD02.ok211
#print axioms OddPerfect.ImpTree.ImpureRowTreeD02.ok223
#print axioms OddPerfect.ImpTree.ImpureRowTreeD02.ok227
#print axioms OddPerfect.ImpTree.ImpureRowTreeD02.ok229
