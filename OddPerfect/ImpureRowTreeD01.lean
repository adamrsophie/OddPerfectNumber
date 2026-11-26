import OddPerfect.ImpureRowTreeCheck

/-!
# Impure row tree certificates for the lengths 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
    53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113

Data for `OddPerfect.ImpTree.tableOK_sound`: for each length `l` a tree for the seed `3`
and a tree for the seed `5`, checked by kernel reduction. Restricted result (one odd prime
divides every ordinary index); no published source was checked; novelty not verified.
The odd perfect number conjecture remains open.
-/

namespace OddPerfect.ImpTree.ImpureRowTreeD01

open OddPerfect.ImpTree

/-- Pratt certificates for the large primes. -/
def pc : List (ℕ × ℕ × List ℕ) :=
  [(15797, 2, [2, 2, 11, 359]),
   (797161, 17, [2, 2, 2, 3, 5, 7, 13, 73]),
   (305175781, 6, [2, 2, 3, 3, 5, 7, 13, 31, 601]),
   (16369, 7, [2, 2, 2, 2, 3, 11, 31]),
   (1957650063931, 2, [2, 3, 3, 5, 11, 107, 1129, 16369])]

/-- The tree for the length `5` and the seed `3`. -/
def t5_3 : Tree :=
  Tree.split 5 (
    Tree.add 11 (
      Tree.add 3221 (
        Tree.add 1957650063931 (
          Tree.leaf
            []
            [Item.pr 3 11, Item.pr 11 3221, Item.pr 3221 1957650063931, Item.pr 1957650063931 41,
                Item.cof 1957650063931 205 2])))) (
    Tree.add 11 (
      Tree.add 71 (
        Tree.leaf
          [(5, [Item.pr 5 11, Item.pr 5 71])]
          [Item.pr 3 11, Item.pr 5 71, Item.pr 11 3221, Item.pr 71 211, Item.pr 71 2221])))

/-- The tree for the length `5` and the seed `5`. -/
def t5_5 : Tree :=
  Tree.add 11 (
    Tree.add 71 (
      Tree.leaf
        [(5, [Item.pr 5 11, Item.pr 5 71])]
        [Item.pr 5 11, Item.pr 5 71, Item.pr 11 3221, Item.pr 71 211, Item.pr 71 2221]))

/-- The tree for the length `7` and the seed `3`. -/
def t7_3 : Tree :=
  Tree.add 7 (
    Tree.split 29 (
      Tree.add 5 (
        Tree.leaf
          [(7, [Item.pr 7 29, Item.pr 7 4733])]
          [Item.pr 3 1093, Item.pr 7 29, Item.pr 7 4733, Item.pr 5 19531])) (
      Tree.leaf
        [(7, [Item.pr 7 29, Item.pr 7 4733])]
        [Item.pr 3 1093, Item.pr 7 29, Item.pr 7 4733, Item.pr 29 88009573]))

/-- The tree for the length `7` and the seed `5`. -/
def t7_5 : Tree :=
  Tree.add 7 (
    Tree.split 29 (
      Tree.add 3 (
        Tree.leaf
          [(7, [Item.pr 7 29, Item.pr 7 4733])]
          [Item.pr 5 19531, Item.pr 7 29, Item.pr 7 4733, Item.pr 3 1093])) (
      Tree.leaf
        [(7, [Item.pr 7 29, Item.pr 7 4733])]
        [Item.pr 5 19531, Item.pr 7 29, Item.pr 7 4733, Item.pr 29 88009573]))

/-- The tree for the length `11` and the seed `3`. -/
def t11_3 : Tree :=
  Tree.add 11 (
    Tree.leaf
      [(3, [Item.pr 3 23, Item.pr 3 3851]), (11, [Item.pr 11 15797, Item.pr 11 1806113])]
      [Item.pr 3 23, Item.pr 3 3851, Item.pr 11 15797, Item.pr 11 1806113])

/-- The tree for the length `11` and the seed `5`. -/
def t11_5 : Tree :=
  Tree.add 11 (
    Tree.split 15797 (
      Tree.add 3 (
        Tree.add 2633 (
          Tree.leaf
            [(11, [Item.pr 11 15797, Item.pr 11 1806113]), (3, [Item.pr 3 23, Item.pr 3 3851]),
                (2633, [Item.pr 2633 2113, Item.pr 2633 947684519])]
            [Item.pr 5 12207031, Item.pr 11 15797, Item.pr 11 1806113, Item.pr 3 23,
                Item.pr 3 3851, Item.pr 2633 2113, Item.pr 2633 947684519,
                Item.pr 2633 9620773471, Item.pr 2633 831572833499]))) (
      Tree.leaf
        [(11, [Item.pr 11 15797, Item.pr 11 1806113])]
        [Item.pr 5 12207031, Item.pr 11 15797, Item.pr 11 1806113, Item.pr 15797 463,
            Item.pr 15797 116880853, Item.pr 15797 1625760718469882273470294777103]))

/-- The tree for the length `13` and the seed `3`. -/
def t13_3 : Tree :=
  Tree.split 13 (
    Tree.add 7 (
      Tree.add 797161 (
        Tree.leaf
          []
          [Item.pr 3 797161, Item.pr 7 16148168401, Item.cof 797161 13 2]))) (
    Tree.leaf
      [(13, [Item.pr 13 53, Item.pr 13 264031])]
      [Item.pr 3 797161, Item.pr 13 53, Item.pr 13 264031, Item.pr 13 1803647])

/-- The tree for the length `13` and the seed `5`. -/
def t13_5 : Tree :=
  Tree.split 13 (
    Tree.add 7 (
      Tree.add 305175781 (
        Tree.leaf
          []
          [Item.pr 5 305175781, Item.pr 7 16148168401, Item.cof 305175781 13 2]))) (
    Tree.leaf
      [(13, [Item.pr 13 53, Item.pr 13 264031])]
      [Item.pr 5 305175781, Item.pr 13 53, Item.pr 13 264031, Item.pr 13 1803647])

/-- The tree for the length `17` and the seed `3`. -/
def t17_3 : Tree :=
  Tree.split 17 (
    Tree.add 1871 (
      Tree.leaf
        [(3, [Item.pr 3 1871, Item.pr 3 34511])]
        [Item.pr 3 1871, Item.pr 3 34511, Item.pr 1871 24379, Item.cof 1871 414443 2])) (
    Tree.leaf
      [(3, [Item.pr 3 1871, Item.pr 3 34511]), (17, [Item.pr 17 10949, Item.pr 17 1749233])]
      [Item.pr 3 1871, Item.pr 3 34511, Item.pr 17 10949, Item.pr 17 1749233,
          Item.pr 17 2699538733])

/-- The tree for the length `17` and the seed `5`. -/
def t17_5 : Tree :=
  Tree.split 17 (
    Tree.add 3 (
      Tree.leaf
        [(5, [Item.pr 5 409, Item.pr 5 466344409]), (3, [Item.pr 3 1871, Item.pr 3 34511])]
        [Item.pr 5 409, Item.pr 5 466344409, Item.pr 3 1871, Item.pr 3 34511])) (
    Tree.leaf
      [(5, [Item.pr 5 409, Item.pr 5 466344409]), (17, [Item.pr 17 10949, Item.pr 17 1749233])]
      [Item.pr 5 409, Item.pr 5 466344409, Item.pr 17 10949, Item.pr 17 1749233,
          Item.pr 17 2699538733])

/-- The tree for the length `19` and the seed `3`. -/
def t19_3 : Tree :=
  Tree.add 19 (
    Tree.split 1597 (
      Tree.add 17 (
        Tree.add 47 (
          Tree.leaf
            [(3, [Item.pr 3 1597, Item.pr 3 363889]), (17, [Item.pr 17 229, Item.pr 17 1103]),
                (47, [Item.pr 47 419, Item.pr 47 65247271367])]
            [Item.pr 3 1597, Item.pr 3 363889, Item.pr 19 109912203092239643840221,
                Item.pr 17 229, Item.pr 17 1103, Item.pr 17 202607147, Item.pr 17 291973723,
                Item.pr 47 419, Item.pr 47 65247271367, Item.pr 47 46808539630950829]))) (
      Tree.leaf
        [(3, [Item.pr 3 1597, Item.pr 3 363889])]
        [Item.pr 3 1597, Item.pr 3 363889, Item.pr 19 109912203092239643840221, Item.pr 1597 191,
            Item.pr 1597 1103, Item.pr 1597 2281, Item.pr 1597 4219, Item.pr 1597 336757,
            Item.pr 1597 14119178807, Item.pr 1597 24942337883983242155950450181]))

/-- The tree for the length `19` and the seed `5`. -/
def t19_5 : Tree :=
  Tree.add 19 (
    Tree.leaf
      [(5, [Item.pr 5 191, Item.pr 5 6271])]
      [Item.pr 5 191, Item.pr 5 6271, Item.pr 5 3981071, Item.pr 19 109912203092239643840221])

/-- The tree for the length `23` and the seed `3`. -/
def t23_3 : Tree :=
  Tree.add 23 (
    Tree.leaf
      [(3, [Item.pr 3 47, Item.pr 3 1001523179]), (23, [Item.pr 23 461, Item.pr 23 1289])]
      [Item.pr 3 47, Item.pr 3 1001523179, Item.pr 23 461, Item.pr 23 1289,
          Item.pr 23 831603031789, Item.pr 23 1920647391913])

/-- The tree for the length `23` and the seed `5`. -/
def t23_5 : Tree :=
  Tree.add 23 (
    Tree.leaf
      [(5, [Item.pr 5 8971, Item.pr 5 332207361361]), (23, [Item.pr 23 461, Item.pr 23 1289])]
      [Item.pr 5 8971, Item.pr 5 332207361361, Item.pr 23 461, Item.pr 23 1289,
          Item.pr 23 831603031789, Item.pr 23 1920647391913])

/-- The tree for the length `29` and the seed `3`. -/
def t29_3 : Tree :=
  Tree.split 29 (
    Tree.add 5 (
      Tree.leaf
        [(3, [Item.pr 3 59, Item.pr 3 28537]), (5, [Item.pr 5 59, Item.pr 5 35671])]
        [Item.pr 3 59, Item.pr 3 28537, Item.pr 3 20381027, Item.pr 5 35671,
            Item.pr 5 22125996444329])) (
    Tree.leaf
      [(3, [Item.pr 3 59, Item.pr 3 28537]), (29, [Item.pr 29 59, Item.pr 29 16763])]
      [Item.pr 3 59, Item.pr 3 28537, Item.pr 3 20381027, Item.pr 29 16763, Item.pr 29 84449,
          Item.pr 29 2428577, Item.pr 29 14111459, Item.pr 29 58320973, Item.pr 29 549334763])

/-- The tree for the length `29` and the seed `5`. -/
def t29_5 : Tree :=
  Tree.split 29 (
    Tree.add 3 (
      Tree.leaf
        [(5, [Item.pr 5 59, Item.pr 5 35671]), (3, [Item.pr 3 59, Item.pr 3 28537])]
        [Item.pr 5 59, Item.pr 5 35671, Item.pr 5 22125996444329, Item.pr 3 28537,
            Item.pr 3 20381027])) (
    Tree.leaf
      [(5, [Item.pr 5 59, Item.pr 5 35671]), (29, [Item.pr 29 59, Item.pr 29 16763])]
      [Item.pr 5 59, Item.pr 5 35671, Item.pr 5 22125996444329, Item.pr 29 16763,
          Item.pr 29 84449, Item.pr 29 2428577, Item.pr 29 14111459, Item.pr 29 58320973,
          Item.pr 29 549334763])

/-- The tree for the length `31` and the seed `3`. -/
def t31_3 : Tree :=
  Tree.add 31 (
    Tree.leaf
      [(3, [Item.pr 3 683, Item.pr 3 102673])]
      [Item.pr 3 683, Item.pr 3 102673, Item.pr 3 4404047, Item.cof 31 1 0])

/-- The tree for the length `31` and the seed `5`. -/
def t31_5 : Tree :=
  Tree.add 31 (
    Tree.split 1861 (
      Tree.add 7 (
        Tree.add 19 (
          Tree.leaf
            [(5, [Item.pr 5 1861, Item.pr 5 625552508473588471]), (7, [Item.pr 7 311,
                Item.pr 7 21143])]
            [Item.pr 5 1861, Item.pr 5 625552508473588471, Item.pr 7 311, Item.pr 7 21143,
                Item.pr 7 3999088279399464409, Item.pr 19 243270318891483838103593381595151809701,
                Item.cof 31 1 0]))) (
      Tree.leaf
        [(5, [Item.pr 5 1861, Item.pr 5 625552508473588471])]
        [Item.pr 5 1861, Item.pr 5 625552508473588471, Item.cof 31 1 0, Item.cof 1861 31 2]))

/-- The tree for the length `37` and the seed `3`. -/
def t37_3 : Tree :=
  Tree.split 37 (
    Tree.add 19 (
      Tree.leaf
        [(3, [Item.pr 3 13097927, Item.pr 3 17189128703]), (19, [Item.pr 19 149,
            Item.cof 19 149 0])]
        [Item.pr 3 13097927, Item.pr 3 17189128703, Item.pr 19 149, Item.cof 19 149 2])) (
    Tree.leaf
      [(3, [Item.pr 3 13097927, Item.pr 3 17189128703]), (37, [Item.pr 37 149, Item.pr 37 1999])]
      [Item.pr 3 13097927, Item.pr 3 17189128703, Item.pr 37 149, Item.pr 37 1999,
          Item.pr 37 7993, Item.pr 37 16651, Item.pr 37 17317, Item.pr 37 10192715656759,
          Item.pr 37 41903425553544839998158239])

/-- The tree for the length `37` and the seed `5`. -/
def t37_5 : Tree :=
  Tree.split 37 (
    Tree.add 19 (
      Tree.leaf
        [(5, [Item.pr 5 149, Item.pr 5 13971969971]), (19, [Item.pr 19 149, Item.cof 19 149 0])]
        [Item.pr 5 149, Item.pr 5 13971969971, Item.pr 5 8737481256739, Item.cof 19 149 2])) (
    Tree.leaf
      [(5, [Item.pr 5 149, Item.pr 5 13971969971]), (37, [Item.pr 37 149, Item.pr 37 1999])]
      [Item.pr 5 149, Item.pr 5 13971969971, Item.pr 5 8737481256739, Item.pr 37 1999,
          Item.pr 37 7993, Item.pr 37 16651, Item.pr 37 17317, Item.pr 37 10192715656759,
          Item.pr 37 41903425553544839998158239])

/-- The tree for the length `41` and the seed `3`. -/
def t41_3 : Tree :=
  Tree.split 41 (
    Tree.add 7 (
      Tree.leaf
        [(3, [Item.pr 3 83, Item.pr 3 2526913]), (7, [Item.pr 7 83, Item.pr 7 20515909])]
        [Item.pr 3 83, Item.pr 3 2526913, Item.pr 3 86950696619, Item.pr 7 20515909,
            Item.pr 7 4362139336229068656094783])) (
    Tree.leaf
      [(3, [Item.pr 3 83, Item.pr 3 2526913]), (41, [Item.pr 41 83, Item.cof 41 83 0])]
      [Item.pr 3 83, Item.pr 3 2526913, Item.pr 3 86950696619, Item.cof 41 83 2])

/-- The tree for the length `41` and the seed `5`. -/
def t41_5 : Tree :=
  Tree.split 41 (
    Tree.add 3 (
      Tree.add 7 (
        Tree.leaf
          [(5, [Item.pr 5 2238236249, Item.pr 5 5079304643216687969]), (3, [Item.pr 3 83,
              Item.pr 3 2526913]), (7, [Item.pr 7 83, Item.pr 7 20515909])]
          [Item.pr 5 2238236249, Item.pr 5 5079304643216687969, Item.pr 3 83, Item.pr 3 2526913,
              Item.pr 3 86950696619, Item.pr 7 20515909, Item.pr 7 4362139336229068656094783]))) (
    Tree.leaf
      [(5, [Item.pr 5 2238236249, Item.pr 5 5079304643216687969]), (41, [Item.pr 41 83,
          Item.cof 41 83 0])]
      [Item.pr 5 2238236249, Item.pr 5 5079304643216687969, Item.pr 41 83, Item.cof 41 83 2])

/-- The tree for the length `43` and the seed `3`. -/
def t43_3 : Tree :=
  Tree.add 43 (
    Tree.leaf
      [(3, [Item.pr 3 431, Item.pr 3 380808546861411923]), (43, [Item.pr 43 173,
          Item.pr 43 120401])]
      [Item.pr 3 431, Item.pr 3 380808546861411923, Item.pr 43 173, Item.pr 43 120401,
          Item.cof 43 20829373 0])

/-- The tree for the length `43` and the seed `5`. -/
def t43_5 : Tree :=
  Tree.add 43 (
    Tree.leaf
      [(5, [Item.pr 5 1644512641, Item.pr 5 172827552198815888791]), (43, [Item.pr 43 173,
          Item.pr 43 120401])]
      [Item.pr 5 1644512641, Item.pr 5 172827552198815888791, Item.pr 43 173, Item.pr 43 120401,
          Item.cof 43 20829373 0])

/-- The tree for the length `47` and the seed `3`. -/
def t47_3 : Tree :=
  Tree.add 47 (
    Tree.leaf
      [(3, [Item.pr 3 1223, Item.pr 3 21997]), (47, [Item.pr 47 1693, Item.cof 47 1693 0])]
      [Item.pr 3 1223, Item.pr 3 21997, Item.pr 3 5112661, Item.pr 3 96656723, Item.pr 47 1693,
          Item.cof 47 1693 2])

/-- The tree for the length `47` and the seed `5`. -/
def t47_5 : Tree :=
  Tree.add 47 (
    Tree.leaf
      [(47, [Item.pr 47 1693, Item.cof 47 1693 0])]
      [Item.pr 5 177635683940025046467781066894531, Item.pr 47 1693, Item.cof 47 1693 2])

/-- The tree for the length `53` and the seed `3`. -/
def t53_3 : Tree :=
  Tree.split 53 (
    Tree.leaf
      [(3, [Item.pr 3 107, Item.pr 3 24169])]
      [Item.pr 3 107, Item.pr 3 24169, Item.pr 3 3747607031112307667]) (
    Tree.leaf
      [(3, [Item.pr 3 107, Item.pr 3 24169]), (53, [Item.pr 53 107, Item.pr 53 141829])]
      [Item.pr 3 107, Item.pr 3 24169, Item.pr 3 3747607031112307667, Item.pr 53 141829,
          Item.cof 53 15175703 2])

/-- The tree for the length `53` and the seed `5`. -/
def t53_5 : Tree :=
  Tree.split 53 (
    Tree.add 3 (
      Tree.leaf
        [(5, [Item.pr 5 5960555749, Item.pr 5 17154094481]), (3, [Item.pr 3 107, Item.pr 3 24169])]
        [Item.pr 5 5960555749, Item.pr 5 17154094481, Item.pr 5 27145365052629449, Item.pr 3 107,
            Item.pr 3 24169, Item.pr 3 3747607031112307667])) (
    Tree.leaf
      [(5, [Item.pr 5 5960555749, Item.pr 5 17154094481]), (53, [Item.pr 53 107,
          Item.pr 53 141829])]
      [Item.pr 5 5960555749, Item.pr 5 17154094481, Item.pr 5 27145365052629449, Item.pr 53 107,
          Item.pr 53 141829, Item.cof 53 15175703 2])

/-- The tree for the length `59` and the seed `3`. -/
def t59_3 : Tree :=
  Tree.add 59 (
    Tree.leaf
      [(3, [Item.pr 3 14425532687, Item.pr 3 489769993189671059]), (59, [Item.pr 59 709,
          Item.cof 59 709 0])]
      [Item.pr 3 14425532687, Item.pr 3 489769993189671059, Item.pr 59 709, Item.cof 59 709 2])

/-- The tree for the length `59` and the seed `5`. -/
def t59_5 : Tree :=
  Tree.add 59 (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (59, [Item.pr 59 709, Item.cof 59 709 0])]
      [Item.pr 59 709, Item.cof 5 1 2, Item.cof 59 709 2])

/-- The tree for the length `61` and the seed `3`. -/
def t61_3 : Tree :=
  Tree.split 61 (
    Tree.add 31 (
      Tree.leaf
        [(3, [Item.pr 3 603901, Item.pr 3 105293313660391861035901]), (31, [Item.pr 31 14519,
            Item.cof 31 14519 0])]
        [Item.pr 3 603901, Item.pr 3 105293313660391861035901, Item.pr 31 14519,
            Item.cof 31 14519 2])) (
    Tree.leaf
      [(3, [Item.pr 3 603901, Item.pr 3 105293313660391861035901]), (61, [Item.pr 61 977,
          Item.cof 61 977 0])]
      [Item.pr 3 603901, Item.pr 3 105293313660391861035901, Item.pr 61 977, Item.cof 61 977 2])

/-- The tree for the length `61` and the seed `5`. -/
def t61_5 : Tree :=
  Tree.split 61 (
    Tree.add 31 (
      Tree.leaf
        [(5, [Item.pr 5 8419, Item.pr 5 918585913061]), (31, [Item.pr 31 14519,
            Item.cof 31 14519 0])]
        [Item.pr 5 8419, Item.pr 5 918585913061, Item.pr 5 140194179307171898833699259,
            Item.pr 31 14519, Item.cof 31 14519 2])) (
    Tree.leaf
      [(5, [Item.pr 5 8419, Item.pr 5 918585913061]), (61, [Item.pr 61 977, Item.cof 61 977 0])]
      [Item.pr 5 8419, Item.pr 5 918585913061, Item.pr 5 140194179307171898833699259,
          Item.pr 61 977, Item.cof 61 977 2])

/-- The tree for the length `67` and the seed `3`. -/
def t67_3 : Tree :=
  Tree.add 67 (
    Tree.leaf
      [(3, [Item.pr 3 221101, Item.pr 3 441019876741]), (67, [Item.pr 67 269, Item.pr 67 4021])]
      [Item.pr 3 221101, Item.pr 3 441019876741, Item.pr 3 475384700124973, Item.pr 67 269,
          Item.pr 67 4021, Item.pr 67 730837, Item.cof 67 790509110213 2])

/-- The tree for the length `67` and the seed `5`. -/
def t67_5 : Tree :=
  Tree.add 67 (
    Tree.leaf
      [(5, [Item.pr 5 269, Item.pr 5 1609]), (67, [Item.pr 67 269, Item.pr 67 4021])]
      [Item.pr 5 269, Item.pr 5 1609, Item.pr 5 26399, Item.pr 5 2454335007529,
          Item.pr 5 604088623657497125653141, Item.pr 67 4021, Item.pr 67 730837,
          Item.cof 67 790509110213 2])

/-- The tree for the length `71` and the seed `3`. -/
def t71_3 : Tree :=
  Tree.add 71 (
    Tree.leaf
      [(71, [Item.pr 71 105649, Item.cof 71 105649 0])]
      [Item.pr 3 3754733257489862401973357979128773, Item.pr 71 105649, Item.cof 71 105649 2])

/-- The tree for the length `71` and the seed `5`. -/
def t71_5 : Tree :=
  Tree.add 71 (
    Tree.leaf
      [(5, [Item.pr 5 569, Item.cof 5 569 0]), (71, [Item.pr 71 105649, Item.cof 71 105649 0])]
      [Item.pr 5 569, Item.pr 71 105649, Item.cof 5 569 0, Item.cof 71 105649 2])

/-- The tree for the length `73` and the seed `3`. -/
def t73_3 : Tree :=
  Tree.split 73 (
    Tree.add 37 (
      Tree.leaf
        [(3, [Item.pr 3 11243, Item.pr 3 20149]), (37, [Item.cof 37 1 2])]
        [Item.pr 3 11243, Item.pr 3 20149, Item.pr 3 15768033143, Item.pr 3 9460375336977361,
            Item.cof 37 1 2])) (
    Tree.leaf
      [(3, [Item.pr 3 11243, Item.pr 3 20149]), (73, [Item.pr 73 293, Item.pr 73 439])]
      [Item.pr 3 11243, Item.pr 3 20149, Item.pr 3 15768033143, Item.pr 3 9460375336977361,
          Item.pr 73 293, Item.pr 73 439, Item.cof 73 128627 2])

/-- The tree for the length `73` and the seed `5`. -/
def t73_5 : Tree :=
  Tree.split 73 (
    Tree.add 37 (
      Tree.leaf
        [(5, [Item.cof 5 1 2]), (37, [Item.cof 37 1 2])]
        [Item.cof 5 1 2, Item.cof 37 1 2])) (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (73, [Item.pr 73 293, Item.pr 73 439])]
      [Item.pr 73 293, Item.pr 73 439, Item.cof 5 1 2, Item.cof 73 128627 2])

/-- The tree for the length `79` and the seed `3`. -/
def t79_3 : Tree :=
  Tree.add 79 (
    Tree.leaf
      [(3, [Item.pr 3 432853009, Item.pr 3 392038110671]), (79, [Item.pr 79 317,
          Item.cof 79 317 0])]
      [Item.pr 3 432853009, Item.pr 3 392038110671, Item.pr 3 145171177264407947, Item.pr 79 317,
          Item.cof 79 317 2])

/-- The tree for the length `79` and the seed `5`. -/
def t79_5 : Tree :=
  Tree.add 79 (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (79, [Item.pr 79 317, Item.cof 79 317 0])]
      [Item.pr 79 317, Item.cof 5 1 2, Item.cof 79 317 2])

/-- The tree for the length `83` and the seed `3`. -/
def t83_3 : Tree :=
  Tree.add 83 (
    Tree.leaf
      [(3, [Item.pr 3 167, Item.pr 3 12119]), (83, [Item.pr 83 2657, Item.cof 83 2657 0])]
      [Item.pr 3 167, Item.pr 3 12119, Item.pr 3 1036745531, Item.pr 3 950996059627210897943351,
          Item.pr 83 2657, Item.cof 83 2657 2])

/-- The tree for the length `83` and the seed `5`. -/
def t83_5 : Tree :=
  Tree.add 83 (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (83, [Item.pr 83 2657, Item.cof 83 2657 0])]
      [Item.pr 83 2657, Item.cof 5 1 2, Item.cof 83 2657 2])

/-- The tree for the length `89` and the seed `3`. -/
def t89_3 : Tree :=
  Tree.split 89 (
    Tree.add 5 (
      Tree.leaf
        [(3, [Item.pr 3 179, Item.pr 3 1611479891519807]), (5, [Item.pr 5 179, Item.cof 5 179 0])]
        [Item.pr 3 179, Item.pr 3 1611479891519807, Item.pr 3 5042939439565996049162197,
            Item.cof 5 179 2])) (
    Tree.leaf
      [(3, [Item.pr 3 179, Item.pr 3 1611479891519807]), (89, [Item.pr 89 179, Item.cof 89 179 0])]
      [Item.pr 3 179, Item.pr 3 1611479891519807, Item.pr 3 5042939439565996049162197,
          Item.cof 89 179 2])

/-- The tree for the length `89` and the seed `5`. -/
def t89_5 : Tree :=
  Tree.split 89 (
    Tree.add 3 (
      Tree.leaf
        [(5, [Item.pr 5 179, Item.cof 5 179 0]), (3, [Item.pr 3 179, Item.pr 3 1611479891519807])]
        [Item.pr 5 179, Item.pr 3 1611479891519807, Item.pr 3 5042939439565996049162197,
            Item.cof 5 179 2])) (
    Tree.leaf
      [(5, [Item.pr 5 179, Item.cof 5 179 0]), (89, [Item.pr 89 179, Item.cof 89 179 0])]
      [Item.pr 5 179, Item.cof 5 179 2, Item.cof 89 179 2])

/-- The tree for the length `97` and the seed `3`. -/
def t97_3 : Tree :=
  Tree.split 97 (
    Tree.add 7 (
      Tree.leaf
        [(3, [Item.pr 3 76631, Item.cof 3 76631 0]), (7, [Item.pr 7 389, Item.pr 7 971])]
        [Item.pr 3 76631, Item.pr 7 389, Item.pr 7 971, Item.cof 3 76631 2, Item.cof 7 377719 0])) (
    Tree.leaf
      [(3, [Item.pr 3 76631, Item.cof 3 76631 0]), (97, [Item.pr 97 389, Item.pr 97 363751])]
      [Item.pr 3 76631, Item.pr 97 389, Item.pr 97 363751, Item.cof 3 76631 2,
          Item.cof 97 141499139 2])

/-- The tree for the length `97` and the seed `5`. -/
def t97_5 : Tree :=
  Tree.split 97 (
    Tree.add 7 (
      Tree.leaf
        [(5, [Item.pr 5 389, Item.pr 5 264811]), (7, [Item.pr 7 389, Item.pr 7 971])]
        [Item.pr 5 389, Item.pr 5 264811, Item.pr 7 971, Item.cof 5 103011479 0,
            Item.cof 7 377719 0])) (
    Tree.leaf
      [(5, [Item.pr 5 389, Item.pr 5 264811]), (97, [Item.pr 97 389, Item.pr 97 363751])]
      [Item.pr 5 389, Item.pr 5 264811, Item.pr 97 363751, Item.cof 5 103011479 0,
          Item.cof 97 141499139 2])

/-- The tree for the length `101` and the seed `3`. -/
def t101_3 : Tree :=
  Tree.split 101 (
    Tree.add 17 (
      Tree.leaf
        [(3, [Item.cof 3 1 2]), (17, [Item.pr 17 10303, Item.pr 17 70297])]
        [Item.pr 17 10303, Item.pr 17 70297, Item.cof 3 1 2, Item.cof 17 724269991 2])) (
    Tree.leaf
      [(3, [Item.cof 3 1 2]), (101, [Item.pr 101 607, Item.pr 101 1213])]
      [Item.pr 101 607, Item.pr 101 1213, Item.pr 101 5657, Item.pr 101 157561, Item.cof 3 1 2,
          Item.cof 101 656272791541907 2])

/-- The tree for the length `101` and the seed `5`. -/
def t101_5 : Tree :=
  Tree.split 101 (
    Tree.add 3 (
      Tree.add 17 (
        Tree.leaf
          [(5, [Item.cof 5 1 2]), (3, [Item.cof 3 1 2]), (17, [Item.pr 17 10303, Item.pr 17 70297])]
          [Item.pr 17 10303, Item.pr 17 70297, Item.cof 5 1 2, Item.cof 3 1 2,
              Item.cof 17 724269991 2]))) (
    Tree.leaf
      [(5, [Item.cof 5 1 2]), (101, [Item.pr 101 607, Item.pr 101 1213])]
      [Item.pr 101 607, Item.pr 101 1213, Item.pr 101 5657, Item.pr 101 157561, Item.cof 5 1 2,
          Item.cof 101 656272791541907 2])

/-- The tree for the length `103` and the seed `3`. -/
def t103_3 : Tree :=
  Tree.add 103 (
    Tree.leaf
      [(103, [Item.pr 103 1237, Item.cof 103 1237 0])]
      [Item.pr 103 1237, Item.cof 3 1 0, Item.cof 103 1237 2])

/-- The tree for the length `103` and the seed `5`. -/
def t103_5 : Tree :=
  Tree.add 103 (
    Tree.leaf
      [(5, [Item.pr 5 3709, Item.pr 5 28429]), (103, [Item.pr 103 1237, Item.cof 103 1237 0])]
      [Item.pr 5 3709, Item.pr 5 28429, Item.pr 103 1237, Item.cof 5 105443161 2,
          Item.cof 103 1237 2])

/-- The tree for the length `107` and the seed `3`. -/
def t107_3 : Tree :=
  Tree.add 107 (
    Tree.leaf
      [(3, [Item.pr 3 50077, Item.pr 3 229837]), (107, [Item.cof 107 1 2])]
      [Item.pr 3 50077, Item.pr 3 229837, Item.cof 3 11509547449 0, Item.cof 107 1 2])

/-- The tree for the length `107` and the seed `5`. -/
def t107_5 : Tree :=
  Tree.add 107 (
    Tree.leaf
      [(5, [Item.pr 5 6421, Item.cof 5 6421 0]), (107, [Item.cof 107 1 2])]
      [Item.pr 5 6421, Item.cof 5 6421 2, Item.cof 107 1 2])

/-- The tree for the length `109` and the seed `3`. -/
def t109_3 : Tree :=
  Tree.split 109 (
    Tree.add 5 (
      Tree.add 11 (
        Tree.leaf
          [(3, [Item.pr 3 1091, Item.cof 3 1091 0]), (5, [Item.pr 5 1091, Item.cof 5 1091 0]),
              (11, [Item.cof 11 1 2])]
          [Item.pr 3 1091, Item.cof 3 1091 2, Item.cof 5 1091 2, Item.cof 11 1 2]))) (
    Tree.leaf
      [(3, [Item.pr 3 1091, Item.cof 3 1091 0]), (109, [Item.pr 109 2617, Item.cof 109 2617 0])]
      [Item.pr 3 1091, Item.pr 109 2617, Item.cof 3 1091 2, Item.cof 109 2617 2])

/-- The tree for the length `109` and the seed `5`. -/
def t109_5 : Tree :=
  Tree.split 109 (
    Tree.add 11 (
      Tree.leaf
        [(5, [Item.pr 5 1091, Item.cof 5 1091 0]), (11, [Item.cof 11 1 2])]
        [Item.pr 5 1091, Item.cof 5 1091 2, Item.cof 11 1 2])) (
    Tree.leaf
      [(5, [Item.pr 5 1091, Item.cof 5 1091 0]), (109, [Item.pr 109 2617, Item.cof 109 2617 0])]
      [Item.pr 5 1091, Item.pr 109 2617, Item.cof 5 1091 2, Item.cof 109 2617 2])

/-- The tree for the length `113` and the seed `3`. -/
def t113_3 : Tree :=
  Tree.split 113 (
    Tree.add 19 (
      Tree.leaf
        [(3, [Item.pr 3 227, Item.pr 3 1583]), (19, [Item.pr 19 227, Item.pr 19 3617])]
        [Item.pr 3 227, Item.pr 3 1583, Item.pr 19 3617, Item.pr 19 6781, Item.cof 3 359341 2,
            Item.cof 19 5567601079 2])) (
    Tree.leaf
      [(3, [Item.pr 3 227, Item.pr 3 1583]), (113, [Item.pr 113 227, Item.pr 113 3391])]
      [Item.pr 3 227, Item.pr 3 1583, Item.pr 113 3391, Item.pr 113 8363, Item.cof 3 359341 2,
          Item.cof 113 6437477791 2])

/-- The tree for the length `113` and the seed `5`. -/
def t113_5 : Tree :=
  Tree.split 113 (
    Tree.add 3 (
      Tree.add 19 (
        Tree.leaf
          [(5, [Item.pr 5 2939, Item.pr 5 6329]), (3, [Item.pr 3 227, Item.pr 3 1583]), (19,
              [Item.pr 19 227, Item.pr 19 3617])]
          [Item.pr 5 2939, Item.pr 5 6329, Item.pr 5 129499, Item.pr 5 308491, Item.pr 3 227,
              Item.pr 3 1583, Item.pr 19 3617, Item.pr 19 6781, Item.cof 5 743093726543364379 2,
              Item.cof 3 359341 2, Item.cof 19 5567601079 2]))) (
    Tree.leaf
      [(5, [Item.pr 5 2939, Item.pr 5 6329]), (113, [Item.pr 113 227, Item.pr 113 3391])]
      [Item.pr 5 2939, Item.pr 5 6329, Item.pr 5 129499, Item.pr 5 308491, Item.pr 113 227,
          Item.pr 113 3391, Item.pr 113 8363, Item.cof 5 743093726543364379 2,
          Item.cof 113 6437477791 2])

/-- The table. -/
def tab : List (ℕ × Tree × Tree) :=
  [(5, t5_3, t5_5),
   (7, t7_3, t7_5),
   (11, t11_3, t11_5),
   (13, t13_3, t13_5),
   (17, t17_3, t17_5),
   (19, t19_3, t19_5),
   (23, t23_3, t23_5),
   (29, t29_3, t29_5),
   (31, t31_3, t31_5),
   (37, t37_3, t37_5),
   (41, t41_3, t41_5),
   (43, t43_3, t43_5),
   (47, t47_3, t47_5),
   (53, t53_3, t53_5),
   (59, t59_3, t59_5),
   (61, t61_3, t61_5),
   (67, t67_3, t67_5),
   (71, t71_3, t71_5),
   (73, t73_3, t73_5),
   (79, t79_3, t79_5),
   (83, t83_3, t83_5),
   (89, t89_3, t89_5),
   (97, t97_3, t97_5),
   (101, t101_3, t101_5),
   (103, t103_3, t103_5),
   (107, t107_3, t107_5),
   (109, t109_3, t109_5),
   (113, t113_3, t113_5)]

/-- The lengths of the table. -/
def ls : List ℕ := [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79,
    83, 89, 97, 101, 103, 107, 109, 113]

theorem tab_ls : tab.map Prod.fst = ls := rfl

theorem ok5 : tableOK pc [(5, t5_3, t5_5)] = true := by
  decide +kernel

theorem ok7 : tableOK pc [(7, t7_3, t7_5)] = true := by
  decide +kernel

theorem ok11 : tableOK pc [(11, t11_3, t11_5)] = true := by
  decide +kernel

theorem ok13 : tableOK pc [(13, t13_3, t13_5)] = true := by
  decide +kernel

theorem ok17 : tableOK pc [(17, t17_3, t17_5)] = true := by
  decide +kernel

theorem ok19 : tableOK pc [(19, t19_3, t19_5)] = true := by
  decide +kernel

theorem ok23 : tableOK pc [(23, t23_3, t23_5)] = true := by
  decide +kernel

theorem ok29 : tableOK pc [(29, t29_3, t29_5)] = true := by
  decide +kernel

theorem ok31 : tableOK pc [(31, t31_3, t31_5)] = true := by
  decide +kernel

theorem ok37 : tableOK pc [(37, t37_3, t37_5)] = true := by
  decide +kernel

theorem ok41 : tableOK pc [(41, t41_3, t41_5)] = true := by
  decide +kernel

theorem ok43 : tableOK pc [(43, t43_3, t43_5)] = true := by
  decide +kernel

theorem ok47 : tableOK pc [(47, t47_3, t47_5)] = true := by
  decide +kernel

theorem ok53 : tableOK pc [(53, t53_3, t53_5)] = true := by
  decide +kernel

theorem ok59 : tableOK pc [(59, t59_3, t59_5)] = true := by
  decide +kernel

theorem ok61 : tableOK pc [(61, t61_3, t61_5)] = true := by
  decide +kernel

theorem ok67 : tableOK pc [(67, t67_3, t67_5)] = true := by
  decide +kernel

theorem ok71 : tableOK pc [(71, t71_3, t71_5)] = true := by
  decide +kernel

theorem ok73 : tableOK pc [(73, t73_3, t73_5)] = true := by
  decide +kernel

theorem ok79 : tableOK pc [(79, t79_3, t79_5)] = true := by
  decide +kernel

theorem ok83 : tableOK pc [(83, t83_3, t83_5)] = true := by
  decide +kernel

theorem ok89 : tableOK pc [(89, t89_3, t89_5)] = true := by
  decide +kernel

theorem ok97 : tableOK pc [(97, t97_3, t97_5)] = true := by
  decide +kernel

theorem ok101 : tableOK pc [(101, t101_3, t101_5)] = true := by
  decide +kernel

theorem ok103 : tableOK pc [(103, t103_3, t103_5)] = true := by
  decide +kernel

theorem ok107 : tableOK pc [(107, t107_3, t107_5)] = true := by
  decide +kernel

theorem ok109 : tableOK pc [(109, t109_3, t109_5)] = true := by
  decide +kernel

theorem ok113 : tableOK pc [(113, t113_3, t113_5)] = true := by
  decide +kernel

theorem tab_ok : tableOK pc tab = true :=
  tableOK_cons ok5 <|
  tableOK_cons ok7 <|
  tableOK_cons ok11 <|
  tableOK_cons ok13 <|
  tableOK_cons ok17 <|
  tableOK_cons ok19 <|
  tableOK_cons ok23 <|
  tableOK_cons ok29 <|
  tableOK_cons ok31 <|
  tableOK_cons ok37 <|
  tableOK_cons ok41 <|
  tableOK_cons ok43 <|
  tableOK_cons ok47 <|
  tableOK_cons ok53 <|
  tableOK_cons ok59 <|
  tableOK_cons ok61 <|
  tableOK_cons ok67 <|
  tableOK_cons ok71 <|
  tableOK_cons ok73 <|
  tableOK_cons ok79 <|
  tableOK_cons ok83 <|
  tableOK_cons ok89 <|
  tableOK_cons ok97 <|
  tableOK_cons ok101 <|
  tableOK_cons ok103 <|
  tableOK_cons ok107 <|
  tableOK_cons ok109 <|
  tableOK_cons ok113 <|
  tableOK_nil pc

end OddPerfect.ImpTree.ImpureRowTreeD01

#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.tab_ls
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.tab_ok
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok5
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok7
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok11
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok13
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok17
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok19
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok23
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok29
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok31
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok37
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok41
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok43
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok47
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok53
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok59
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok61
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok67
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok71
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok73
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok79
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok83
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok89
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok97
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok101
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok103
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok107
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok109
#print axioms OddPerfect.ImpTree.ImpureRowTreeD01.ok113
