import OddPerfect.LargestPrimeFactorThreeData

/-!
# Row certificates for the largest prime factor bound `200000`, part 2 of 3

Certificates `(p, R, X, EXS, EX)` of the rows of 48 primes of the search table, found
outside Lean (`scripts/LargestPrimeFactor/gen6.py`) and checked here by the kernel with
`LPF3.rowOK3`, one prime at a time.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

namespace OddPerfect

namespace LPF3

private def c3221 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (3221, [1], [], [], [])

private theorem ok3221 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c3221 = true := by decide +kernel

private def c367 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (367, [2], [3], [], [(9, 417709985358861)])

private theorem ok367 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c367 = true := by decide +kernel

private def c547 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (547, [2], [3], [], [(9, 1571026437)])

private theorem ok547 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c547 = true := by decide +kernel

private def c163 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (163, [2, 4], [3, 5], [], [(9, 80199), (15, 18987627619653), (25, 746492972291)])

private theorem ok163 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c163 = true := by decide +kernel

private def c55897 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (55897, [1, 2, 5], [3], [], [(9, 9373591521)])

private theorem ok55897 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c55897 = true := by decide +kernel

private def c937 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (937, [1], [], [], [])

private theorem ok937 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c937 = true := by decide +kernel

private def c71 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (71, [2, 4], [3, 5], [(23, 2209)], [(9, 189181), (15, 4048599754015465), (25, 13016226025)])

private theorem ok71 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c71 = true := by decide +kernel

private def c5113 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (5113, [1], [], [], [])

private theorem ok5113 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c5113 = true := by decide +kernel

private def c139 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (139, [2], [3], [], [(9, 1109277)])

private theorem ok139 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c139 = true := by decide +kernel

private def c571 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (571, [2], [3], [(7, 841)], [(9, 36254043)])

private theorem ok571 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c571 = true := by decide +kernel

private def c103 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (103, [2], [3], [], [(9, 58926824361)])

private theorem ok103 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c103 = true := by decide +kernel

private def c3571 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (3571, [2], [3], [], [(9, 38266839)])

private theorem ok3571 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c3571 = true := by decide +kernel

private def c911 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (911, [], [], [], [])

private theorem ok911 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c911 = true := by decide +kernel

private def c2617 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (2617, [1, 2, 5], [3], [(11, 349669)], [(9, 16248018427947)])

private theorem ok2617 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c2617 = true := by decide +kernel

private def c193 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (193, [1, 2, 5], [3], [], [(9, 112329)])

private theorem ok193 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c193 = true := by decide +kernel

private def c1783 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (1783, [2], [3], [], [(9, 77139716035931433)])

private theorem ok1783 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c1783 = true := by decide +kernel

private def c829 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (829, [1, 2, 5], [3], [], [(9, 224999217)])

private theorem ok829 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c829 = true := by decide +kernel

private def c211 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (211, [2], [3], [], [(9, 24093149067)])

private theorem ok211 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c211 = true := by decide +kernel

private def c1871 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (1871, [2], [3], [], [(9, 66547747)])

private theorem ok1871 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c1871 = true := by decide +kernel

private def c197 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (197, [1, 2, 4, 5, 9], [3, 5], [(163, 426409)], [(9, 1066568401), (15, 40803334642267657), (25, 11453585280148861)])

private theorem ok197 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c197 = true := by decide +kernel

private def c2053 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (2053, [1, 2, 5], [3], [(11, 71900093)], [(9, 2289756609)])

private theorem ok2053 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c2053 = true := by decide +kernel

private def c661 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (661, [1, 2, 5], [3], [], [(9, 1381782531663)])

private theorem ok661 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c661 = true := by decide +kernel

private def c145861 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (145861, [1], [], [(491, 966289)], [])

private theorem ok145861 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c145861 = true := by decide +kernel

private def c1471 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (1471, [2], [3], [(11, 10472837)], [(9, 474262010451)])

private theorem ok1471 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c1471 = true := by decide +kernel

private def c823 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (823, [2], [3], [(577, 5331481)], [(9, 13130892759537)])

private theorem ok823 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c823 = true := by decide +kernel

private def c158791 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (158791, [], [], [], [])

private theorem ok158791 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c158791 = true := by decide +kernel

private def c2557 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (2557, [1, 2], [3], [], [(6, 16731384306), (9, 54144846530638227)])

private theorem ok2557 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c2557 = true := by decide +kernel

private def c47 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (47, [2, 4], [3, 5], [], [(9, 42883), (15, 568843456129927), (25, 5606736540383561)])

private theorem ok47 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c47 = true := by decide +kernel

private def c313 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (313, [1, 2, 5], [3], [], [(9, 190287583677)])

private theorem ok313 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c313 = true := by decide +kernel

private def c727 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (727, [2], [3], [], [(9, 29885693313324843)])

private theorem ok727 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c727 = true := by decide +kernel

private def c176419 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (176419, [], [], [], [])

private theorem ok176419 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c176419 = true := by decide +kernel

private def c491 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (491, [2], [3], [], [(9, 4589887)])

private theorem ok491 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c491 = true := by decide +kernel

private def c1063 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (1063, [], [], [], [])

private theorem ok1063 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c1063 = true := by decide +kernel

private def c86353 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (86353, [1], [], [(7, 1967099), (23, 307051), (29, 3481)], [])

private theorem ok86353 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c86353 = true := by decide +kernel

private def c43177 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (43177, [1], [], [(29, 56333023)], [])

private theorem ok43177 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c43177 = true := by decide +kernel

private def c1723 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (1723, [], [], [], [])

private theorem ok1723 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c1723 = true := by decide +kernel

private def c24061 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (24061, [1, 2], [3], [], [(6, 19071311815197474), (9, 1736867349)])

private theorem ok24061 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c24061 = true := by decide +kernel

private def c3187 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (3187, [2], [3], [], [(9, 19233177201)])

private theorem ok3187 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c3187 = true := by decide +kernel

private def c271 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (271, [2], [3], [], [(9, 155460717)])

private theorem ok271 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c271 = true := by decide +kernel

private def c2411 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (2411, [], [], [(23, 74180429)], [])

private theorem ok2411 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c2411 = true := by decide +kernel

private def c53 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (53, [1, 2, 4, 5, 8, 9], [3, 5], [(23, 236313520609), (29, 425806363)], [(15, 23024878723), (18, 538498954406886827886), (25, 6039707971), (27, 6275000877627853956166939)])

private theorem ok53 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c53 = true := by decide +kernel

private def c17351 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (17351, [2], [3], [], [(9, 5720416507)])

private theorem ok17351 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c17351 = true := by decide +kernel

private def c17 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (17, [1, 2, 4, 5, 9], [3, 5], [(24473, 2395808809)], [(9, 5833), (15, 27243487), (25, 1211350235141)])

private theorem ok17 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c17 = true := by decide +kernel

private def c88741 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (88741, [1, 2], [3], [(1549, 1070785523347)], [(6, 16949161183325232498), (9, 23625161469)])

private theorem ok88741 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c88741 = true := by decide +kernel

private def c44371 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (44371, [], [], [], [])

private theorem ok44371 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c44371 = true := by decide +kernel

private def c59 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (59, [2, 4, 6], [3, 5, 7], [], [(9, 5166319), (15, 2071547401417681), (21, 151936463926561), (25, 417256938131), (35, 528893405395412101), (49, 8452833491537)])

private theorem ok59 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c59 = true := by decide +kernel

private def c3541 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (3541, [1, 2], [3], [], [(6, 44424553866), (9, 4304152293579)])

private theorem ok3541 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c3541 = true := by decide +kernel

private def c73 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (73, [1, 2, 5], [3], [], [(9, 55742751)])

private theorem ok73 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c73 = true := by decide +kernel

/-- The row certificates of part 2 for the bound `200000`. -/
def certs200000_2 : List (ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)) :=
  [c3221, c367, c547, c163, c55897, c937, c71, c5113, c139, c571, c103, c3571, c911, c2617, c193, c1783, c829, c211, c1871, c197, c2053, c661, c145861, c1471, c823, c158791, c2557, c47, c313, c727, c176419, c491, c1063, c86353, c43177, c1723, c24061, c3187, c271, c2411, c53, c17351, c17, c88741, c44371, c59, c3541, c73]

/-- The row certificates of part 2 pass `rowOK3`. -/
theorem certs200000_2_ok : certs200000_2.all (rowOK3 bigM200000 bigXU200000 listDR200000 listL200000) = true := by
  simp only [certs200000_2, List.all_cons, List.all_nil, ok3221, ok367, ok547, ok163, ok55897, ok937, ok71, ok5113, ok139, ok571, ok103, ok3571, ok911, ok2617, ok193, ok1783, ok829, ok211, ok1871, ok197, ok2053, ok661, ok145861, ok1471, ok823, ok158791, ok2557, ok47, ok313, ok727, ok176419, ok491, ok1063, ok86353, ok43177, ok1723, ok24061, ok3187, ok271, ok2411, ok53, ok17351, ok17, ok88741, ok44371, ok59, ok3541, ok73, Bool.true_and]

end LPF3

end OddPerfect

#print axioms OddPerfect.LPF3.certs200000_2_ok
