import OddPerfect.LargestPrimeFactorThreeData

/-!
# Row certificates for the largest prime factor bound `200000`, part 1 of 3

Certificates `(p, R, X, EXS, EX)` of the rows of 48 primes of the search table, found
outside Lean (`scripts/LargestPrimeFactor/gen6.py`) and checked here by the kernel with
`LPF3.rowOK3`, one prime at a time.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

namespace OddPerfect

namespace LPF3

private def c3 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (3, [2, 4, 6, 8, 10, 14, 16, 26, 48], [3, 5, 7, 11, 17, 31], [], [(21, 14209), (25, 1083071), (31, 70125659), (33, 1151449), (35, 9389963), (45, 1593478705282321), (51, 10788950264209), (55, 155733565823), (77, 96810289), (81, 14827974309555277), (85, 7812979801), (119, 16867448549387), (121, 1028952541), (187, 36368175223082267), (289, 2873820595067), (343, 2954987767004280564143127577)])

private theorem ok3 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c3 = true := by decide +kernel

private def c13 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (13, [1, 2, 4, 5, 9, 10, 14], [3, 5, 11], [], [(9, 549), (22, 2090853793042), (25, 213664653491), (30, 7708117317840512386772574), (33, 27330446009049), (55, 13220498552091166103), (121, 149346699503)])

private theorem ok13 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c13 = true := by decide +kernel

private def c7 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (7, [2, 4, 6, 8, 14], [3, 5, 7], [], [(21, 7823649), (25, 7145351), (27, 4239639088359669), (35, 384456857), (45, 93363170873764401), (49, 484379953)])

private theorem ok7 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c7 = true := by decide +kernel

private def c19 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (19, [2, 4, 6, 8], [3, 5, 7], [], [(15, 342818656881), (21, 18920285121), (25, 143494439384711), (27, 26191484802981), (35, 485016344484571), (49, 49659541)])

private theorem ok19 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c19 = true := by decide +kernel

private def c127 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (127, [2, 6], [3, 7], [], [(9, 3932064333), (21, 68753673481829889), (49, 29604214453639)])

private theorem ok127 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c127 = true := by decide +kernel

private def c5419 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (5419, [2], [3], [], [(9, 139260235328550930274479)])

private theorem ok5419 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c5419 = true := by decide +kernel

private def c31 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (31, [2, 4, 8], [3, 5], [], [(15, 2388962284665), (25, 2386005847775), (27, 2643962216067)])

private theorem ok31 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c31 = true := by decide +kernel

private def c331 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (331, [2, 4], [3, 5], [(179, 128881)], [(9, 329679), (15, 522047732906169402765), (25, 914936755487844025)])

private theorem ok331 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c331 = true := by decide +kernel

private def c5233 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (5233, [1, 2, 5], [3], [], [(9, 15052213649403)])

private theorem ok5233 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c5233 = true := by decide +kernel

private def c42073 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (42073, [1, 2], [3], [], [(6, 113132884338567618), (9, 22442793710646699693)])

private theorem ok42073 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c42073 = true := by decide +kernel

private def c409 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (409, [1, 2, 4, 5], [3, 5], [(17291, 1195983889)], [(9, 503073), (10, 177749850064435550), (15, 1980378612196284291), (25, 2833203376681)])

private theorem ok409 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c409 = true := by decide +kernel

private def c5 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (5, [1, 2, 4, 5, 6, 8, 9, 13, 14, 17, 26, 29], [3, 5, 7], [], [(21, 229469719), (25, 7939451531), (35, 8531787106590451), (45, 23898578359591342067881), (49, 19531), (54, 866359630633145570638724061558), (81, 9054318070411682127691)])

private theorem ok5 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c5 = true := by decide +kernel

private def c43 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (43, [2, 6, 8], [3, 7], [], [(21, 2585014407233139), (27, 35899472281203), (49, 22243823008841)])

private theorem ok43 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c43 = true := by decide +kernel

private def c631 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (631, [2, 4], [3, 5], [], [(9, 22731201), (15, 793338318925642924242765), (25, 1395313614849289025)])

private theorem ok631 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c631 = true := by decide +kernel

private def c307 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (307, [2, 4], [3, 5], [], [(9, 283671), (15, 37011646489713172097536598667), (25, 8911903001)])

private theorem ok307 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c307 = true := by decide +kernel

private def c733 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (733, [1, 2, 5], [3], [], [(9, 125133927363)])

private theorem ok733 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c733 = true := by decide +kernel

private def c9439 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (9439, [], [], [], [])

private theorem ok9439 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c9439 = true := by decide +kernel

private def c1051 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (1051, [], [], [], [])

private theorem ok1051 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c1051 = true := by decide +kernel

private def c5839 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (5839, [], [], [(41, 6889)], [])

private theorem ok5839 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c5839 = true := by decide +kernel

private def c181 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (181, [1, 2, 5], [3], [], [(9, 91296154791)])

private theorem ok181 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c181 = true := by decide +kernel

private def c79 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (79, [2, 6], [3, 7], [], [(9, 7528311), (21, 234145614864691057754667), (49, 246203961361)])

private theorem ok79 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c79 = true := by decide +kernel

private def c151 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (151, [2], [3], [], [(9, 7656225633)])

private theorem ok151 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c151 = true := by decide +kernel

private def c1093 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (1093, [1], [], [], [])

private theorem ok1093 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c1093 = true := by decide +kernel

private def c701 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (701, [1], [], [], [])

private theorem ok701 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c701 = true := by decide +kernel

private def c2801 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (2801, [1, 2, 5], [3], [], [(9, 7848403)])

private theorem ok2801 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c2801 = true := by decide +kernel

private def c37 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (37, [1, 2, 4, 5, 8], [3, 5], [], [(10, 73196398), (15, 29107718878338177), (18, 36389814209677115586), (25, 544929847121), (27, 95337766284671169)])

private theorem ok37 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c37 = true := by decide +kernel

private def c67 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (67, [2, 4], [3, 5], [], [(9, 13671), (15, 111452994977182467), (25, 1328666299391)])

private theorem ok67 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c67 = true := by decide +kernel

private def c761 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (761, [1], [], [], [])

private theorem ok761 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c761 = true := by decide +kernel

private def c11 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (11, [2, 4, 6, 20], [3, 5, 7], [], [(9, 133), (15, 2141965), (25, 5836222584275), (35, 6622042417135), (49, 1948717)])

private theorem ok11 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c11 = true := by decide +kernel

private def c29 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (29, [1, 2, 5, 8], [3], [], [(18, 720295341072534630), (27, 27363067872268453)])

private theorem ok29 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c29 = true := by decide +kernel

private def c61 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (61, [1, 2, 4, 5], [3, 5], [], [(9, 215631), (10, 9600244610), (15, 53251796715), (25, 3586085506775)])

private theorem ok61 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c61 = true := by decide +kernel

private def c97 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (97, [1, 2, 5], [3], [], [(9, 32884713)])

private theorem ok97 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c97 = true := by decide +kernel

private def c3169 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (3169, [1], [], [], [])

private theorem ok3169 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c3169 = true := by decide +kernel

private def c131 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (131, [2], [3], [], [(9, 328567)])

private theorem ok131 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c131 = true := by decide +kernel

private def c17293 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (17293, [1], [], [], [])

private theorem ok17293 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c17293 = true := by decide +kernel

private def c19531 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (19531, [], [], [(11, 2200111)], [])

private theorem ok19531 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c19531 = true := by decide +kernel

private def c30941 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (30941, [1, 2, 5], [3], [], [(9, 77534377078134169)])

private theorem ok30941 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c30941 = true := by decide +kernel

private def c191 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (191, [2, 4, 6], [3, 5, 7], [], [(9, 36673), (15, 51369669338657735065), (21, 12529231920558447367), (25, 13283853689441070442025), (35, 4636086749371793982473735), (49, 48806759042497)])

private theorem ok191 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c191 = true := by decide +kernel

private def c523 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (523, [2], [3], [], [(9, 822159)])

private theorem ok523 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c523 = true := by decide +kernel

private def c7027 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (7027, [2], [3], [(5, 4961)], [(9, 104154561513)])

private theorem ok7027 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c7027 = true := by decide +kernel

private def c1879 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (1879, [], [], [], [])

private theorem ok1879 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c1879 = true := by decide +kernel

private def c157 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (157, [1, 2, 5], [3], [], [(9, 135660478059)])

private theorem ok157 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c157 = true := by decide +kernel

private def c281 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (281, [1, 2, 4, 5], [3, 5], [], [(9, 2316879336679), (10, 19409545309110), (15, 3720509974881465604165), (25, 3159838936525)])

private theorem ok281 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c281 = true := by decide +kernel

private def c109 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (109, [1, 2, 4, 5], [3, 5], [], [(9, 316670319), (10, 78355849550), (15, 9995263214405721), (25, 683975333981)])

private theorem ok109 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c109 = true := by decide +kernel

private def c8269 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (8269, [1], [], [(11, 529)], [])

private theorem ok8269 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c8269 = true := by decide +kernel

private def c23 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (23, [2], [3], [], [(9, 10507)])

private theorem ok23 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c23 = true := by decide +kernel

private def c467 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (467, [2], [3], [], [(9, 133975441)])

private theorem ok467 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c467 = true := by decide +kernel

private def c41 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (41, [1, 2, 5], [3], [], [(9, 839101)])

private theorem ok41 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c41 = true := by decide +kernel

/-- The row certificates of part 1 for the bound `200000`. -/
def certs200000_1 : List (ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)) :=
  [c3, c13, c7, c19, c127, c5419, c31, c331, c5233, c42073, c409, c5, c43, c631, c307, c733, c9439, c1051, c5839, c181, c79, c151, c1093, c701, c2801, c37, c67, c761, c11, c29, c61, c97, c3169, c131, c17293, c19531, c30941, c191, c523, c7027, c1879, c157, c281, c109, c8269, c23, c467, c41]

/-- The row certificates of part 1 pass `rowOK3`. -/
theorem certs200000_1_ok : certs200000_1.all (rowOK3 bigM200000 bigXU200000 listDR200000 listL200000) = true := by
  simp only [certs200000_1, List.all_cons, List.all_nil, ok3, ok13, ok7, ok19, ok127, ok5419, ok31, ok331, ok5233, ok42073, ok409, ok5, ok43, ok631, ok307, ok733, ok9439, ok1051, ok5839, ok181, ok79, ok151, ok1093, ok701, ok2801, ok37, ok67, ok761, ok11, ok29, ok61, ok97, ok3169, ok131, ok17293, ok19531, ok30941, ok191, ok523, ok7027, ok1879, ok157, ok281, ok109, ok8269, ok23, ok467, ok41, Bool.true_and]

end LPF3

end OddPerfect

#print axioms OddPerfect.LPF3.certs200000_1_ok
