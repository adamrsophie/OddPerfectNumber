import OddPerfect.LargestPrimeFactorThreeData

/-!
# Row certificates for the largest prime factor bound `200000`, part 3 of 3

Certificates `(p, R, X, EXS, EX)` of the rows of 49 primes of the search table, found
outside Lean (`scripts/LargestPrimeFactor/gen6.py`) and checked here by the kernel with
`LPF3.rowOK3`, one prime at a time.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

namespace OddPerfect

namespace LPF3

private def c83 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (83, [2, 8], [3], [(487, 23726641)], [(27, 617814746067115231)])

private theorem ok83 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c83 = true := by decide +kernel

private def c89 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (89, [1, 2, 4, 5], [3, 5], [], [(9, 584803), (10, 885200332950), (15, 508339775431), (25, 63455221)])

private theorem ok89 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c89 = true := by decide +kernel

private def c8011 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (8011, [4], [5], [], [(25, 1197645630809571009275)])

private theorem ok8011 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c8011 = true := by decide +kernel

private def c8647 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (8647, [2], [3], [], [(9, 224337771)])

private theorem ok8647 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c8647 = true := by decide +kernel

private def c101 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (101, [1, 2, 4, 5], [3, 5], [], [(9, 195757), (10, 117923327610), (15, 27833755312178849965), (25, 525505025)])

private theorem ok101 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c101 = true := by decide +kernel

private def c10303 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (10303, [2], [3], [], [(9, 20156681908971)])

private theorem ok10303 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c10303 = true := by decide +kernel

private def c107 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (107, [2], [3], [], [(9, 427609)])

private theorem ok107 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c107 = true := by decide +kernel

private def c113 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (113, [1, 2, 4, 5, 9], [3, 5], [], [(9, 219616501), (15, 45397396035039763), (25, 164503141)])

private theorem ok113 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c113 = true := by decide +kernel

private def c137 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (137, [1, 2, 5], [3], [(29, 3481)], [(9, 10003561351)])

private theorem ok137 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c137 = true := by decide +kernel

private def c149 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (149, [1, 2, 4, 5, 9], [3, 5], [], [(9, 53932963), (15, 11090894782051), (25, 1414708112551)])

private theorem ok149 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c149 = true := by decide +kernel

private def c251 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (251, [2], [3], [(5, 121)], [(9, 227488845223)])

private theorem ok251 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c251 = true := by decide +kernel

private def c167 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (167, [2, 4], [3, 5], [], [(9, 28057), (15, 1992355895017045687), (25, 782481841)])

private theorem ok167 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c167 = true := by decide +kernel

private def c28057 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (28057, [1], [], [(2819, 31798321)], [])

private theorem ok28057 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c28057 = true := by decide +kernel

private def c14029 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (14029, [1, 2], [3], [], [(6, 2761481000130), (9, 27911428095897)])

private theorem ok14029 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c14029 = true := by decide +kernel

private def c173 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (173, [1, 2, 4, 5], [3, 5], [], [(9, 360085854679), (10, 225899514649974), (15, 840762903215173), (25, 361282097261)])

private theorem ok173 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c173 = true := by decide +kernel

private def c30103 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (30103, [2], [3], [], [(9, 5679285208371)])

private theorem ok30103 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c30103 = true := by decide +kernel

private def c9431 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (9431, [], [], [], [])

private theorem ok9431 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c9431 = true := by decide +kernel

private def c179 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (179, [2], [3], [], [(9, 15103819297)])

private theorem ok179 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c179 = true := by decide +kernel

private def c199 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (199, [2], [3], [], [(9, 1880716653)])

private theorem ok199 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c199 = true := by decide +kernel

private def c223 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (223, [2, 4], [3, 5], [], [(9, 10939707), (15, 124088894740833), (25, 95942617315891270661)])

private theorem ok223 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c223 = true := by decide +kernel

private def c227 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (227, [2], [3], [], [(9, 2719468051)])

private theorem ok227 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c227 = true := by decide +kernel

private def c229 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (229, [1, 2, 5], [3], [], [(9, 816221365929)])

private theorem ok229 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c229 = true := by decide +kernel

private def c233 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (233, [1, 2, 5], [3], [], [(9, 21519519301)])

private theorem ok233 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c233 = true := by decide +kernel

private def c239 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (239, [2], [3], [], [(9, 57361)])

private theorem ok239 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c239 = true := by decide +kernel

private def c241 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (241, [1, 2, 5], [3], [], [(9, 463142943)])

private theorem ok241 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c241 = true := by decide +kernel

private def c257 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (257, [1, 2, 5], [3], [], [(9, 809690491759)])

private theorem ok257 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c257 = true := by decide +kernel

private def c263 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (263, [2], [3], [], [(9, 1319227)])

private theorem ok263 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c263 = true := by decide +kernel

private def c269 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (269, [1, 2, 5, 6], [3, 7], [(5, 121)], [(9, 72631), (14, 43229182822837697970), (21, 438552543785017312436617), (49, 380304238786291)])

private theorem ok269 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c269 = true := by decide +kernel

private def c277 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (277, [1, 2, 5], [3], [], [(9, 3064955607)])

private theorem ok277 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c277 = true := by decide +kernel

private def c283 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (283, [2], [3], [], [(9, 4581261)])

private theorem ok283 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c283 = true := by decide +kernel

private def c293 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (293, [1, 2, 5], [3], [(41, 5090971)], [(9, 9699471539761)])

private theorem ok293 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c293 = true := by decide +kernel

private def c86143 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (86143, [], [], [], [])

private theorem ok86143 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c86143 = true := by decide +kernel

private def c311 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (311, [2], [3], [], [(9, 10128595639)])

private theorem ok311 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c311 = true := by decide +kernel

private def c317 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (317, [1, 2, 5], [3], [], [(9, 2567964473683)])

private theorem ok317 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c317 = true := by decide +kernel

private def c337 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (337, [1, 2, 5], [3], [], [(9, 344796489)])

private theorem ok337 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c337 = true := by decide +kernel

private def c347 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (347, [2], [3], [], [(9, 217234476823)])

private theorem ok347 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c347 = true := by decide +kernel

private def c349 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (349, [1, 2, 5], [3], [], [(9, 13558761)])

private theorem ok349 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c349 = true := by decide +kernel

private def c353 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (353, [1, 2, 5], [3], [], [(9, 4872182407)])

private theorem ok353 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c353 = true := by decide +kernel

private def c359 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (359, [2, 6], [3, 7], [], [(9, 2455579), (21, 487622115129703041363328579), (49, 2146733400397321)])

private theorem ok359 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c359 = true := by decide +kernel

private def c373 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (373, [1, 2, 5], [3], [], [(9, 8851849959771)])

private theorem ok373 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c373 = true := by decide +kernel

private def c379 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (379, [2, 8], [3], [], [(27, 1280508143055705662643)])

private theorem ok379 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c379 = true := by decide +kernel

private def c383 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (383, [2], [3], [], [(9, 147073)])

private theorem ok383 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c383 = true := by decide +kernel

private def c147073 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (147073, [1], [], [], [])

private theorem ok147073 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c147073 = true := by decide +kernel

private def c389 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (389, [1, 2, 4, 5, 6, 9], [3, 5, 7], [], [(9, 139055116669), (14, 429214639749691469641253130), (15, 630393790920928111), (21, 778418322766340934204457), (25, 34763483207747710471), (35, 79750197034791920324143951), (49, 3473885370230731)])

private theorem ok389 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c389 = true := by decide +kernel

private def c397 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (397, [1, 2, 5], [3], [], [(9, 657467127)])

private theorem ok397 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c397 = true := by decide +kernel

private def c401 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (401, [1, 2, 5], [3], [(41, 5090971)], [(9, 29177743)])

private theorem ok401 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c401 = true := by decide +kernel

private def c419 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (419, [2], [3], [], [(9, 188938305049)])

private theorem ok419 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c419 = true := by decide +kernel

private def c421 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (421, [1, 2, 4, 5, 9], [3, 5], [], [(9, 532989), (15, 1175298228326470091616547665), (25, 1251851881989775)])

private theorem ok421 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c421 = true := by decide +kernel

private def c431 : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (431, [2], [3], [(23, 269143103)], [(9, 186193)])

private theorem ok431 : rowOK3 bigM200000 bigXU200000 listDR200000 listL200000 c431 = true := by decide +kernel

/-- The row certificates of part 3 for the bound `200000`. -/
def certs200000_3 : List (ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)) :=
  [c83, c89, c8011, c8647, c101, c10303, c107, c113, c137, c149, c251, c167, c28057, c14029, c173, c30103, c9431, c179, c199, c223, c227, c229, c233, c239, c241, c257, c263, c269, c277, c283, c293, c86143, c311, c317, c337, c347, c349, c353, c359, c373, c379, c383, c147073, c389, c397, c401, c419, c421, c431]

/-- The row certificates of part 3 pass `rowOK3`. -/
theorem certs200000_3_ok : certs200000_3.all (rowOK3 bigM200000 bigXU200000 listDR200000 listL200000) = true := by
  simp only [certs200000_3, List.all_cons, List.all_nil, ok83, ok89, ok8011, ok8647, ok101, ok10303, ok107, ok113, ok137, ok149, ok251, ok167, ok28057, ok14029, ok173, ok30103, ok9431, ok179, ok199, ok223, ok227, ok229, ok233, ok239, ok241, ok257, ok263, ok269, ok277, ok283, ok293, ok86143, ok311, ok317, ok337, ok347, ok349, ok353, ok359, ok373, ok379, ok383, ok147073, ok389, ok397, ok401, ok419, ok421, ok431, Bool.true_and]

end LPF3

end OddPerfect

#print axioms OddPerfect.LPF3.certs200000_3_ok
