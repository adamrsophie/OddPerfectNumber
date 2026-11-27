import OddPerfect.EulerIndexPairReceiverCore

/-!
# Two prime Euler index, branch `v = 1`: receiver certificates 97 to 107

Restricted result; no published source was checked; novelty not verified. The odd perfect
number conjecture remains open.

For each prime receiver `u` with `97 ≤ u ≤ 107`, a certificate `(A, L)` accepted by
`ReceiverSieve.packRow` (kernel evaluation): the absent primes `A` with their divisor lists, and
the envelope `L`. The set of kept pure row lengths is computed by the checker from `u`. Each
receiver needs its own finite certificate; no uniform statement over all receivers is proved.
-/

namespace OddPerfect
namespace ReceiverPack

open ReceiverSieve

def row97A0 : List (ℕ × List ℕ) :=
  [(5, []), (11, []), (13, []), (17, []), (23, []), (29, []), (37, []), (41, []), (47, []),
   (53, []), (61, [39]), (67, [])]

def row97A : List (ℕ × List ℕ) := row97A0

def row97L0 : List ℕ :=
  [7, 19, 31, 43, 59, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149,
   151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
   257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367,
   373, 379, 383, 389]

def row97L1 : List ℕ :=
  [397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
   509]

def row97L2 : List ℕ :=
  [521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599]

def row97L3 : List ℕ :=
  [601, 607, 613]

def row97P1 : List ℕ := row97L0

def row97P2 : List ℕ := row97P1 ++ row97L1

def row97P3 : List ℕ := row97P2 ++ row97L2

def row97L : List ℕ := row97P3 ++ row97L3

theorem row97_a0 : absentOK 97 row97A0 = true := by decide +kernel

theorem row97_e0 : envOK (row97A.map Prod.fst) 5 row97L0 = true := by
  decide +kernel

theorem row97_e1 :
    envOK (row97P1.reverse ++ row97A.map Prod.fst) (envNext 5 row97P1) row97L1 =
      true := by
  decide +kernel

theorem row97_e2 :
    envOK (row97P2.reverse ++ row97A.map Prod.fst) (envNext 5 row97P2) row97L2 =
      true := by
  decide +kernel

theorem row97_e3 :
    envOK (row97P3.reverse ++ row97A.map Prod.fst) (envNext 5 row97P3) row97L3 =
      true := by
  decide +kernel

theorem row97_t : tailOK 97 row97L = true := by decide +kernel

/-- Receiver 97: the certificate is accepted. -/
theorem row97_ok : packRow 97 row97A row97L = true := by
  have a : absentOK 97 row97A0 = true := row97_a0
  have e : envOK (row97A.map Prod.fst) 5 row97P1 = true := row97_e0
  have e : envOK (row97A.map Prod.fst) 5 row97P2 = true :=
    envOK_of_append e row97_e1
  have e : envOK (row97A.map Prod.fst) 5 row97P3 = true :=
    envOK_of_append e row97_e2
  have e : envOK (row97A.map Prod.fst) 5 row97L = true :=
    envOK_of_append e row97_e3
  exact packRow_of_parts a e row97_t

def row101A0 : List (ℕ × List ℕ) :=
  [(5, [11]), (7, []), (11, []), (13, []), (17, []), (19, [151])]

def row101A : List (ℕ × List ℕ) := row101A0

def row101L0 : List ℕ :=
  [23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
   127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227,
   229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337,
   347, 349, 353, 359, 367, 373, 379, 383, 389]

def row101L1 : List ℕ :=
  [397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
   509]

def row101L2 : List ℕ :=
  [521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599]

def row101L3 : List ℕ :=
  [601, 607]

def row101P1 : List ℕ := row101L0

def row101P2 : List ℕ := row101P1 ++ row101L1

def row101P3 : List ℕ := row101P2 ++ row101L2

def row101L : List ℕ := row101P3 ++ row101L3

theorem row101_a0 : absentOK 101 row101A0 = true := by decide +kernel

theorem row101_e0 : envOK (row101A.map Prod.fst) 5 row101L0 = true := by
  decide +kernel

theorem row101_e1 :
    envOK (row101P1.reverse ++ row101A.map Prod.fst) (envNext 5 row101P1) row101L1 =
      true := by
  decide +kernel

theorem row101_e2 :
    envOK (row101P2.reverse ++ row101A.map Prod.fst) (envNext 5 row101P2) row101L2 =
      true := by
  decide +kernel

theorem row101_e3 :
    envOK (row101P3.reverse ++ row101A.map Prod.fst) (envNext 5 row101P3) row101L3 =
      true := by
  decide +kernel

theorem row101_t : tailOK 101 row101L = true := by decide +kernel

/-- Receiver 101: the certificate is accepted. -/
theorem row101_ok : packRow 101 row101A row101L = true := by
  have a : absentOK 101 row101A0 = true := row101_a0
  have e : envOK (row101A.map Prod.fst) 5 row101P1 = true := row101_e0
  have e : envOK (row101A.map Prod.fst) 5 row101P2 = true :=
    envOK_of_append e row101_e1
  have e : envOK (row101A.map Prod.fst) 5 row101P3 = true :=
    envOK_of_append e row101_e2
  have e : envOK (row101A.map Prod.fst) 5 row101L = true :=
    envOK_of_append e row101_e3
  exact packRow_of_parts a e row101_t

def row103A0 : List (ℕ × List ℕ) :=
  [(5, []), (7, [3]), (11, []), (17, [307]), (19, [3]), (23, [62246266355102810647]), (29, [13])]

def row103A : List (ℕ × List ℕ) := row103A0

def row103L0 : List ℕ :=
  [13, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127,
   131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229,
   233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347,
   349, 353, 359, 367, 373, 379, 383, 389]

def row103L1 : List ℕ :=
  [397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
   509]

def row103L2 : List ℕ :=
  [521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599]

def row103L3 : List ℕ :=
  [601, 607, 613, 617]

def row103P1 : List ℕ := row103L0

def row103P2 : List ℕ := row103P1 ++ row103L1

def row103P3 : List ℕ := row103P2 ++ row103L2

def row103L : List ℕ := row103P3 ++ row103L3

theorem row103_a0 : absentOK 103 row103A0 = true := by decide +kernel

theorem row103_e0 : envOK (row103A.map Prod.fst) 5 row103L0 = true := by
  decide +kernel

theorem row103_e1 :
    envOK (row103P1.reverse ++ row103A.map Prod.fst) (envNext 5 row103P1) row103L1 =
      true := by
  decide +kernel

theorem row103_e2 :
    envOK (row103P2.reverse ++ row103A.map Prod.fst) (envNext 5 row103P2) row103L2 =
      true := by
  decide +kernel

theorem row103_e3 :
    envOK (row103P3.reverse ++ row103A.map Prod.fst) (envNext 5 row103P3) row103L3 =
      true := by
  decide +kernel

theorem row103_t : tailOK 103 row103L = true := by decide +kernel

/-- Receiver 103: the certificate is accepted. -/
theorem row103_ok : packRow 103 row103A row103L = true := by
  have a : absentOK 103 row103A0 = true := row103_a0
  have e : envOK (row103A.map Prod.fst) 5 row103P1 = true := row103_e0
  have e : envOK (row103A.map Prod.fst) 5 row103P2 = true :=
    envOK_of_append e row103_e1
  have e : envOK (row103A.map Prod.fst) 5 row103P3 = true :=
    envOK_of_append e row103_e2
  have e : envOK (row103A.map Prod.fst) 5 row103L = true :=
    envOK_of_append e row103_e3
  exact packRow_of_parts a e row103_t

def row107A0 : List (ℕ × List ℕ) :=
  [(5, []), (11, [351497]), (17, []), (19, [gsum 53 19 / 107 ^ 1]), (29, [10601]),
   (41, [gsum 53 41 / 107 ^ 1]), (47, [gsum 53 47 / 107 ^ 1]), (53, [141829]), (59, []),
   (61, [2333]), (67, []), (71, []), (73, []), (79, [2333]), (89, [1851821]), (97, []),
   (101, [gsum 53 101 / 107 ^ 1]), (109, []), (113, []), (137, [gsum 53 137 / 107 ^ 1])]

def row107A : List (ℕ × List ℕ) := row107A0

def row107L0 : List ℕ :=
  [7, 13, 23, 31, 37, 43, 83, 103, 107, 127, 131, 139, 149, 151, 157, 163, 167, 173, 179, 181,
   191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283,
   293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389]

def row107L1 : List ℕ :=
  [397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
   509]

def row107L2 : List ℕ :=
  [521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599]

def row107L3 : List ℕ :=
  [601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673]

def row107L4 : List ℕ :=
  [677, 683, 691, 701, 709, 719, 727, 733]

def row107P1 : List ℕ := row107L0

def row107P2 : List ℕ := row107P1 ++ row107L1

def row107P3 : List ℕ := row107P2 ++ row107L2

def row107P4 : List ℕ := row107P3 ++ row107L3

def row107L : List ℕ := row107P4 ++ row107L4

theorem row107_a0 : absentOK 107 row107A0 = true := by decide +kernel

theorem row107_e0 : envOK (row107A.map Prod.fst) 5 row107L0 = true := by
  decide +kernel

theorem row107_e1 :
    envOK (row107P1.reverse ++ row107A.map Prod.fst) (envNext 5 row107P1) row107L1 =
      true := by
  decide +kernel

theorem row107_e2 :
    envOK (row107P2.reverse ++ row107A.map Prod.fst) (envNext 5 row107P2) row107L2 =
      true := by
  decide +kernel

theorem row107_e3 :
    envOK (row107P3.reverse ++ row107A.map Prod.fst) (envNext 5 row107P3) row107L3 =
      true := by
  decide +kernel

theorem row107_e4 :
    envOK (row107P4.reverse ++ row107A.map Prod.fst) (envNext 5 row107P4) row107L4 =
      true := by
  decide +kernel

theorem row107_t : tailOK 107 row107L = true := by decide +kernel

/-- Receiver 107: the certificate is accepted. -/
theorem row107_ok : packRow 107 row107A row107L = true := by
  have a : absentOK 107 row107A0 = true := row107_a0
  have e : envOK (row107A.map Prod.fst) 5 row107P1 = true := row107_e0
  have e : envOK (row107A.map Prod.fst) 5 row107P2 = true :=
    envOK_of_append e row107_e1
  have e : envOK (row107A.map Prod.fst) 5 row107P3 = true :=
    envOK_of_append e row107_e2
  have e : envOK (row107A.map Prod.fst) 5 row107P4 = true :=
    envOK_of_append e row107_e3
  have e : envOK (row107A.map Prod.fst) 5 row107L = true :=
    envOK_of_append e row107_e4
  exact packRow_of_parts a e row107_t

end ReceiverPack
end OddPerfect

#print axioms OddPerfect.ReceiverPack.row97_a0
#print axioms OddPerfect.ReceiverPack.row97_e0
#print axioms OddPerfect.ReceiverPack.row97_e1
#print axioms OddPerfect.ReceiverPack.row97_e2
#print axioms OddPerfect.ReceiverPack.row97_e3
#print axioms OddPerfect.ReceiverPack.row97_t
#print axioms OddPerfect.ReceiverPack.row97_ok
#print axioms OddPerfect.ReceiverPack.row101_a0
#print axioms OddPerfect.ReceiverPack.row101_e0
#print axioms OddPerfect.ReceiverPack.row101_e1
#print axioms OddPerfect.ReceiverPack.row101_e2
#print axioms OddPerfect.ReceiverPack.row101_e3
#print axioms OddPerfect.ReceiverPack.row101_t
#print axioms OddPerfect.ReceiverPack.row101_ok
#print axioms OddPerfect.ReceiverPack.row103_a0
#print axioms OddPerfect.ReceiverPack.row103_e0
#print axioms OddPerfect.ReceiverPack.row103_e1
#print axioms OddPerfect.ReceiverPack.row103_e2
#print axioms OddPerfect.ReceiverPack.row103_e3
#print axioms OddPerfect.ReceiverPack.row103_t
#print axioms OddPerfect.ReceiverPack.row103_ok
#print axioms OddPerfect.ReceiverPack.row107_a0
#print axioms OddPerfect.ReceiverPack.row107_e0
#print axioms OddPerfect.ReceiverPack.row107_e1
#print axioms OddPerfect.ReceiverPack.row107_e2
#print axioms OddPerfect.ReceiverPack.row107_e3
#print axioms OddPerfect.ReceiverPack.row107_e4
#print axioms OddPerfect.ReceiverPack.row107_t
#print axioms OddPerfect.ReceiverPack.row107_ok
