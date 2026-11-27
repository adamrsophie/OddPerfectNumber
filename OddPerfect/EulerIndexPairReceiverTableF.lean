import OddPerfect.EulerIndexPairReceiverCore

/-!
# Two prime Euler index, branch `v = 1`: receiver certificates 157 to 163

Restricted result; no published source was checked; novelty not verified. The odd perfect
number conjecture remains open.

For each prime receiver `u` with `157 ≤ u ≤ 163`, a certificate `(A, L)` accepted by
`ReceiverSieve.packRow` (kernel evaluation): the absent primes `A` with their divisor lists, and
the envelope `L`. The set of kept pure row lengths is computed by the checker from `u`. Each
receiver needs its own finite certificate; no uniform statement over all receivers is proved.
-/

namespace OddPerfect
namespace ReceiverPack

open ReceiverSieve

def row157A0 : List (ℕ × List ℕ) :=
  [(5, []), (7, []), (11, [7]), (13, []), (17, [307]), (29, []), (31, []), (37, [3]), (41, [])]

def row157A : List (ℕ × List ℕ) := row157A0

def row157L0 : List ℕ :=
  [19, 23, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
   137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
   239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349,
   353, 359, 367, 373, 379, 383, 389]

def row157L1 : List ℕ :=
  [397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
   509]

def row157L2 : List ℕ :=
  [521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599]

def row157L3 : List ℕ :=
  [601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673]

def row157L4 : List ℕ :=
  [677, 683, 691, 701, 709, 719, 727, 733]

def row157L5 : List ℕ :=
  [739, 743, 751, 757, 761, 769, 773, 787]

def row157L6 : List ℕ :=
  [797, 809, 811, 821, 823, 827, 829]

def row157L7 : List ℕ :=
  [839, 853, 857, 859, 863, 877]

def row157L8 : List ℕ :=
  [881, 883, 887, 907, 911, 919]

def row157L9 : List ℕ :=
  [929, 937, 941, 947, 953]

def row157L10 : List ℕ :=
  [967, 971, 977, 983, 991]

def row157L11 : List ℕ :=
  [997, 1009, 1013]

def row157P1 : List ℕ := row157L0

def row157P2 : List ℕ := row157P1 ++ row157L1

def row157P3 : List ℕ := row157P2 ++ row157L2

def row157P4 : List ℕ := row157P3 ++ row157L3

def row157P5 : List ℕ := row157P4 ++ row157L4

def row157P6 : List ℕ := row157P5 ++ row157L5

def row157P7 : List ℕ := row157P6 ++ row157L6

def row157P8 : List ℕ := row157P7 ++ row157L7

def row157P9 : List ℕ := row157P8 ++ row157L8

def row157P10 : List ℕ := row157P9 ++ row157L9

def row157P11 : List ℕ := row157P10 ++ row157L10

def row157L : List ℕ := row157P11 ++ row157L11

theorem row157_a0 : absentOK 157 row157A0 = true := by decide +kernel

theorem row157_e0 : envOK (row157A.map Prod.fst) 5 row157L0 = true := by
  decide +kernel

theorem row157_e1 :
    envOK (row157P1.reverse ++ row157A.map Prod.fst) (envNext 5 row157P1) row157L1 =
      true := by
  decide +kernel

theorem row157_e2 :
    envOK (row157P2.reverse ++ row157A.map Prod.fst) (envNext 5 row157P2) row157L2 =
      true := by
  decide +kernel

theorem row157_e3 :
    envOK (row157P3.reverse ++ row157A.map Prod.fst) (envNext 5 row157P3) row157L3 =
      true := by
  decide +kernel

theorem row157_e4 :
    envOK (row157P4.reverse ++ row157A.map Prod.fst) (envNext 5 row157P4) row157L4 =
      true := by
  decide +kernel

theorem row157_e5 :
    envOK (row157P5.reverse ++ row157A.map Prod.fst) (envNext 5 row157P5) row157L5 =
      true := by
  decide +kernel

theorem row157_e6 :
    envOK (row157P6.reverse ++ row157A.map Prod.fst) (envNext 5 row157P6) row157L6 =
      true := by
  decide +kernel

theorem row157_e7 :
    envOK (row157P7.reverse ++ row157A.map Prod.fst) (envNext 5 row157P7) row157L7 =
      true := by
  decide +kernel

theorem row157_e8 :
    envOK (row157P8.reverse ++ row157A.map Prod.fst) (envNext 5 row157P8) row157L8 =
      true := by
  decide +kernel

theorem row157_e9 :
    envOK (row157P9.reverse ++ row157A.map Prod.fst) (envNext 5 row157P9) row157L9 =
      true := by
  decide +kernel

theorem row157_e10 :
    envOK (row157P10.reverse ++ row157A.map Prod.fst) (envNext 5 row157P10) row157L10 =
      true := by
  decide +kernel

theorem row157_e11 :
    envOK (row157P11.reverse ++ row157A.map Prod.fst) (envNext 5 row157P11) row157L11 =
      true := by
  decide +kernel

theorem row157_t : tailOK 157 row157L = true := by decide +kernel

/-- Receiver 157: the certificate is accepted. -/
theorem row157_ok : packRow 157 row157A row157L = true := by
  have a : absentOK 157 row157A0 = true := row157_a0
  have e : envOK (row157A.map Prod.fst) 5 row157P1 = true := row157_e0
  have e : envOK (row157A.map Prod.fst) 5 row157P2 = true :=
    envOK_of_append e row157_e1
  have e : envOK (row157A.map Prod.fst) 5 row157P3 = true :=
    envOK_of_append e row157_e2
  have e : envOK (row157A.map Prod.fst) 5 row157P4 = true :=
    envOK_of_append e row157_e3
  have e : envOK (row157A.map Prod.fst) 5 row157P5 = true :=
    envOK_of_append e row157_e4
  have e : envOK (row157A.map Prod.fst) 5 row157P6 = true :=
    envOK_of_append e row157_e5
  have e : envOK (row157A.map Prod.fst) 5 row157P7 = true :=
    envOK_of_append e row157_e6
  have e : envOK (row157A.map Prod.fst) 5 row157P8 = true :=
    envOK_of_append e row157_e7
  have e : envOK (row157A.map Prod.fst) 5 row157P9 = true :=
    envOK_of_append e row157_e8
  have e : envOK (row157A.map Prod.fst) 5 row157P10 = true :=
    envOK_of_append e row157_e9
  have e : envOK (row157A.map Prod.fst) 5 row157P11 = true :=
    envOK_of_append e row157_e10
  have e : envOK (row157A.map Prod.fst) 5 row157L = true :=
    envOK_of_append e row157_e11
  exact packRow_of_parts a e row157_t

def row163A0 : List (ℕ × List ℕ) :=
  [(5, []), (7, []), (13, []), (17, []), (19, []), (23, []), (29, []), (37, []), (41, [487]),
   (43, [3]), (53, [389306700307])]

def row163A : List (ℕ × List ℕ) := row163A0

def row163L0 : List ℕ :=
  [11, 31, 47, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139,
   149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241,
   251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359,
   367, 373, 379, 383, 389]

def row163L1 : List ℕ :=
  [397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
   509]

def row163L2 : List ℕ :=
  [521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599]

def row163L3 : List ℕ :=
  [601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673]

def row163L4 : List ℕ :=
  [677, 683, 691, 701, 709, 719, 727, 733]

def row163L5 : List ℕ :=
  [739, 743, 751, 757, 761, 769, 773, 787]

def row163L6 : List ℕ :=
  [797, 809, 811, 821, 823, 827, 829]

def row163L7 : List ℕ :=
  [839, 853, 857, 859, 863, 877]

def row163L8 : List ℕ :=
  [881, 883, 887, 907, 911, 919]

def row163L9 : List ℕ :=
  [929, 937, 941, 947, 953]

def row163L10 : List ℕ :=
  [967, 971, 977, 983, 991]

def row163L11 : List ℕ :=
  [997, 1009, 1013, 1019, 1021]

def row163L12 : List ℕ :=
  [1031, 1033, 1039, 1049, 1051]

def row163P1 : List ℕ := row163L0

def row163P2 : List ℕ := row163P1 ++ row163L1

def row163P3 : List ℕ := row163P2 ++ row163L2

def row163P4 : List ℕ := row163P3 ++ row163L3

def row163P5 : List ℕ := row163P4 ++ row163L4

def row163P6 : List ℕ := row163P5 ++ row163L5

def row163P7 : List ℕ := row163P6 ++ row163L6

def row163P8 : List ℕ := row163P7 ++ row163L7

def row163P9 : List ℕ := row163P8 ++ row163L8

def row163P10 : List ℕ := row163P9 ++ row163L9

def row163P11 : List ℕ := row163P10 ++ row163L10

def row163P12 : List ℕ := row163P11 ++ row163L11

def row163L : List ℕ := row163P12 ++ row163L12

theorem row163_a0 : absentOK 163 row163A0 = true := by decide +kernel

theorem row163_e0 : envOK (row163A.map Prod.fst) 5 row163L0 = true := by
  decide +kernel

theorem row163_e1 :
    envOK (row163P1.reverse ++ row163A.map Prod.fst) (envNext 5 row163P1) row163L1 =
      true := by
  decide +kernel

theorem row163_e2 :
    envOK (row163P2.reverse ++ row163A.map Prod.fst) (envNext 5 row163P2) row163L2 =
      true := by
  decide +kernel

theorem row163_e3 :
    envOK (row163P3.reverse ++ row163A.map Prod.fst) (envNext 5 row163P3) row163L3 =
      true := by
  decide +kernel

theorem row163_e4 :
    envOK (row163P4.reverse ++ row163A.map Prod.fst) (envNext 5 row163P4) row163L4 =
      true := by
  decide +kernel

theorem row163_e5 :
    envOK (row163P5.reverse ++ row163A.map Prod.fst) (envNext 5 row163P5) row163L5 =
      true := by
  decide +kernel

theorem row163_e6 :
    envOK (row163P6.reverse ++ row163A.map Prod.fst) (envNext 5 row163P6) row163L6 =
      true := by
  decide +kernel

theorem row163_e7 :
    envOK (row163P7.reverse ++ row163A.map Prod.fst) (envNext 5 row163P7) row163L7 =
      true := by
  decide +kernel

theorem row163_e8 :
    envOK (row163P8.reverse ++ row163A.map Prod.fst) (envNext 5 row163P8) row163L8 =
      true := by
  decide +kernel

theorem row163_e9 :
    envOK (row163P9.reverse ++ row163A.map Prod.fst) (envNext 5 row163P9) row163L9 =
      true := by
  decide +kernel

theorem row163_e10 :
    envOK (row163P10.reverse ++ row163A.map Prod.fst) (envNext 5 row163P10) row163L10 =
      true := by
  decide +kernel

theorem row163_e11 :
    envOK (row163P11.reverse ++ row163A.map Prod.fst) (envNext 5 row163P11) row163L11 =
      true := by
  decide +kernel

theorem row163_e12 :
    envOK (row163P12.reverse ++ row163A.map Prod.fst) (envNext 5 row163P12) row163L12 =
      true := by
  decide +kernel

theorem row163_t : tailOK 163 row163L = true := by decide +kernel

/-- Receiver 163: the certificate is accepted. -/
theorem row163_ok : packRow 163 row163A row163L = true := by
  have a : absentOK 163 row163A0 = true := row163_a0
  have e : envOK (row163A.map Prod.fst) 5 row163P1 = true := row163_e0
  have e : envOK (row163A.map Prod.fst) 5 row163P2 = true :=
    envOK_of_append e row163_e1
  have e : envOK (row163A.map Prod.fst) 5 row163P3 = true :=
    envOK_of_append e row163_e2
  have e : envOK (row163A.map Prod.fst) 5 row163P4 = true :=
    envOK_of_append e row163_e3
  have e : envOK (row163A.map Prod.fst) 5 row163P5 = true :=
    envOK_of_append e row163_e4
  have e : envOK (row163A.map Prod.fst) 5 row163P6 = true :=
    envOK_of_append e row163_e5
  have e : envOK (row163A.map Prod.fst) 5 row163P7 = true :=
    envOK_of_append e row163_e6
  have e : envOK (row163A.map Prod.fst) 5 row163P8 = true :=
    envOK_of_append e row163_e7
  have e : envOK (row163A.map Prod.fst) 5 row163P9 = true :=
    envOK_of_append e row163_e8
  have e : envOK (row163A.map Prod.fst) 5 row163P10 = true :=
    envOK_of_append e row163_e9
  have e : envOK (row163A.map Prod.fst) 5 row163P11 = true :=
    envOK_of_append e row163_e10
  have e : envOK (row163A.map Prod.fst) 5 row163P12 = true :=
    envOK_of_append e row163_e11
  have e : envOK (row163A.map Prod.fst) 5 row163L = true :=
    envOK_of_append e row163_e12
  exact packRow_of_parts a e row163_t

end ReceiverPack
end OddPerfect

#print axioms OddPerfect.ReceiverPack.row157_a0
#print axioms OddPerfect.ReceiverPack.row157_e0
#print axioms OddPerfect.ReceiverPack.row157_e1
#print axioms OddPerfect.ReceiverPack.row157_e2
#print axioms OddPerfect.ReceiverPack.row157_e3
#print axioms OddPerfect.ReceiverPack.row157_e4
#print axioms OddPerfect.ReceiverPack.row157_e5
#print axioms OddPerfect.ReceiverPack.row157_e6
#print axioms OddPerfect.ReceiverPack.row157_e7
#print axioms OddPerfect.ReceiverPack.row157_e8
#print axioms OddPerfect.ReceiverPack.row157_e9
#print axioms OddPerfect.ReceiverPack.row157_e10
#print axioms OddPerfect.ReceiverPack.row157_e11
#print axioms OddPerfect.ReceiverPack.row157_t
#print axioms OddPerfect.ReceiverPack.row157_ok
#print axioms OddPerfect.ReceiverPack.row163_a0
#print axioms OddPerfect.ReceiverPack.row163_e0
#print axioms OddPerfect.ReceiverPack.row163_e1
#print axioms OddPerfect.ReceiverPack.row163_e2
#print axioms OddPerfect.ReceiverPack.row163_e3
#print axioms OddPerfect.ReceiverPack.row163_e4
#print axioms OddPerfect.ReceiverPack.row163_e5
#print axioms OddPerfect.ReceiverPack.row163_e6
#print axioms OddPerfect.ReceiverPack.row163_e7
#print axioms OddPerfect.ReceiverPack.row163_e8
#print axioms OddPerfect.ReceiverPack.row163_e9
#print axioms OddPerfect.ReceiverPack.row163_e10
#print axioms OddPerfect.ReceiverPack.row163_e11
#print axioms OddPerfect.ReceiverPack.row163_e12
#print axioms OddPerfect.ReceiverPack.row163_t
#print axioms OddPerfect.ReceiverPack.row163_ok
