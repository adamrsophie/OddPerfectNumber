import OddPerfect.EulerIndexPairReceiverCore

/-!
# Two prime Euler index, branch `v = 1`: receiver certificates 167 to 167

Restricted result; no published source was checked; novelty not verified. The odd perfect
number conjecture remains open.

For each prime receiver `u` with `167 ≤ u ≤ 167`, a certificate `(A, L)` accepted by
`ReceiverSieve.packRow` (kernel evaluation): the absent primes `A` with their divisor lists, and
the envelope `L`. The set of kept pure row lengths is computed by the checker from `u`. Each
receiver needs its own finite certificate; no uniform statement over all receivers is proved.
-/

namespace OddPerfect
namespace ReceiverPack

open ReceiverSieve

def row167A0 : List (ℕ × List ℕ) :=
  [(5, []), (7, [66733]), (11, [12119]), (13, []), (17, []), (29, [gsum 83 29 / 167 ^ 1]),
   (47, [gsum 83 47 / 167 ^ 1]), (53, []), (59, []), (71, []), (73, []), (83, [])]

def row167A : List (ℕ × List ℕ) := row167A0

def row167L0 : List ℕ :=
  [19, 23, 31, 37, 41, 43, 61, 67, 79, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149,
   151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
   257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367,
   373, 379, 383, 389]

def row167L1 : List ℕ :=
  [397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
   509]

def row167L2 : List ℕ :=
  [521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599]

def row167L3 : List ℕ :=
  [601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673]

def row167L4 : List ℕ :=
  [677, 683, 691, 701, 709, 719, 727, 733]

def row167L5 : List ℕ :=
  [739, 743, 751, 757, 761, 769, 773, 787]

def row167L6 : List ℕ :=
  [797, 809, 811, 821, 823, 827, 829]

def row167L7 : List ℕ :=
  [839, 853, 857, 859, 863, 877]

def row167L8 : List ℕ :=
  [881, 883, 887, 907, 911, 919]

def row167L9 : List ℕ :=
  [929, 937, 941, 947, 953]

def row167L10 : List ℕ :=
  [967, 971, 977, 983, 991]

def row167L11 : List ℕ :=
  [997, 1009, 1013, 1019, 1021]

def row167L12 : List ℕ :=
  [1031, 1033, 1039, 1049, 1051]

def row167L13 : List ℕ :=
  [1061, 1063, 1069]

def row167L14 : List ℕ :=
  [1087, 1091, 1093]

def row167P1 : List ℕ := row167L0

def row167P2 : List ℕ := row167P1 ++ row167L1

def row167P3 : List ℕ := row167P2 ++ row167L2

def row167P4 : List ℕ := row167P3 ++ row167L3

def row167P5 : List ℕ := row167P4 ++ row167L4

def row167P6 : List ℕ := row167P5 ++ row167L5

def row167P7 : List ℕ := row167P6 ++ row167L6

def row167P8 : List ℕ := row167P7 ++ row167L7

def row167P9 : List ℕ := row167P8 ++ row167L8

def row167P10 : List ℕ := row167P9 ++ row167L9

def row167P11 : List ℕ := row167P10 ++ row167L10

def row167P12 : List ℕ := row167P11 ++ row167L11

def row167P13 : List ℕ := row167P12 ++ row167L12

def row167P14 : List ℕ := row167P13 ++ row167L13

def row167L : List ℕ := row167P14 ++ row167L14

theorem row167_a0 : absentOK 167 row167A0 = true := by decide +kernel

theorem row167_e0 : envOK (row167A.map Prod.fst) 5 row167L0 = true := by
  decide +kernel

theorem row167_e1 :
    envOK (row167P1.reverse ++ row167A.map Prod.fst) (envNext 5 row167P1) row167L1 =
      true := by
  decide +kernel

theorem row167_e2 :
    envOK (row167P2.reverse ++ row167A.map Prod.fst) (envNext 5 row167P2) row167L2 =
      true := by
  decide +kernel

theorem row167_e3 :
    envOK (row167P3.reverse ++ row167A.map Prod.fst) (envNext 5 row167P3) row167L3 =
      true := by
  decide +kernel

theorem row167_e4 :
    envOK (row167P4.reverse ++ row167A.map Prod.fst) (envNext 5 row167P4) row167L4 =
      true := by
  decide +kernel

theorem row167_e5 :
    envOK (row167P5.reverse ++ row167A.map Prod.fst) (envNext 5 row167P5) row167L5 =
      true := by
  decide +kernel

theorem row167_e6 :
    envOK (row167P6.reverse ++ row167A.map Prod.fst) (envNext 5 row167P6) row167L6 =
      true := by
  decide +kernel

theorem row167_e7 :
    envOK (row167P7.reverse ++ row167A.map Prod.fst) (envNext 5 row167P7) row167L7 =
      true := by
  decide +kernel

theorem row167_e8 :
    envOK (row167P8.reverse ++ row167A.map Prod.fst) (envNext 5 row167P8) row167L8 =
      true := by
  decide +kernel

theorem row167_e9 :
    envOK (row167P9.reverse ++ row167A.map Prod.fst) (envNext 5 row167P9) row167L9 =
      true := by
  decide +kernel

theorem row167_e10 :
    envOK (row167P10.reverse ++ row167A.map Prod.fst) (envNext 5 row167P10) row167L10 =
      true := by
  decide +kernel

theorem row167_e11 :
    envOK (row167P11.reverse ++ row167A.map Prod.fst) (envNext 5 row167P11) row167L11 =
      true := by
  decide +kernel

theorem row167_e12 :
    envOK (row167P12.reverse ++ row167A.map Prod.fst) (envNext 5 row167P12) row167L12 =
      true := by
  decide +kernel

theorem row167_e13 :
    envOK (row167P13.reverse ++ row167A.map Prod.fst) (envNext 5 row167P13) row167L13 =
      true := by
  decide +kernel

theorem row167_e14 :
    envOK (row167P14.reverse ++ row167A.map Prod.fst) (envNext 5 row167P14) row167L14 =
      true := by
  decide +kernel

theorem row167_t : tailOK 167 row167L = true := by decide +kernel

/-- Receiver 167: the certificate is accepted. -/
theorem row167_ok : packRow 167 row167A row167L = true := by
  have a : absentOK 167 row167A0 = true := row167_a0
  have e : envOK (row167A.map Prod.fst) 5 row167P1 = true := row167_e0
  have e : envOK (row167A.map Prod.fst) 5 row167P2 = true :=
    envOK_of_append e row167_e1
  have e : envOK (row167A.map Prod.fst) 5 row167P3 = true :=
    envOK_of_append e row167_e2
  have e : envOK (row167A.map Prod.fst) 5 row167P4 = true :=
    envOK_of_append e row167_e3
  have e : envOK (row167A.map Prod.fst) 5 row167P5 = true :=
    envOK_of_append e row167_e4
  have e : envOK (row167A.map Prod.fst) 5 row167P6 = true :=
    envOK_of_append e row167_e5
  have e : envOK (row167A.map Prod.fst) 5 row167P7 = true :=
    envOK_of_append e row167_e6
  have e : envOK (row167A.map Prod.fst) 5 row167P8 = true :=
    envOK_of_append e row167_e7
  have e : envOK (row167A.map Prod.fst) 5 row167P9 = true :=
    envOK_of_append e row167_e8
  have e : envOK (row167A.map Prod.fst) 5 row167P10 = true :=
    envOK_of_append e row167_e9
  have e : envOK (row167A.map Prod.fst) 5 row167P11 = true :=
    envOK_of_append e row167_e10
  have e : envOK (row167A.map Prod.fst) 5 row167P12 = true :=
    envOK_of_append e row167_e11
  have e : envOK (row167A.map Prod.fst) 5 row167P13 = true :=
    envOK_of_append e row167_e12
  have e : envOK (row167A.map Prod.fst) 5 row167P14 = true :=
    envOK_of_append e row167_e13
  have e : envOK (row167A.map Prod.fst) 5 row167L = true :=
    envOK_of_append e row167_e14
  exact packRow_of_parts a e row167_t

end ReceiverPack
end OddPerfect

#print axioms OddPerfect.ReceiverPack.row167_a0
#print axioms OddPerfect.ReceiverPack.row167_e0
#print axioms OddPerfect.ReceiverPack.row167_e1
#print axioms OddPerfect.ReceiverPack.row167_e2
#print axioms OddPerfect.ReceiverPack.row167_e3
#print axioms OddPerfect.ReceiverPack.row167_e4
#print axioms OddPerfect.ReceiverPack.row167_e5
#print axioms OddPerfect.ReceiverPack.row167_e6
#print axioms OddPerfect.ReceiverPack.row167_e7
#print axioms OddPerfect.ReceiverPack.row167_e8
#print axioms OddPerfect.ReceiverPack.row167_e9
#print axioms OddPerfect.ReceiverPack.row167_e10
#print axioms OddPerfect.ReceiverPack.row167_e11
#print axioms OddPerfect.ReceiverPack.row167_e12
#print axioms OddPerfect.ReceiverPack.row167_e13
#print axioms OddPerfect.ReceiverPack.row167_e14
#print axioms OddPerfect.ReceiverPack.row167_t
#print axioms OddPerfect.ReceiverPack.row167_ok
