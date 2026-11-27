import OddPerfect.EulerIndexPairReceiverCore

/-!
# Two prime Euler index, branch `v = 1`: receiver certificates 149 to 151

Restricted result; no published source was checked; novelty not verified. The odd perfect
number conjecture remains open.

For each prime receiver `u` with `149 ≤ u ≤ 151`, a certificate `(A, L)` accepted by
`ReceiverSieve.packRow` (kernel evaluation): the absent primes `A` with their divisor lists, and
the envelope `L`. The set of kept pure row lengths is computed by the checker from `u`. Each
receiver needs its own finite certificate; no uniform statement over all receivers is proved.
-/

namespace OddPerfect
namespace ReceiverPack

open ReceiverSieve

def row149A0 : List (ℕ × List ℕ) :=
  [(5, [122079825741332649384569]), (11, []), (13, []), (17, [223]),
   (19, [gsum 37 19 / 149 ^ 1]), (23, []), (37, [1999]), (41, []), (43, []), (53, []), (61, []),
   (67, [gsum 37 67 / 149 ^ 1]), (71, []), (73, [20129]), (89, [])]

def row149A : List (ℕ × List ℕ) := row149A0

def row149L0 : List ℕ :=
  [7, 29, 31, 47, 59, 79, 83, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157,
   163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263,
   269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379,
   383, 389]

def row149L1 : List ℕ :=
  [397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
   509]

def row149L2 : List ℕ :=
  [521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599]

def row149L3 : List ℕ :=
  [601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673]

def row149L4 : List ℕ :=
  [677, 683, 691, 701, 709, 719, 727, 733]

def row149L5 : List ℕ :=
  [739, 743, 751, 757, 761, 769, 773, 787]

def row149L6 : List ℕ :=
  [797, 809, 811, 821, 823, 827, 829]

def row149L7 : List ℕ :=
  [839, 853, 857, 859, 863, 877]

def row149L8 : List ℕ :=
  [881, 883, 887, 907, 911, 919]

def row149L9 : List ℕ :=
  [929, 937, 941, 947, 953]

def row149L10 : List ℕ :=
  [967, 971, 977, 983, 991]

def row149L11 : List ℕ :=
  [997]

def row149P1 : List ℕ := row149L0

def row149P2 : List ℕ := row149P1 ++ row149L1

def row149P3 : List ℕ := row149P2 ++ row149L2

def row149P4 : List ℕ := row149P3 ++ row149L3

def row149P5 : List ℕ := row149P4 ++ row149L4

def row149P6 : List ℕ := row149P5 ++ row149L5

def row149P7 : List ℕ := row149P6 ++ row149L6

def row149P8 : List ℕ := row149P7 ++ row149L7

def row149P9 : List ℕ := row149P8 ++ row149L8

def row149P10 : List ℕ := row149P9 ++ row149L9

def row149P11 : List ℕ := row149P10 ++ row149L10

def row149L : List ℕ := row149P11 ++ row149L11

theorem row149_a0 : absentOK 149 row149A0 = true := by decide +kernel

theorem row149_e0 : envOK (row149A.map Prod.fst) 5 row149L0 = true := by
  decide +kernel

theorem row149_e1 :
    envOK (row149P1.reverse ++ row149A.map Prod.fst) (envNext 5 row149P1) row149L1 =
      true := by
  decide +kernel

theorem row149_e2 :
    envOK (row149P2.reverse ++ row149A.map Prod.fst) (envNext 5 row149P2) row149L2 =
      true := by
  decide +kernel

theorem row149_e3 :
    envOK (row149P3.reverse ++ row149A.map Prod.fst) (envNext 5 row149P3) row149L3 =
      true := by
  decide +kernel

theorem row149_e4 :
    envOK (row149P4.reverse ++ row149A.map Prod.fst) (envNext 5 row149P4) row149L4 =
      true := by
  decide +kernel

theorem row149_e5 :
    envOK (row149P5.reverse ++ row149A.map Prod.fst) (envNext 5 row149P5) row149L5 =
      true := by
  decide +kernel

theorem row149_e6 :
    envOK (row149P6.reverse ++ row149A.map Prod.fst) (envNext 5 row149P6) row149L6 =
      true := by
  decide +kernel

theorem row149_e7 :
    envOK (row149P7.reverse ++ row149A.map Prod.fst) (envNext 5 row149P7) row149L7 =
      true := by
  decide +kernel

theorem row149_e8 :
    envOK (row149P8.reverse ++ row149A.map Prod.fst) (envNext 5 row149P8) row149L8 =
      true := by
  decide +kernel

theorem row149_e9 :
    envOK (row149P9.reverse ++ row149A.map Prod.fst) (envNext 5 row149P9) row149L9 =
      true := by
  decide +kernel

theorem row149_e10 :
    envOK (row149P10.reverse ++ row149A.map Prod.fst) (envNext 5 row149P10) row149L10 =
      true := by
  decide +kernel

theorem row149_e11 :
    envOK (row149P11.reverse ++ row149A.map Prod.fst) (envNext 5 row149P11) row149L11 =
      true := by
  decide +kernel

theorem row149_t : tailOK 149 row149L = true := by decide +kernel

/-- Receiver 149: the certificate is accepted. -/
theorem row149_ok : packRow 149 row149A row149L = true := by
  have a : absentOK 149 row149A0 = true := row149_a0
  have e : envOK (row149A.map Prod.fst) 5 row149P1 = true := row149_e0
  have e : envOK (row149A.map Prod.fst) 5 row149P2 = true :=
    envOK_of_append e row149_e1
  have e : envOK (row149A.map Prod.fst) 5 row149P3 = true :=
    envOK_of_append e row149_e2
  have e : envOK (row149A.map Prod.fst) 5 row149P4 = true :=
    envOK_of_append e row149_e3
  have e : envOK (row149A.map Prod.fst) 5 row149P5 = true :=
    envOK_of_append e row149_e4
  have e : envOK (row149A.map Prod.fst) 5 row149P6 = true :=
    envOK_of_append e row149_e5
  have e : envOK (row149A.map Prod.fst) 5 row149P7 = true :=
    envOK_of_append e row149_e6
  have e : envOK (row149A.map Prod.fst) 5 row149P8 = true :=
    envOK_of_append e row149_e7
  have e : envOK (row149A.map Prod.fst) 5 row149P9 = true :=
    envOK_of_append e row149_e8
  have e : envOK (row149A.map Prod.fst) 5 row149P10 = true :=
    envOK_of_append e row149_e9
  have e : envOK (row149A.map Prod.fst) 5 row149P11 = true :=
    envOK_of_append e row149_e10
  have e : envOK (row149A.map Prod.fst) 5 row149L = true :=
    envOK_of_append e row149_e11
  exact packRow_of_parts a e row149_t

def row151A0 : List (ℕ × List ℕ) :=
  [(5, [11]), (7, []), (11, [5]), (13, []), (17, [307]), (23, []), (31, [3]), (37, [3])]

def row151A : List (ℕ × List ℕ) := row151A0

def row151L0 : List ℕ :=
  [19, 29, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
   137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
   239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349,
   353, 359, 367, 373, 379, 383, 389]

def row151L1 : List ℕ :=
  [397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
   509]

def row151L2 : List ℕ :=
  [521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599]

def row151L3 : List ℕ :=
  [601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673]

def row151L4 : List ℕ :=
  [677, 683, 691, 701, 709, 719, 727, 733]

def row151L5 : List ℕ :=
  [739, 743, 751, 757, 761, 769, 773, 787]

def row151L6 : List ℕ :=
  [797, 809, 811, 821, 823, 827, 829]

def row151L7 : List ℕ :=
  [839, 853, 857, 859, 863, 877]

def row151L8 : List ℕ :=
  [881, 883, 887, 907, 911, 919]

def row151L9 : List ℕ :=
  [929, 937, 941, 947, 953]

def row151P1 : List ℕ := row151L0

def row151P2 : List ℕ := row151P1 ++ row151L1

def row151P3 : List ℕ := row151P2 ++ row151L2

def row151P4 : List ℕ := row151P3 ++ row151L3

def row151P5 : List ℕ := row151P4 ++ row151L4

def row151P6 : List ℕ := row151P5 ++ row151L5

def row151P7 : List ℕ := row151P6 ++ row151L6

def row151P8 : List ℕ := row151P7 ++ row151L7

def row151P9 : List ℕ := row151P8 ++ row151L8

def row151L : List ℕ := row151P9 ++ row151L9

theorem row151_a0 : absentOK 151 row151A0 = true := by decide +kernel

theorem row151_e0 : envOK (row151A.map Prod.fst) 5 row151L0 = true := by
  decide +kernel

theorem row151_e1 :
    envOK (row151P1.reverse ++ row151A.map Prod.fst) (envNext 5 row151P1) row151L1 =
      true := by
  decide +kernel

theorem row151_e2 :
    envOK (row151P2.reverse ++ row151A.map Prod.fst) (envNext 5 row151P2) row151L2 =
      true := by
  decide +kernel

theorem row151_e3 :
    envOK (row151P3.reverse ++ row151A.map Prod.fst) (envNext 5 row151P3) row151L3 =
      true := by
  decide +kernel

theorem row151_e4 :
    envOK (row151P4.reverse ++ row151A.map Prod.fst) (envNext 5 row151P4) row151L4 =
      true := by
  decide +kernel

theorem row151_e5 :
    envOK (row151P5.reverse ++ row151A.map Prod.fst) (envNext 5 row151P5) row151L5 =
      true := by
  decide +kernel

theorem row151_e6 :
    envOK (row151P6.reverse ++ row151A.map Prod.fst) (envNext 5 row151P6) row151L6 =
      true := by
  decide +kernel

theorem row151_e7 :
    envOK (row151P7.reverse ++ row151A.map Prod.fst) (envNext 5 row151P7) row151L7 =
      true := by
  decide +kernel

theorem row151_e8 :
    envOK (row151P8.reverse ++ row151A.map Prod.fst) (envNext 5 row151P8) row151L8 =
      true := by
  decide +kernel

theorem row151_e9 :
    envOK (row151P9.reverse ++ row151A.map Prod.fst) (envNext 5 row151P9) row151L9 =
      true := by
  decide +kernel

theorem row151_t : tailOK 151 row151L = true := by decide +kernel

/-- Receiver 151: the certificate is accepted. -/
theorem row151_ok : packRow 151 row151A row151L = true := by
  have a : absentOK 151 row151A0 = true := row151_a0
  have e : envOK (row151A.map Prod.fst) 5 row151P1 = true := row151_e0
  have e : envOK (row151A.map Prod.fst) 5 row151P2 = true :=
    envOK_of_append e row151_e1
  have e : envOK (row151A.map Prod.fst) 5 row151P3 = true :=
    envOK_of_append e row151_e2
  have e : envOK (row151A.map Prod.fst) 5 row151P4 = true :=
    envOK_of_append e row151_e3
  have e : envOK (row151A.map Prod.fst) 5 row151P5 = true :=
    envOK_of_append e row151_e4
  have e : envOK (row151A.map Prod.fst) 5 row151P6 = true :=
    envOK_of_append e row151_e5
  have e : envOK (row151A.map Prod.fst) 5 row151P7 = true :=
    envOK_of_append e row151_e6
  have e : envOK (row151A.map Prod.fst) 5 row151P8 = true :=
    envOK_of_append e row151_e7
  have e : envOK (row151A.map Prod.fst) 5 row151P9 = true :=
    envOK_of_append e row151_e8
  have e : envOK (row151A.map Prod.fst) 5 row151L = true :=
    envOK_of_append e row151_e9
  exact packRow_of_parts a e row151_t

end ReceiverPack
end OddPerfect

#print axioms OddPerfect.ReceiverPack.row149_a0
#print axioms OddPerfect.ReceiverPack.row149_e0
#print axioms OddPerfect.ReceiverPack.row149_e1
#print axioms OddPerfect.ReceiverPack.row149_e2
#print axioms OddPerfect.ReceiverPack.row149_e3
#print axioms OddPerfect.ReceiverPack.row149_e4
#print axioms OddPerfect.ReceiverPack.row149_e5
#print axioms OddPerfect.ReceiverPack.row149_e6
#print axioms OddPerfect.ReceiverPack.row149_e7
#print axioms OddPerfect.ReceiverPack.row149_e8
#print axioms OddPerfect.ReceiverPack.row149_e9
#print axioms OddPerfect.ReceiverPack.row149_e10
#print axioms OddPerfect.ReceiverPack.row149_e11
#print axioms OddPerfect.ReceiverPack.row149_t
#print axioms OddPerfect.ReceiverPack.row149_ok
#print axioms OddPerfect.ReceiverPack.row151_a0
#print axioms OddPerfect.ReceiverPack.row151_e0
#print axioms OddPerfect.ReceiverPack.row151_e1
#print axioms OddPerfect.ReceiverPack.row151_e2
#print axioms OddPerfect.ReceiverPack.row151_e3
#print axioms OddPerfect.ReceiverPack.row151_e4
#print axioms OddPerfect.ReceiverPack.row151_e5
#print axioms OddPerfect.ReceiverPack.row151_e6
#print axioms OddPerfect.ReceiverPack.row151_e7
#print axioms OddPerfect.ReceiverPack.row151_e8
#print axioms OddPerfect.ReceiverPack.row151_e9
#print axioms OddPerfect.ReceiverPack.row151_t
#print axioms OddPerfect.ReceiverPack.row151_ok
