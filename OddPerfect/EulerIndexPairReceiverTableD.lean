import OddPerfect.EulerIndexPairReceiverCore

/-!
# Two prime Euler index, branch `v = 1`: receiver certificates 137 to 139

Restricted result; no published source was checked; novelty not verified. The odd perfect
number conjecture remains open.

For each prime receiver `u` with `137 ≤ u ≤ 139`, a certificate `(A, L)` accepted by
`ReceiverSieve.packRow` (kernel evaluation): the absent primes `A` with their divisor lists, and
the envelope `L`. The set of kept pure row lengths is computed by the checker from `u`. Each
receiver needs its own finite certificate; no uniform statement over all receivers is proved.
-/

namespace OddPerfect
namespace ReceiverPack

open ReceiverSieve

def row137A0 : List (ℕ × List ℕ) :=
  [(5, []), (13, []), (17, []), (19, []), (23, []), (29, []), (31, []), (41, []), (47, []),
   (53, []), (59, [443]), (61, []), (67, []), (71, []), (79, []), (89, []), (97, []), (101, []),
   (107, [])]

def row137A1 : List (ℕ × List ℕ) :=
  [(113, [])]

def row137A : List (ℕ × List ℕ) :=
  row137A0 ++ row137A1

def row137L0 : List ℕ :=
  [7, 11, 37, 43, 73, 83, 103, 109, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
   191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283,
   293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389]

def row137L1 : List ℕ :=
  [397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
   509]

def row137L2 : List ℕ :=
  [521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599]

def row137L3 : List ℕ :=
  [601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673]

def row137L4 : List ℕ :=
  [677, 683, 691, 701, 709, 719, 727, 733]

def row137L5 : List ℕ :=
  [739, 743, 751, 757, 761, 769, 773, 787]

def row137L6 : List ℕ :=
  [797, 809, 811, 821, 823, 827, 829]

def row137L7 : List ℕ :=
  [839, 853, 857, 859, 863, 877]

def row137L8 : List ℕ :=
  [881, 883, 887, 907, 911, 919]

def row137L9 : List ℕ :=
  [929, 937, 941, 947]

def row137P1 : List ℕ := row137L0

def row137P2 : List ℕ := row137P1 ++ row137L1

def row137P3 : List ℕ := row137P2 ++ row137L2

def row137P4 : List ℕ := row137P3 ++ row137L3

def row137P5 : List ℕ := row137P4 ++ row137L4

def row137P6 : List ℕ := row137P5 ++ row137L5

def row137P7 : List ℕ := row137P6 ++ row137L6

def row137P8 : List ℕ := row137P7 ++ row137L7

def row137P9 : List ℕ := row137P8 ++ row137L8

def row137L : List ℕ := row137P9 ++ row137L9

theorem row137_a0 : absentOK 137 row137A0 = true := by decide +kernel

theorem row137_a1 : absentOK 137 row137A1 = true := by decide +kernel

theorem row137_e0 : envOK (row137A.map Prod.fst) 5 row137L0 = true := by
  decide +kernel

theorem row137_e1 :
    envOK (row137P1.reverse ++ row137A.map Prod.fst) (envNext 5 row137P1) row137L1 =
      true := by
  decide +kernel

theorem row137_e2 :
    envOK (row137P2.reverse ++ row137A.map Prod.fst) (envNext 5 row137P2) row137L2 =
      true := by
  decide +kernel

theorem row137_e3 :
    envOK (row137P3.reverse ++ row137A.map Prod.fst) (envNext 5 row137P3) row137L3 =
      true := by
  decide +kernel

theorem row137_e4 :
    envOK (row137P4.reverse ++ row137A.map Prod.fst) (envNext 5 row137P4) row137L4 =
      true := by
  decide +kernel

theorem row137_e5 :
    envOK (row137P5.reverse ++ row137A.map Prod.fst) (envNext 5 row137P5) row137L5 =
      true := by
  decide +kernel

theorem row137_e6 :
    envOK (row137P6.reverse ++ row137A.map Prod.fst) (envNext 5 row137P6) row137L6 =
      true := by
  decide +kernel

theorem row137_e7 :
    envOK (row137P7.reverse ++ row137A.map Prod.fst) (envNext 5 row137P7) row137L7 =
      true := by
  decide +kernel

theorem row137_e8 :
    envOK (row137P8.reverse ++ row137A.map Prod.fst) (envNext 5 row137P8) row137L8 =
      true := by
  decide +kernel

theorem row137_e9 :
    envOK (row137P9.reverse ++ row137A.map Prod.fst) (envNext 5 row137P9) row137L9 =
      true := by
  decide +kernel

theorem row137_t : tailOK 137 row137L = true := by decide +kernel

/-- Receiver 137: the certificate is accepted. -/
theorem row137_ok : packRow 137 row137A row137L = true := by
  have a : absentOK 137 row137A0 = true := row137_a0
  have a : absentOK 137 (row137A0 ++ row137A1) = true :=
    absentOK_append a row137_a1
  have e : envOK (row137A.map Prod.fst) 5 row137P1 = true := row137_e0
  have e : envOK (row137A.map Prod.fst) 5 row137P2 = true :=
    envOK_of_append e row137_e1
  have e : envOK (row137A.map Prod.fst) 5 row137P3 = true :=
    envOK_of_append e row137_e2
  have e : envOK (row137A.map Prod.fst) 5 row137P4 = true :=
    envOK_of_append e row137_e3
  have e : envOK (row137A.map Prod.fst) 5 row137P5 = true :=
    envOK_of_append e row137_e4
  have e : envOK (row137A.map Prod.fst) 5 row137P6 = true :=
    envOK_of_append e row137_e5
  have e : envOK (row137A.map Prod.fst) 5 row137P7 = true :=
    envOK_of_append e row137_e6
  have e : envOK (row137A.map Prod.fst) 5 row137P8 = true :=
    envOK_of_append e row137_e7
  have e : envOK (row137A.map Prod.fst) 5 row137P9 = true :=
    envOK_of_append e row137_e8
  have e : envOK (row137A.map Prod.fst) 5 row137L = true :=
    envOK_of_append e row137_e9
  exact packRow_of_parts a e row137_t

def row139A0 : List (ℕ × List ℕ) :=
  [(5, [31]), (11, [7]), (13, [3]), (17, []), (19, []), (23, []), (31, [3]), (37, [3]),
   (47, [23]), (59, []), (61, []), (71, [47]), (73, []), (89, [47])]

def row139A : List (ℕ × List ℕ) := row139A0

def row139L0 : List ℕ :=
  [7, 29, 41, 43, 53, 67, 79, 83, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157,
   163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263,
   269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379,
   383, 389]

def row139L1 : List ℕ :=
  [397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
   509]

def row139L2 : List ℕ :=
  [521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599]

def row139L3 : List ℕ :=
  [601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673]

def row139L4 : List ℕ :=
  [677, 683, 691, 701, 709, 719, 727, 733]

def row139L5 : List ℕ :=
  [739, 743, 751, 757, 761, 769, 773, 787]

def row139L6 : List ℕ :=
  [797, 809, 811, 821, 823, 827, 829]

def row139L7 : List ℕ :=
  [839, 853, 857, 859, 863, 877]

def row139L8 : List ℕ :=
  [881, 883, 887, 907, 911, 919]

def row139P1 : List ℕ := row139L0

def row139P2 : List ℕ := row139P1 ++ row139L1

def row139P3 : List ℕ := row139P2 ++ row139L2

def row139P4 : List ℕ := row139P3 ++ row139L3

def row139P5 : List ℕ := row139P4 ++ row139L4

def row139P6 : List ℕ := row139P5 ++ row139L5

def row139P7 : List ℕ := row139P6 ++ row139L6

def row139P8 : List ℕ := row139P7 ++ row139L7

def row139L : List ℕ := row139P8 ++ row139L8

theorem row139_a0 : absentOK 139 row139A0 = true := by decide +kernel

theorem row139_e0 : envOK (row139A.map Prod.fst) 5 row139L0 = true := by
  decide +kernel

theorem row139_e1 :
    envOK (row139P1.reverse ++ row139A.map Prod.fst) (envNext 5 row139P1) row139L1 =
      true := by
  decide +kernel

theorem row139_e2 :
    envOK (row139P2.reverse ++ row139A.map Prod.fst) (envNext 5 row139P2) row139L2 =
      true := by
  decide +kernel

theorem row139_e3 :
    envOK (row139P3.reverse ++ row139A.map Prod.fst) (envNext 5 row139P3) row139L3 =
      true := by
  decide +kernel

theorem row139_e4 :
    envOK (row139P4.reverse ++ row139A.map Prod.fst) (envNext 5 row139P4) row139L4 =
      true := by
  decide +kernel

theorem row139_e5 :
    envOK (row139P5.reverse ++ row139A.map Prod.fst) (envNext 5 row139P5) row139L5 =
      true := by
  decide +kernel

theorem row139_e6 :
    envOK (row139P6.reverse ++ row139A.map Prod.fst) (envNext 5 row139P6) row139L6 =
      true := by
  decide +kernel

theorem row139_e7 :
    envOK (row139P7.reverse ++ row139A.map Prod.fst) (envNext 5 row139P7) row139L7 =
      true := by
  decide +kernel

theorem row139_e8 :
    envOK (row139P8.reverse ++ row139A.map Prod.fst) (envNext 5 row139P8) row139L8 =
      true := by
  decide +kernel

theorem row139_t : tailOK 139 row139L = true := by decide +kernel

/-- Receiver 139: the certificate is accepted. -/
theorem row139_ok : packRow 139 row139A row139L = true := by
  have a : absentOK 139 row139A0 = true := row139_a0
  have e : envOK (row139A.map Prod.fst) 5 row139P1 = true := row139_e0
  have e : envOK (row139A.map Prod.fst) 5 row139P2 = true :=
    envOK_of_append e row139_e1
  have e : envOK (row139A.map Prod.fst) 5 row139P3 = true :=
    envOK_of_append e row139_e2
  have e : envOK (row139A.map Prod.fst) 5 row139P4 = true :=
    envOK_of_append e row139_e3
  have e : envOK (row139A.map Prod.fst) 5 row139P5 = true :=
    envOK_of_append e row139_e4
  have e : envOK (row139A.map Prod.fst) 5 row139P6 = true :=
    envOK_of_append e row139_e5
  have e : envOK (row139A.map Prod.fst) 5 row139P7 = true :=
    envOK_of_append e row139_e6
  have e : envOK (row139A.map Prod.fst) 5 row139P8 = true :=
    envOK_of_append e row139_e7
  have e : envOK (row139A.map Prod.fst) 5 row139L = true :=
    envOK_of_append e row139_e8
  exact packRow_of_parts a e row139_t

end ReceiverPack
end OddPerfect

#print axioms OddPerfect.ReceiverPack.row137_a0
#print axioms OddPerfect.ReceiverPack.row137_a1
#print axioms OddPerfect.ReceiverPack.row137_e0
#print axioms OddPerfect.ReceiverPack.row137_e1
#print axioms OddPerfect.ReceiverPack.row137_e2
#print axioms OddPerfect.ReceiverPack.row137_e3
#print axioms OddPerfect.ReceiverPack.row137_e4
#print axioms OddPerfect.ReceiverPack.row137_e5
#print axioms OddPerfect.ReceiverPack.row137_e6
#print axioms OddPerfect.ReceiverPack.row137_e7
#print axioms OddPerfect.ReceiverPack.row137_e8
#print axioms OddPerfect.ReceiverPack.row137_e9
#print axioms OddPerfect.ReceiverPack.row137_t
#print axioms OddPerfect.ReceiverPack.row137_ok
#print axioms OddPerfect.ReceiverPack.row139_a0
#print axioms OddPerfect.ReceiverPack.row139_e0
#print axioms OddPerfect.ReceiverPack.row139_e1
#print axioms OddPerfect.ReceiverPack.row139_e2
#print axioms OddPerfect.ReceiverPack.row139_e3
#print axioms OddPerfect.ReceiverPack.row139_e4
#print axioms OddPerfect.ReceiverPack.row139_e5
#print axioms OddPerfect.ReceiverPack.row139_e6
#print axioms OddPerfect.ReceiverPack.row139_e7
#print axioms OddPerfect.ReceiverPack.row139_e8
#print axioms OddPerfect.ReceiverPack.row139_t
#print axioms OddPerfect.ReceiverPack.row139_ok
