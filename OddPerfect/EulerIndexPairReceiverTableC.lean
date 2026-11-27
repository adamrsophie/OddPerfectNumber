import OddPerfect.EulerIndexPairReceiverCore

/-!
# Two prime Euler index, branch `v = 1`: receiver certificates 109 to 131

Restricted result; no published source was checked; novelty not verified. The odd perfect
number conjecture remains open.

For each prime receiver `u` with `109 ≤ u ≤ 131`, a certificate `(A, L)` accepted by
`ReceiverSieve.packRow` (kernel evaluation): the absent primes `A` with their divisor lists, and
the envelope `L`. The set of kept pure row lengths is computed by the checker from `u`. Each
receiver needs its own finite certificate; no uniform statement over all receivers is proved.
-/

namespace OddPerfect
namespace ReceiverPack

open ReceiverSieve

def row109A0 : List (ℕ × List ℕ) :=
  [(5, [19]), (7, [3]), (11, []), (13, []), (17, []), (19, [])]

def row109A : List (ℕ × List ℕ) := row109A0

def row109L0 : List ℕ :=
  [23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
   127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227,
   229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337,
   347, 349, 353, 359, 367, 373, 379, 383, 389]

def row109L1 : List ℕ :=
  [397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
   509]

def row109L2 : List ℕ :=
  [521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599]

def row109L3 : List ℕ :=
  [601, 607, 613, 617, 619, 631, 641, 643, 647]

def row109P1 : List ℕ := row109L0

def row109P2 : List ℕ := row109P1 ++ row109L1

def row109P3 : List ℕ := row109P2 ++ row109L2

def row109L : List ℕ := row109P3 ++ row109L3

theorem row109_a0 : absentOK 109 row109A0 = true := by decide +kernel

theorem row109_e0 : envOK (row109A.map Prod.fst) 5 row109L0 = true := by
  decide +kernel

theorem row109_e1 :
    envOK (row109P1.reverse ++ row109A.map Prod.fst) (envNext 5 row109P1) row109L1 =
      true := by
  decide +kernel

theorem row109_e2 :
    envOK (row109P2.reverse ++ row109A.map Prod.fst) (envNext 5 row109P2) row109L2 =
      true := by
  decide +kernel

theorem row109_e3 :
    envOK (row109P3.reverse ++ row109A.map Prod.fst) (envNext 5 row109P3) row109L3 =
      true := by
  decide +kernel

theorem row109_t : tailOK 109 row109L = true := by decide +kernel

/-- Receiver 109: the certificate is accepted. -/
theorem row109_ok : packRow 109 row109A row109L = true := by
  have a : absentOK 109 row109A0 = true := row109_a0
  have e : envOK (row109A.map Prod.fst) 5 row109P1 = true := row109_e0
  have e : envOK (row109A.map Prod.fst) 5 row109P2 = true :=
    envOK_of_append e row109_e1
  have e : envOK (row109A.map Prod.fst) 5 row109P3 = true :=
    envOK_of_append e row109_e2
  have e : envOK (row109A.map Prod.fst) 5 row109L = true :=
    envOK_of_append e row109_e3
  exact packRow_of_parts a e row109_t

def row113A0 : List (ℕ × List ℕ) :=
  [(5, []), (7, []), (11, []), (17, []), (19, []), (23, []), (29, []), (37, [])]

def row113A : List (ℕ × List ℕ) := row113A0

def row113L0 : List ℕ :=
  [13, 31, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
   137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
   239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349,
   353, 359, 367, 373, 379, 383, 389]

def row113L1 : List ℕ :=
  [397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
   509]

def row113L2 : List ℕ :=
  [521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599]

def row113L3 : List ℕ :=
  [601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673]

def row113L4 : List ℕ :=
  [677, 683, 691]

def row113P1 : List ℕ := row113L0

def row113P2 : List ℕ := row113P1 ++ row113L1

def row113P3 : List ℕ := row113P2 ++ row113L2

def row113P4 : List ℕ := row113P3 ++ row113L3

def row113L : List ℕ := row113P4 ++ row113L4

theorem row113_a0 : absentOK 113 row113A0 = true := by decide +kernel

theorem row113_e0 : envOK (row113A.map Prod.fst) 5 row113L0 = true := by
  decide +kernel

theorem row113_e1 :
    envOK (row113P1.reverse ++ row113A.map Prod.fst) (envNext 5 row113P1) row113L1 =
      true := by
  decide +kernel

theorem row113_e2 :
    envOK (row113P2.reverse ++ row113A.map Prod.fst) (envNext 5 row113P2) row113L2 =
      true := by
  decide +kernel

theorem row113_e3 :
    envOK (row113P3.reverse ++ row113A.map Prod.fst) (envNext 5 row113P3) row113L3 =
      true := by
  decide +kernel

theorem row113_e4 :
    envOK (row113P4.reverse ++ row113A.map Prod.fst) (envNext 5 row113P4) row113L4 =
      true := by
  decide +kernel

theorem row113_t : tailOK 113 row113L = true := by decide +kernel

/-- Receiver 113: the certificate is accepted. -/
theorem row113_ok : packRow 113 row113A row113L = true := by
  have a : absentOK 113 row113A0 = true := row113_a0
  have e : envOK (row113A.map Prod.fst) 5 row113P1 = true := row113_e0
  have e : envOK (row113A.map Prod.fst) 5 row113P2 = true :=
    envOK_of_append e row113_e1
  have e : envOK (row113A.map Prod.fst) 5 row113P3 = true :=
    envOK_of_append e row113_e2
  have e : envOK (row113A.map Prod.fst) 5 row113P4 = true :=
    envOK_of_append e row113_e3
  have e : envOK (row113A.map Prod.fst) 5 row113L = true :=
    envOK_of_append e row113_e4
  exact packRow_of_parts a e row113_t

def row127A0 : List (ℕ × List ℕ) :=
  [(5, []), (7, []), (13, [3]), (17, [19]), (19, [3]), (23, []), (29, []), (31, [3]),
   (37, [28425577383])]

def row127A : List (ℕ × List ℕ) := row127A0

def row127L0 : List ℕ :=
  [11, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
   137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
   239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349,
   353, 359, 367, 373, 379, 383, 389]

def row127L1 : List ℕ :=
  [397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
   509]

def row127L2 : List ℕ :=
  [521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599]

def row127L3 : List ℕ :=
  [601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673]

def row127L4 : List ℕ :=
  [677, 683, 691, 701, 709, 719, 727, 733]

def row127L5 : List ℕ :=
  [739, 743, 751, 757, 761, 769, 773, 787]

def row127L6 : List ℕ :=
  [797, 809]

def row127P1 : List ℕ := row127L0

def row127P2 : List ℕ := row127P1 ++ row127L1

def row127P3 : List ℕ := row127P2 ++ row127L2

def row127P4 : List ℕ := row127P3 ++ row127L3

def row127P5 : List ℕ := row127P4 ++ row127L4

def row127P6 : List ℕ := row127P5 ++ row127L5

def row127L : List ℕ := row127P6 ++ row127L6

theorem row127_a0 : absentOK 127 row127A0 = true := by decide +kernel

theorem row127_e0 : envOK (row127A.map Prod.fst) 5 row127L0 = true := by
  decide +kernel

theorem row127_e1 :
    envOK (row127P1.reverse ++ row127A.map Prod.fst) (envNext 5 row127P1) row127L1 =
      true := by
  decide +kernel

theorem row127_e2 :
    envOK (row127P2.reverse ++ row127A.map Prod.fst) (envNext 5 row127P2) row127L2 =
      true := by
  decide +kernel

theorem row127_e3 :
    envOK (row127P3.reverse ++ row127A.map Prod.fst) (envNext 5 row127P3) row127L3 =
      true := by
  decide +kernel

theorem row127_e4 :
    envOK (row127P4.reverse ++ row127A.map Prod.fst) (envNext 5 row127P4) row127L4 =
      true := by
  decide +kernel

theorem row127_e5 :
    envOK (row127P5.reverse ++ row127A.map Prod.fst) (envNext 5 row127P5) row127L5 =
      true := by
  decide +kernel

theorem row127_e6 :
    envOK (row127P6.reverse ++ row127A.map Prod.fst) (envNext 5 row127P6) row127L6 =
      true := by
  decide +kernel

theorem row127_t : tailOK 127 row127L = true := by decide +kernel

/-- Receiver 127: the certificate is accepted. -/
theorem row127_ok : packRow 127 row127A row127L = true := by
  have a : absentOK 127 row127A0 = true := row127_a0
  have e : envOK (row127A.map Prod.fst) 5 row127P1 = true := row127_e0
  have e : envOK (row127A.map Prod.fst) 5 row127P2 = true :=
    envOK_of_append e row127_e1
  have e : envOK (row127A.map Prod.fst) 5 row127P3 = true :=
    envOK_of_append e row127_e2
  have e : envOK (row127A.map Prod.fst) 5 row127P4 = true :=
    envOK_of_append e row127_e3
  have e : envOK (row127A.map Prod.fst) 5 row127P5 = true :=
    envOK_of_append e row127_e4
  have e : envOK (row127A.map Prod.fst) 5 row127P6 = true :=
    envOK_of_append e row127_e5
  have e : envOK (row127A.map Prod.fst) 5 row127L = true :=
    envOK_of_append e row127_e6
  exact packRow_of_parts a e row127_t

def row131A0 : List (ℕ × List ℕ) :=
  [(5, [11]), (7, [2801]), (13, [53]), (17, []), (29, []), (31, []), (37, []), (41, [5]),
   (53, [61391]), (59, [11]), (61, [107455]), (71, [])]

def row131A : List (ℕ × List ℕ) := row131A0

def row131L0 : List ℕ :=
  [11, 19, 23, 43, 47, 67, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149,
   151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
   257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367,
   373, 379, 383, 389]

def row131L1 : List ℕ :=
  [397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
   509]

def row131L2 : List ℕ :=
  [521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599]

def row131L3 : List ℕ :=
  [601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673]

def row131L4 : List ℕ :=
  [677, 683, 691, 701, 709, 719, 727, 733]

def row131L5 : List ℕ :=
  [739, 743, 751, 757, 761, 769, 773, 787]

def row131L6 : List ℕ :=
  [797, 809, 811, 821, 823, 827, 829]

def row131L7 : List ℕ :=
  [839]

def row131P1 : List ℕ := row131L0

def row131P2 : List ℕ := row131P1 ++ row131L1

def row131P3 : List ℕ := row131P2 ++ row131L2

def row131P4 : List ℕ := row131P3 ++ row131L3

def row131P5 : List ℕ := row131P4 ++ row131L4

def row131P6 : List ℕ := row131P5 ++ row131L5

def row131P7 : List ℕ := row131P6 ++ row131L6

def row131L : List ℕ := row131P7 ++ row131L7

theorem row131_a0 : absentOK 131 row131A0 = true := by decide +kernel

theorem row131_e0 : envOK (row131A.map Prod.fst) 5 row131L0 = true := by
  decide +kernel

theorem row131_e1 :
    envOK (row131P1.reverse ++ row131A.map Prod.fst) (envNext 5 row131P1) row131L1 =
      true := by
  decide +kernel

theorem row131_e2 :
    envOK (row131P2.reverse ++ row131A.map Prod.fst) (envNext 5 row131P2) row131L2 =
      true := by
  decide +kernel

theorem row131_e3 :
    envOK (row131P3.reverse ++ row131A.map Prod.fst) (envNext 5 row131P3) row131L3 =
      true := by
  decide +kernel

theorem row131_e4 :
    envOK (row131P4.reverse ++ row131A.map Prod.fst) (envNext 5 row131P4) row131L4 =
      true := by
  decide +kernel

theorem row131_e5 :
    envOK (row131P5.reverse ++ row131A.map Prod.fst) (envNext 5 row131P5) row131L5 =
      true := by
  decide +kernel

theorem row131_e6 :
    envOK (row131P6.reverse ++ row131A.map Prod.fst) (envNext 5 row131P6) row131L6 =
      true := by
  decide +kernel

theorem row131_e7 :
    envOK (row131P7.reverse ++ row131A.map Prod.fst) (envNext 5 row131P7) row131L7 =
      true := by
  decide +kernel

theorem row131_t : tailOK 131 row131L = true := by decide +kernel

/-- Receiver 131: the certificate is accepted. -/
theorem row131_ok : packRow 131 row131A row131L = true := by
  have a : absentOK 131 row131A0 = true := row131_a0
  have e : envOK (row131A.map Prod.fst) 5 row131P1 = true := row131_e0
  have e : envOK (row131A.map Prod.fst) 5 row131P2 = true :=
    envOK_of_append e row131_e1
  have e : envOK (row131A.map Prod.fst) 5 row131P3 = true :=
    envOK_of_append e row131_e2
  have e : envOK (row131A.map Prod.fst) 5 row131P4 = true :=
    envOK_of_append e row131_e3
  have e : envOK (row131A.map Prod.fst) 5 row131P5 = true :=
    envOK_of_append e row131_e4
  have e : envOK (row131A.map Prod.fst) 5 row131P6 = true :=
    envOK_of_append e row131_e5
  have e : envOK (row131A.map Prod.fst) 5 row131P7 = true :=
    envOK_of_append e row131_e6
  have e : envOK (row131A.map Prod.fst) 5 row131L = true :=
    envOK_of_append e row131_e7
  exact packRow_of_parts a e row131_t

end ReceiverPack
end OddPerfect

#print axioms OddPerfect.ReceiverPack.row109_a0
#print axioms OddPerfect.ReceiverPack.row109_e0
#print axioms OddPerfect.ReceiverPack.row109_e1
#print axioms OddPerfect.ReceiverPack.row109_e2
#print axioms OddPerfect.ReceiverPack.row109_e3
#print axioms OddPerfect.ReceiverPack.row109_t
#print axioms OddPerfect.ReceiverPack.row109_ok
#print axioms OddPerfect.ReceiverPack.row113_a0
#print axioms OddPerfect.ReceiverPack.row113_e0
#print axioms OddPerfect.ReceiverPack.row113_e1
#print axioms OddPerfect.ReceiverPack.row113_e2
#print axioms OddPerfect.ReceiverPack.row113_e3
#print axioms OddPerfect.ReceiverPack.row113_e4
#print axioms OddPerfect.ReceiverPack.row113_t
#print axioms OddPerfect.ReceiverPack.row113_ok
#print axioms OddPerfect.ReceiverPack.row127_a0
#print axioms OddPerfect.ReceiverPack.row127_e0
#print axioms OddPerfect.ReceiverPack.row127_e1
#print axioms OddPerfect.ReceiverPack.row127_e2
#print axioms OddPerfect.ReceiverPack.row127_e3
#print axioms OddPerfect.ReceiverPack.row127_e4
#print axioms OddPerfect.ReceiverPack.row127_e5
#print axioms OddPerfect.ReceiverPack.row127_e6
#print axioms OddPerfect.ReceiverPack.row127_t
#print axioms OddPerfect.ReceiverPack.row127_ok
#print axioms OddPerfect.ReceiverPack.row131_a0
#print axioms OddPerfect.ReceiverPack.row131_e0
#print axioms OddPerfect.ReceiverPack.row131_e1
#print axioms OddPerfect.ReceiverPack.row131_e2
#print axioms OddPerfect.ReceiverPack.row131_e3
#print axioms OddPerfect.ReceiverPack.row131_e4
#print axioms OddPerfect.ReceiverPack.row131_e5
#print axioms OddPerfect.ReceiverPack.row131_e6
#print axioms OddPerfect.ReceiverPack.row131_e7
#print axioms OddPerfect.ReceiverPack.row131_t
#print axioms OddPerfect.ReceiverPack.row131_ok
