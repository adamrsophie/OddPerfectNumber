import OddPerfect.EulerIndexPairReceiverCore

/-!
# Two prime Euler index, branch `v = 1`: receiver certificates 43 to 89

Restricted result; no published source was checked; novelty not verified. The odd perfect
number conjecture remains open.

For each prime receiver `u` with `43 ≤ u ≤ 89`, `u ≠ 47`, a certificate `(A, L)` accepted by
`ReceiverSieve.packRow` (kernel evaluation): the absent primes `A` with their divisor lists, and
the envelope `L`. The set of kept pure row lengths is computed by the checker from `u`. Each
receiver needs its own finite certificate; no uniform statement over all receivers is proved.
-/

namespace OddPerfect
namespace ReceiverPack

open ReceiverSieve

def row43A0 : List (ℕ × List ℕ) :=
  [(5, []), (7, []), (11, [45319]), (13, [3])]

def row43A : List (ℕ × List ℕ) := row43A0

def row43L0 : List ℕ :=
  [17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107,
   109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211,
   223, 227, 229, 233]

def row43L : List ℕ := row43L0

theorem row43_a0 : absentOK 43 row43A0 = true := by decide +kernel

theorem row43_e0 : envOK (row43A.map Prod.fst) 5 row43L0 = true := by
  decide +kernel

theorem row43_t : tailOK 43 row43L = true := by decide +kernel

/-- Receiver 43: the certificate is accepted. -/
theorem row43_ok : packRow 43 row43A row43L = true := by
  have a : absentOK 43 row43A0 = true := row43_a0
  have e : envOK (row43A.map Prod.fst) 5 row43L = true := row43_e0
  exact packRow_of_parts a e row43_t

def row53A0 : List (ℕ × List ℕ) :=
  [(5, []), (13, [476218721057]), (17, []), (19, []), (23, []), (29, []), (31, []), (43, [])]

def row53A : List (ℕ × List ℕ) := row53A0

def row53L0 : List ℕ :=
  [7, 11, 37, 41, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
   137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
   239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313]

def row53L : List ℕ := row53L0

theorem row53_a0 : absentOK 53 row53A0 = true := by decide +kernel

theorem row53_e0 : envOK (row53A.map Prod.fst) 5 row53L0 = true := by
  decide +kernel

theorem row53_t : tailOK 53 row53L = true := by decide +kernel

/-- Receiver 53: the certificate is accepted. -/
theorem row53_ok : packRow 53 row53A row53L = true := by
  have a : absentOK 53 row53A0 = true := row53_a0
  have e : envOK (row53A.map Prod.fst) 5 row53L = true := row53_e0
  exact packRow_of_parts a e row53_t

def row59A0 : List (ℕ × List ℕ) :=
  [(5, [35671]), (7, [9095778971223671544739]), (13, []), (17, [7193]), (19, [233])]

def row59A : List (ℕ × List ℕ) := row59A0

def row59L0 : List ℕ :=
  [11, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109,
   113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
   227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331]

def row59L : List ℕ := row59L0

theorem row59_a0 : absentOK 59 row59A0 = true := by decide +kernel

theorem row59_e0 : envOK (row59A.map Prod.fst) 5 row59L0 = true := by
  decide +kernel

theorem row59_t : tailOK 59 row59L = true := by decide +kernel

/-- Receiver 59: the certificate is accepted. -/
theorem row59_ok : packRow 59 row59A row59L = true := by
  have a : absentOK 59 row59A0 = true := row59_a0
  have e : envOK (row59A.map Prod.fst) 5 row59L = true := row59_e0
  exact packRow_of_parts a e row59_t

def row61A0 : List (ℕ × List ℕ) :=
  [(5, []), (7, []), (11, []), (13, [3]), (17, [])]

def row61A : List (ℕ × List ℕ) := row61A0

def row61L0 : List ℕ :=
  [19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109,
   113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
   227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331,
   337, 347, 349]

def row61L : List ℕ := row61L0

theorem row61_a0 : absentOK 61 row61A0 = true := by decide +kernel

theorem row61_e0 : envOK (row61A.map Prod.fst) 5 row61L0 = true := by
  decide +kernel

theorem row61_t : tailOK 61 row61L = true := by decide +kernel

/-- Receiver 61: the certificate is accepted. -/
theorem row61_ok : packRow 61 row61A row61L = true := by
  have a : absentOK 61 row61A0 = true := row61_a0
  have e : envOK (row61A.map Prod.fst) 5 row61L = true := row61_e0
  exact packRow_of_parts a e row61_t

def row67A0 : List (ℕ × List ℕ) :=
  [(5, []), (7, []), (13, []), (17, [307]), (23, [7]), (29, [13])]

def row67A : List (ℕ × List ℕ) := row67A0

def row67L0 : List ℕ :=
  [11, 19, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
   127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227,
   229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337,
   347, 349, 353, 359, 367, 373, 379, 383, 389]

def row67L : List ℕ := row67L0

theorem row67_a0 : absentOK 67 row67A0 = true := by decide +kernel

theorem row67_e0 : envOK (row67A.map Prod.fst) 5 row67L0 = true := by
  decide +kernel

theorem row67_t : tailOK 67 row67L = true := by decide +kernel

/-- Receiver 67: the certificate is accepted. -/
theorem row67_ok : packRow 67 row67A row67L = true := by
  have a : absentOK 67 row67A0 = true := row67_a0
  have e : envOK (row67A.map Prod.fst) 5 row67L = true := row67_e0
  exact packRow_of_parts a e row67_t

def row71A0 : List (ℕ × List ℕ) :=
  [(5, [11]), (7, []), (11, []), (13, []), (17, [])]

def row71A : List (ℕ × List ℕ) := row71A0

def row71L0 : List ℕ :=
  [19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109,
   113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
   227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331,
   337, 347, 349, 353, 359, 367, 373, 379, 383, 389]

def row71L1 : List ℕ :=
  [397, 401, 409]

def row71P1 : List ℕ := row71L0

def row71L : List ℕ := row71P1 ++ row71L1

theorem row71_a0 : absentOK 71 row71A0 = true := by decide +kernel

theorem row71_e0 : envOK (row71A.map Prod.fst) 5 row71L0 = true := by
  decide +kernel

theorem row71_e1 :
    envOK (row71P1.reverse ++ row71A.map Prod.fst) (envNext 5 row71P1) row71L1 =
      true := by
  decide +kernel

theorem row71_t : tailOK 71 row71L = true := by decide +kernel

/-- Receiver 71: the certificate is accepted. -/
theorem row71_ok : packRow 71 row71A row71L = true := by
  have a : absentOK 71 row71A0 = true := row71_a0
  have e : envOK (row71A.map Prod.fst) 5 row71P1 = true := row71_e0
  have e : envOK (row71A.map Prod.fst) 5 row71L = true :=
    envOK_of_append e row71_e1
  exact packRow_of_parts a e row71_t

def row73A0 : List (ℕ × List ℕ) :=
  [(5, []), (7, []), (11, []), (13, []), (17, [])]

def row73A : List (ℕ × List ℕ) := row73A0

def row73L0 : List ℕ :=
  [19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109,
   113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
   227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331,
   337, 347, 349, 353, 359, 367, 373, 379, 383, 389]

def row73L1 : List ℕ :=
  [397, 401, 409, 419]

def row73P1 : List ℕ := row73L0

def row73L : List ℕ := row73P1 ++ row73L1

theorem row73_a0 : absentOK 73 row73A0 = true := by decide +kernel

theorem row73_e0 : envOK (row73A.map Prod.fst) 5 row73L0 = true := by
  decide +kernel

theorem row73_e1 :
    envOK (row73P1.reverse ++ row73A.map Prod.fst) (envNext 5 row73P1) row73L1 =
      true := by
  decide +kernel

theorem row73_t : tailOK 73 row73L = true := by decide +kernel

/-- Receiver 73: the certificate is accepted. -/
theorem row73_ok : packRow 73 row73A row73L = true := by
  have a : absentOK 73 row73A0 = true := row73_a0
  have e : envOK (row73A.map Prod.fst) 5 row73P1 = true := row73_e0
  have e : envOK (row73A.map Prod.fst) 5 row73L = true :=
    envOK_of_append e row73_e1
  exact packRow_of_parts a e row73_t

def row79A0 : List (ℕ × List ℕ) :=
  [(5, [31]), (7, []), (11, [7]), (13, [3]), (17, [])]

def row79A : List (ℕ × List ℕ) := row79A0

def row79L0 : List ℕ :=
  [19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109,
   113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
   227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331,
   337, 347, 349, 353, 359, 367, 373, 379, 383, 389]

def row79L1 : List ℕ :=
  [397, 401, 409, 419, 421, 431, 433, 439, 443, 449]

def row79P1 : List ℕ := row79L0

def row79L : List ℕ := row79P1 ++ row79L1

theorem row79_a0 : absentOK 79 row79A0 = true := by decide +kernel

theorem row79_e0 : envOK (row79A.map Prod.fst) 5 row79L0 = true := by
  decide +kernel

theorem row79_e1 :
    envOK (row79P1.reverse ++ row79A.map Prod.fst) (envNext 5 row79P1) row79L1 =
      true := by
  decide +kernel

theorem row79_t : tailOK 79 row79L = true := by decide +kernel

/-- Receiver 79: the certificate is accepted. -/
theorem row79_ok : packRow 79 row79A row79L = true := by
  have a : absentOK 79 row79A0 = true := row79_a0
  have e : envOK (row79A.map Prod.fst) 5 row79P1 = true := row79_e0
  have e : envOK (row79A.map Prod.fst) 5 row79L = true :=
    envOK_of_append e row79_e1
  exact packRow_of_parts a e row79_t

def row83A0 : List (ℕ × List ℕ) :=
  [(5, []), (7, [89493253667395975703192863402747]), (11, [1231]), (13, []), (17, [892079])]

def row83A : List (ℕ × List ℕ) := row83A0

def row83L0 : List ℕ :=
  [19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109,
   113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
   227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331,
   337, 347, 349, 353, 359, 367, 373, 379, 383, 389]

def row83L1 : List ℕ :=
  [397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467]

def row83P1 : List ℕ := row83L0

def row83L : List ℕ := row83P1 ++ row83L1

theorem row83_a0 : absentOK 83 row83A0 = true := by decide +kernel

theorem row83_e0 : envOK (row83A.map Prod.fst) 5 row83L0 = true := by
  decide +kernel

theorem row83_e1 :
    envOK (row83P1.reverse ++ row83A.map Prod.fst) (envNext 5 row83P1) row83L1 =
      true := by
  decide +kernel

theorem row83_t : tailOK 83 row83L = true := by decide +kernel

/-- Receiver 83: the certificate is accepted. -/
theorem row83_ok : packRow 83 row83A row83L = true := by
  have a : absentOK 83 row83A0 = true := row83_a0
  have e : envOK (row83A.map Prod.fst) 5 row83P1 = true := row83_e0
  have e : envOK (row83A.map Prod.fst) 5 row83L = true :=
    envOK_of_append e row83_e1
  exact packRow_of_parts a e row83_t

def row89A0 : List (ℕ × List ℕ) :=
  [(5, []), (7, []), (11, []), (13, []), (17, []), (19, [])]

def row89A : List (ℕ × List ℕ) := row89A0

def row89L0 : List ℕ :=
  [23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
   127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227,
   229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337,
   347, 349, 353, 359, 367, 373, 379, 383, 389]

def row89L1 : List ℕ :=
  [397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
   509]

def row89L2 : List ℕ :=
  [521, 523]

def row89P1 : List ℕ := row89L0

def row89P2 : List ℕ := row89P1 ++ row89L1

def row89L : List ℕ := row89P2 ++ row89L2

theorem row89_a0 : absentOK 89 row89A0 = true := by decide +kernel

theorem row89_e0 : envOK (row89A.map Prod.fst) 5 row89L0 = true := by
  decide +kernel

theorem row89_e1 :
    envOK (row89P1.reverse ++ row89A.map Prod.fst) (envNext 5 row89P1) row89L1 =
      true := by
  decide +kernel

theorem row89_e2 :
    envOK (row89P2.reverse ++ row89A.map Prod.fst) (envNext 5 row89P2) row89L2 =
      true := by
  decide +kernel

theorem row89_t : tailOK 89 row89L = true := by decide +kernel

/-- Receiver 89: the certificate is accepted. -/
theorem row89_ok : packRow 89 row89A row89L = true := by
  have a : absentOK 89 row89A0 = true := row89_a0
  have e : envOK (row89A.map Prod.fst) 5 row89P1 = true := row89_e0
  have e : envOK (row89A.map Prod.fst) 5 row89P2 = true :=
    envOK_of_append e row89_e1
  have e : envOK (row89A.map Prod.fst) 5 row89L = true :=
    envOK_of_append e row89_e2
  exact packRow_of_parts a e row89_t

end ReceiverPack
end OddPerfect

#print axioms OddPerfect.ReceiverPack.row43_a0
#print axioms OddPerfect.ReceiverPack.row43_e0
#print axioms OddPerfect.ReceiverPack.row43_t
#print axioms OddPerfect.ReceiverPack.row43_ok
#print axioms OddPerfect.ReceiverPack.row53_a0
#print axioms OddPerfect.ReceiverPack.row53_e0
#print axioms OddPerfect.ReceiverPack.row53_t
#print axioms OddPerfect.ReceiverPack.row53_ok
#print axioms OddPerfect.ReceiverPack.row59_a0
#print axioms OddPerfect.ReceiverPack.row59_e0
#print axioms OddPerfect.ReceiverPack.row59_t
#print axioms OddPerfect.ReceiverPack.row59_ok
#print axioms OddPerfect.ReceiverPack.row61_a0
#print axioms OddPerfect.ReceiverPack.row61_e0
#print axioms OddPerfect.ReceiverPack.row61_t
#print axioms OddPerfect.ReceiverPack.row61_ok
#print axioms OddPerfect.ReceiverPack.row67_a0
#print axioms OddPerfect.ReceiverPack.row67_e0
#print axioms OddPerfect.ReceiverPack.row67_t
#print axioms OddPerfect.ReceiverPack.row67_ok
#print axioms OddPerfect.ReceiverPack.row71_a0
#print axioms OddPerfect.ReceiverPack.row71_e0
#print axioms OddPerfect.ReceiverPack.row71_e1
#print axioms OddPerfect.ReceiverPack.row71_t
#print axioms OddPerfect.ReceiverPack.row71_ok
#print axioms OddPerfect.ReceiverPack.row73_a0
#print axioms OddPerfect.ReceiverPack.row73_e0
#print axioms OddPerfect.ReceiverPack.row73_e1
#print axioms OddPerfect.ReceiverPack.row73_t
#print axioms OddPerfect.ReceiverPack.row73_ok
#print axioms OddPerfect.ReceiverPack.row79_a0
#print axioms OddPerfect.ReceiverPack.row79_e0
#print axioms OddPerfect.ReceiverPack.row79_e1
#print axioms OddPerfect.ReceiverPack.row79_t
#print axioms OddPerfect.ReceiverPack.row79_ok
#print axioms OddPerfect.ReceiverPack.row83_a0
#print axioms OddPerfect.ReceiverPack.row83_e0
#print axioms OddPerfect.ReceiverPack.row83_e1
#print axioms OddPerfect.ReceiverPack.row83_t
#print axioms OddPerfect.ReceiverPack.row83_ok
#print axioms OddPerfect.ReceiverPack.row89_a0
#print axioms OddPerfect.ReceiverPack.row89_e0
#print axioms OddPerfect.ReceiverPack.row89_e1
#print axioms OddPerfect.ReceiverPack.row89_e2
#print axioms OddPerfect.ReceiverPack.row89_t
#print axioms OddPerfect.ReceiverPack.row89_ok
