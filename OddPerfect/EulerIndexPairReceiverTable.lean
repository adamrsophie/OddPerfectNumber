import OddPerfect.EulerIndexPairReceiverPacking
import OddPerfect.EulerIndexPairReceiverTableA
import OddPerfect.EulerIndexPairReceiverTableB
import OddPerfect.EulerIndexPairReceiverTableC
import OddPerfect.EulerIndexPairReceiverTableD
import OddPerfect.EulerIndexPairReceiverTableE
import OddPerfect.EulerIndexPairReceiverTableF
import OddPerfect.EulerIndexPairReceiverTableG

/-!
# Two prime Euler index, branch `v = 1`: the receiver is at least 173

Restricted result; no published source was checked; novelty not verified. The odd perfect
number conjecture remains open.

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly the two prime factors
`r ≠ s`, oriented by a frame `PairFrame N q r s t u`. In the branch `v = 1`, that is
`σ(t ^ e) = q * u` with `e = v_t(N)`:

* `PairFrame.receiver_ge_packing`: `173 ≤ u`. Every prime receiver `u` with `43 ≤ u < 173`,
  `u ≠ 47`, has a certificate accepted by `ReceiverSieve.packRow` (kernel evaluation), which
  `PairFrame.false_of_packRow` excludes; `u = 47` and `u < 43` are excluded by
  `PairFrame.receiver_ge`.
* `eulerIndex_pair_receiver_ge_packing`: the form without a frame, with `172 ≤ e`.

Each receiver needs its own finite certificate; no uniform statement over all receivers is
proved. The branch `v = 0` and the family are not excluded.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

open ReceiverSieve

/-- The receivers of the certificate table. -/
theorem packTable_mem : ∀ u < 173, u.Prime → 43 ≤ u → u ≠ 47 →
    u ∈ [43, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139,
      149, 151, 157, 163, 167] :=
  @of_decide_eq_true _ (@Nat.decidableBallLT 173 _ fun _ _ => inferInstance)
    (by decide +kernel)

variable {N q m r s t u : ℕ}

/-- In the branch `v = 1`: `173 ≤ u`. -/
theorem PairFrame.receiver_ge_packing (F : PairFrame N q r s t u) (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s})
    (hv : σ 1 (t ^ N.factorization t) = q * u) :
    173 ≤ u := by
  obtain ⟨h43, h47⟩ := F.receiver_ge h hq hN hqm hr hs hrs hJ hv
  by_contra hc
  push Not at hc
  have hmem := packTable_mem u hc F.u_prime h43 h47
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row43_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row53_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row59_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row61_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row67_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row71_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row73_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row79_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row83_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row89_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row97_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row101_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row103_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row107_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row109_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row113_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row127_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row131_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row137_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row139_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row149_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row151_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row157_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row163_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row167_ok

/-- The family form: in the two prime Euler index family, the oriented pair `(t, u)`
satisfies, in the branch `v = 1`, `3 ∤ N`, `173 ≤ u` and `172 ≤ v_t(N)`. -/
theorem eulerIndex_pair_receiver_ge_packing (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧
      (∃ v, σ 1 (t ^ N.factorization t) = q * u ^ v) ∧
      (σ 1 (t ^ N.factorization t) = q * u →
        ¬ 3 ∣ N ∧ 173 ≤ u ∧ 172 ≤ N.factorization t) := by
  obtain ⟨t, u, F⟩ := exists_pairFrame h hq hN hqm hr hs hrs hJ
  refine ⟨t, u, F.pair, F.ne, F.emit, fun hv =>
    ⟨F.receiver_not_three_dvd h hq hN hqm hr hs hrs hJ hv,
      F.receiver_ge_packing h hq hN hqm hr hs hrs hJ hv, ?_⟩⟩
  have hU := F.receiver_ge_packing h hq hN hqm hr hs hrs hJ hv
  have hue := (F.vOne_basic h hq hN hqm hr hs hrs hJ hv).1
  omega

end OddPerfect

#print axioms OddPerfect.packTable_mem
#print axioms OddPerfect.PairFrame.receiver_ge_packing
#print axioms OddPerfect.eulerIndex_pair_receiver_ge_packing
