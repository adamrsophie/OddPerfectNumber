import OddPerfect.EulerIndexPairReceiverTable
import OddPerfect.EulerIndexPairReceiverWideA
import OddPerfect.EulerIndexPairReceiverWideB
import OddPerfect.EulerIndexPairReceiverWideC

/-!
# Two prime Euler index, branch `v = 1`: the receiver is at least 401

Restricted result; no published source was checked; novelty not verified. The odd perfect
number conjecture remains open.

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly the two prime factors
`r ≠ s`, oriented by a frame `PairFrame N q r s t u`. In the branch `v = 1`, that is
`σ(t ^ e) = q * u` with `e = v_t(N)`:

* `PairFrame.receiver_ge_wide`: `401 ≤ u`. Every prime receiver `u` with `173 ≤ u < 401` has a
  certificate accepted by `ReceiverSieve.packRow` (kernel evaluation), which
  `PairFrame.false_of_packRow` excludes; `u < 173` is excluded by
  `PairFrame.receiver_ge_packing`.
* `eulerIndex_pair_receiver_ge_wide`: the form without a frame, with `400 ≤ e`.

Each receiver needs its own finite certificate; no uniform statement over all receivers is
proved. The branch `v = 0` and the family are not excluded.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

open ReceiverSieve

/-- The receivers of the wide certificate table, with the test `primeFast`. -/
theorem packWide_mem_fast : ∀ u < 401, primeFast u = true → 173 ≤ u →
    u ∈ [173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269,
      271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379,
      383, 389, 397] :=
  @of_decide_eq_true _ (@Nat.decidableBallLT 401 _ fun _ _ => inferInstance)
    (by decide +kernel)

/-- The receivers of the wide certificate table. -/
theorem packWide_mem : ∀ u < 401, u.Prime → 173 ≤ u →
    u ∈ [173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269,
      271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379,
      383, 389, 397] :=
  fun u hu hp h173 => packWide_mem_fast u hu ((primeFast_iff u).mpr hp) h173

variable {N q m r s t u : ℕ}

/-- In the branch `v = 1`: `401 ≤ u`. -/
theorem PairFrame.receiver_ge_wide (F : PairFrame N q r s t u) (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s})
    (hv : σ 1 (t ^ N.factorization t) = q * u) :
    401 ≤ u := by
  have h173 := F.receiver_ge_packing h hq hN hqm hr hs hrs hJ hv
  by_contra hc
  push Not at hc
  have hmem := packWide_mem u hc F.u_prime h173
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row173_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row179_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row181_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row191_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row193_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row197_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row199_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row211_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row223_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row227_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row229_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row233_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row239_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row241_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row251_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row257_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row263_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row269_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row271_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row277_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row281_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row283_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row293_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row307_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row311_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row313_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row317_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row331_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row337_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row347_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row349_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row353_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row359_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row367_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row373_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row379_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row383_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row389_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row397_ok

/-- The family form: in the two prime Euler index family, the oriented pair `(t, u)`
satisfies, in the branch `v = 1`, `3 ∤ N`, `401 ≤ u` and `400 ≤ v_t(N)`. -/
theorem eulerIndex_pair_receiver_ge_wide (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧
      (∃ v, σ 1 (t ^ N.factorization t) = q * u ^ v) ∧
      (σ 1 (t ^ N.factorization t) = q * u →
        ¬ 3 ∣ N ∧ 401 ≤ u ∧ 400 ≤ N.factorization t) := by
  obtain ⟨t, u, F⟩ := exists_pairFrame h hq hN hqm hr hs hrs hJ
  refine ⟨t, u, F.pair, F.ne, F.emit, fun hv =>
    ⟨F.receiver_not_three_dvd h hq hN hqm hr hs hrs hJ hv,
      F.receiver_ge_wide h hq hN hqm hr hs hrs hJ hv, ?_⟩⟩
  have hU := F.receiver_ge_wide h hq hN hqm hr hs hrs hJ hv
  have hue := (F.vOne_basic h hq hN hqm hr hs hrs hJ hv).1
  omega

end OddPerfect

#print axioms OddPerfect.packWide_mem_fast
#print axioms OddPerfect.packWide_mem
#print axioms OddPerfect.PairFrame.receiver_ge_wide
#print axioms OddPerfect.eulerIndex_pair_receiver_ge_wide
