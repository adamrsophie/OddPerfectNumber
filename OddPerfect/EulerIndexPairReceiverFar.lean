import OddPerfect.EulerIndexPairReceiverWide
import OddPerfect.EulerIndexPairReceiverFarA
import OddPerfect.EulerIndexPairReceiverFarB
import OddPerfect.EulerIndexPairReceiverFarC

/-!
# Two prime Euler index, branch `v = 1`: the receiver is at least 557

Restricted result; no published source was checked; novelty not verified. The odd perfect
number conjecture remains open.

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly the two prime factors
`r ≠ s`, oriented by a frame `PairFrame N q r s t u`. In the branch `v = 1`, that is
`σ(t ^ e) = q * u` with `e = v_t(N)`:

* `PairFrame.receiver_ge_far`: `557 ≤ u`. Every prime receiver `u` with `401 ≤ u < 557` has a
  certificate accepted by `ReceiverSieve.packRow` (kernel evaluation), which
  `PairFrame.false_of_packRow` excludes; `u < 401` is excluded by
  `PairFrame.receiver_ge_wide`.
* `eulerIndex_pair_receiver_ge_far`: the form without a frame, with `556 ≤ e`.

Each receiver needs its own finite certificate; no uniform statement over all receivers is
proved. The branch `v = 0` and the family are not excluded.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

open ReceiverSieve

/-- The receivers of the far certificate table, with the test `primeFast`. -/
theorem packFar_mem_fast : ∀ u < 557, primeFast u = true → 401 ≤ u →
    u ∈ [401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
      509, 521, 523, 541, 547] :=
  @of_decide_eq_true _ (@Nat.decidableBallLT 557 _ fun _ _ => inferInstance)
    (by decide +kernel)

/-- The receivers of the far certificate table. -/
theorem packFar_mem : ∀ u < 557, u.Prime → 401 ≤ u →
    u ∈ [401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
      509, 521, 523, 541, 547] :=
  fun u hu hp h401 => packFar_mem_fast u hu ((primeFast_iff u).mpr hp) h401

variable {N q m r s t u : ℕ}

/-- In the branch `v = 1`: `557 ≤ u`. -/
theorem PairFrame.receiver_ge_far (F : PairFrame N q r s t u) (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s})
    (hv : σ 1 (t ^ N.factorization t) = q * u) :
    557 ≤ u := by
  have h401 := F.receiver_ge_wide h hq hN hqm hr hs hrs hJ hv
  by_contra hc
  push Not at hc
  have hmem := packFar_mem u hc F.u_prime h401
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row401_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row409_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row419_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row421_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row431_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row433_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row439_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row443_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row449_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row457_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row461_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row463_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row467_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row479_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row487_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row491_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row499_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row503_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row509_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row521_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row523_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row541_ok
  · exact F.false_of_packRow h hq hN hqm hr hs hrs hJ hv ReceiverPack.row547_ok

/-- The family form: in the two prime Euler index family, the oriented pair `(t, u)`
satisfies, in the branch `v = 1`, `3 ∤ N`, `557 ≤ u` and `556 ≤ v_t(N)`. -/
theorem eulerIndex_pair_receiver_ge_far (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧
      (∃ v, σ 1 (t ^ N.factorization t) = q * u ^ v) ∧
      (σ 1 (t ^ N.factorization t) = q * u →
        ¬ 3 ∣ N ∧ 557 ≤ u ∧ 556 ≤ N.factorization t) := by
  obtain ⟨t, u, F⟩ := exists_pairFrame h hq hN hqm hr hs hrs hJ
  refine ⟨t, u, F.pair, F.ne, F.emit, fun hv =>
    ⟨F.receiver_not_three_dvd h hq hN hqm hr hs hrs hJ hv,
      F.receiver_ge_far h hq hN hqm hr hs hrs hJ hv, ?_⟩⟩
  have hU := F.receiver_ge_far h hq hN hqm hr hs hrs hJ hv
  have hue := (F.vOne_basic h hq hN hqm hr hs hrs hJ hv).1
  omega

end OddPerfect

#print axioms OddPerfect.packFar_mem_fast
#print axioms OddPerfect.packFar_mem
#print axioms OddPerfect.PairFrame.receiver_ge_far
#print axioms OddPerfect.eulerIndex_pair_receiver_ge_far
