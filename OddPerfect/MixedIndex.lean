import OddPerfect.MixedIndexData

/-!
# The mixed index family 3, 5, 7 with special prime 5

Let `N` be an odd perfect number with `v_3(N) = 2` and `v_5(N) = 1`, so that `5` is the special
prime. If every prime `p ≠ 5` dividing `N` has an index `m_p = v_p(N) + 1` divisible by `3`, by
`5` or by `7`, a contradiction follows. The proof is a finite exclusion tree (`MixedIndex.tree`,
1846 branching nodes, depth 31) checked by the kernel with `MixedIndex.chk`, whose soundness is
`MixedIndex.chk_sound`.

The published theorem of Fletcher, Nielsen and Ochem (Math. Comp. 81, 2012) excludes the family
where every ordinary index is divisible by `3` or by `5`; the family here also allows indices
divisible by `7` only, under the extra conditions `v_3(N) = 2` and `v_5(N) = 1`. Whether this
case is new has not been verified against the literature.
-/

namespace OddPerfect

/-- No odd perfect number `N` has `v_3(N) = 2`, `v_5(N) = 1`, and an index `v_p(N) + 1`
divisible by `3`, `5` or `7` at every prime `p ≠ 5` dividing `N`. -/
theorem not_mixed_index_three_five_seven {N : ℕ} (h : OddPerfect N)
    (h3 : N.factorization 3 = 2) (h5 : N.factorization 5 = 1)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ 5 →
      3 ∣ N.factorization p + 1 ∨ 5 ∣ N.factorization p + 1 ∨ 7 ∣ N.factorization p + 1) :
    False := by
  have h13 : 13 ∣ N := OPNStarter.thirteen_dvd_of_three_sq h.2 h3
  refine MixedIndex.chk_sound h h3 h5 hexp MixedIndex.primes_prime MixedIndex.tree [13] [] 0 0
    ⟨?_, by simp, Or.inl rfl, Or.inl rfl⟩ ?_ MixedIndex.tree_ok
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨by norm_num, h13, by norm_num, by norm_num⟩
  · intro p k hk
    have hf : MixedIndex.isAt p k MixedIndex.tree = false := rfl
    rw [hf] at hk
    exact absurd hk Bool.false_ne_true

end OddPerfect

#print axioms OddPerfect.not_mixed_index_three_five_seven
