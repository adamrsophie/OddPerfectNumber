import OddPerfect.PrimePowerIndexBound

/-!
# Indices that are powers of one prime: caps on the receivers only

Let `l` be an odd prime and `N` an odd perfect number with special prime `q` such that every
ordinary index `e_p + 1` (`p ≠ q`) is a power `l ^ γ_p` with `γ_p ≥ 1`. Write
`S = primePowIndexReceivers N q l` for the ordinary prime factors `s ≡ 1 (mod l)`,
`U = primePowIndexSources N q l` for the ordinary prime factors `p ≠ l`, `p ≢ 1 (mod l)` with
`σ(p ^ e_p)` a power of `q`, and `C = primePowIndexWeight N q l = e_l + Σ_{s ∈ S} e_s`.

* `card_primeFactors_le_of_prime_pow_index_weighted`: `ω(N) ≤ C + #U + 2`. For an ordinary
  `p ∉ S`, `p ≠ l`, every prime factor of `σ(p ^ e_p)` is `≡ 1 (mod l)` (the prime `l` does not
  divide it since the order of `p` modulo `l` divides both `l ^ γ_p` and `l - 1`). So if
  `σ(p ^ e_p)` is not a power of `q`, it has a prime factor in `S`; a receiver `s` has at most
  `e_s` senders (`card_feeders_le`), and `#S ≤ e_l` (`sum_padicValNat_succ_le`).
* `two_mul_pred_pow_card_le`: `2 (l - 1) ^ #U ≤ C + #U + 3`. No ordinary row feeds a source
  `p ∈ U`, so `v_p(σ(q ^ α)) = e_p`, and the lemma of Dandapat, Hunsucker and Pomerance gives
  `p ^ (l - 2) ∣ α + 1`; Bang's theorem at `q` bounds the number of divisors of `α + 1`.
* `card_primeFactors_le_of_prime_pow_index_receivers`: if `e_l ≤ B` and `e_s ≤ B` for every
  `s ∈ S`, then `ω(N) ≤ B ^ 2 + 2 B + 2`. No condition on `q` modulo `l` is needed.
* `lt_two_pow_four_pow_of_prime_pow_index_receivers`: then `N < 2 ^ (4 ^ (B ^ 2 + 2 B + 2))`.

These results bound `ω(N)` under caps on the receivers and exclude nothing: the cap `B` is a
hypothesis and no bound on `B` is known. Indices with different prime divisors are not covered;
there ordinary rows can feed the sources in `U`. For `l = 3` and `l = 5` the family is empty by
Fletcher, Nielsen and Ochem (Math. Comp. 81 (2012)) together with Kanold's theorem; the library
proves only instances. Whether these results are new was not verified against the literature.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The receivers: the prime factors `s ≠ q` of `N` with `s ≡ 1 (mod l)`. -/
def primePowIndexReceivers (N q l : ℕ) : Finset ℕ :=
  N.primeFactors.filter (fun s => s ≠ q ∧ s % l = 1)

open Classical in
/-- The sources: the prime factors `p ≠ q` of `N` with `p ≠ l`, `p ≢ 1 (mod l)` and
`σ(p ^ v_p(N))` a power of `q`. -/
noncomputable def primePowIndexSources (N q l : ℕ) : Finset ℕ :=
  N.primeFactors.filter (fun p => p ≠ q ∧ p ≠ l ∧ p % l ≠ 1 ∧
    ∃ c, σ 1 (p ^ N.factorization p) = q ^ c)

/-- The weight `v_l(N) + Σ v_s(N)`, the sum over the receivers `s`. -/
def primePowIndexWeight (N q l : ℕ) : ℕ :=
  N.factorization l + ∑ s ∈ primePowIndexReceivers N q l, N.factorization s

private lemma mem_receivers {N q l s : ℕ} :
    s ∈ primePowIndexReceivers N q l ↔ s ∈ N.primeFactors ∧ s ≠ q ∧ s % l = 1 :=
  Finset.mem_filter

private lemma mem_sources {N q l p : ℕ} :
    p ∈ primePowIndexSources N q l ↔ p ∈ N.primeFactors ∧ p ≠ q ∧ p ≠ l ∧ p % l ≠ 1 ∧
      ∃ c, σ 1 (p ^ N.factorization p) = q ^ c := by
  classical
  unfold primePowIndexSources
  rw [Finset.mem_filter]

/-- If `e + 1 = l ^ γ` and `p ≢ 1 (mod l)`, then `l ∤ σ(p ^ e)`. -/
private lemma not_dvd_sigma_of_mod_ne_one {p l e γ : ℕ} (hp : p.Prime) (hl : l.Prime)
    (he : e + 1 = l ^ γ) (hp1 : p % l ≠ 1) : ¬ l ∣ σ 1 (p ^ e) := by
  intro hd
  have hl2 := hl.two_le
  rcases (prime_dvd_sigma_prime_pow hp hl hd).2 with ⟨h1, -⟩ | ⟨ho1, hod, hot⟩
  · exact hp1 h1
  · rw [he] at hod
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hl).mp hod
    have hj0 : j ≠ 0 := by rintro rfl; rw [hj, pow_zero] at ho1; omega
    rw [hj] at hot
    have := Nat.le_of_dvd (by omega) ((dvd_pow_self l hj0).trans hot)
    omega

/-- Every receiver contributes a factor `l` to `σ(N)`, so there are at most `v_l(N)`. -/
private lemma card_receivers_le {N q l : ℕ} (h : OddPerfect N) (hl : l.Prime) (hl2 : l ≠ 2)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, 1 ≤ γ ∧ N.factorization p + 1 = l ^ γ) :
    (primePowIndexReceivers N q l).card ≤ N.factorization l := by
  have : Fact l.Prime := ⟨hl⟩
  rw [Finset.card_eq_sum_ones]
  calc ∑ p ∈ primePowIndexReceivers N q l, 1
        ≤ ∑ p ∈ primePowIndexReceivers N q l, padicValNat l (N.factorization p + 1) := by
        refine Finset.sum_le_sum fun p hp => ?_
        obtain ⟨hpN, hpq, -⟩ := mem_receivers.mp hp
        obtain ⟨γ, hγ1, hγ⟩ := hidx p hpN hpq
        exact one_le_padicValNat_of_dvd (by omega)
          (hγ ▸ dvd_pow_self l (by omega : γ ≠ 0))
    _ ≤ ∑ p ∈ N.primeFactors.filter (fun p => p % l = 1),
          padicValNat l (N.factorization p + 1) :=
        Finset.sum_le_sum_of_subset fun p hp => by
          obtain ⟨hpN, -, h1⟩ := mem_receivers.mp hp
          exact Finset.mem_filter.mpr ⟨hpN, h1⟩
    _ ≤ N.factorization l := sum_padicValNat_succ_le h.perfect hl hl2

/-- Weighted form. If every ordinary index `e_p + 1` of the odd perfect number `N` is a power
`l ^ γ_p` (`γ_p ≥ 1`) of the odd prime `l`, then `ω(N) ≤ C + #U + 2`, where
`C = v_l(N) + Σ_{s ∈ S} v_s(N)` over the receivers `S` and `U` is the set of sources. Here `q`
is an arbitrary natural number; in the applications it is the special prime. -/
theorem card_primeFactors_le_of_prime_pow_index_weighted {N q l : ℕ} (h : OddPerfect N)
    (hl : l.Prime) (hl2 : l ≠ 2)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, 1 ≤ γ ∧ N.factorization p + 1 = l ^ γ) :
    N.primeFactors.card ≤
      primePowIndexWeight N q l + (primePowIndexSources N q l).card + 2 := by
  classical
  unfold primePowIndexWeight
  have hN0 := h.ne_zero
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have hpf2 : ∀ p ∈ N.primeFactors, p ≠ 2 := fun p hp h2 =>
    h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hp)
  have hSle := card_receivers_le h hl hl2 hidx
  set S := primePowIndexReceivers N q l with hS
  set U := primePowIndexSources N q l with hU
  set A : ℕ → Finset ℕ := fun s =>
    (N.primeFactors.erase s).filter (fun p => s ∣ σ 1 (p ^ N.factorization p)) with hA
  have hcover : N.primeFactors.erase q ⊆ insert l (S ∪ S.biUnion A ∪ U) := by
    intro p hp
    obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hp
    by_cases hpl : p = l
    · exact hpl ▸ Finset.mem_insert_self _ _
    refine Finset.mem_insert_of_mem ?_
    by_cases h1 : p % l = 1
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (mem_receivers.mpr ⟨hpN, hpq, h1⟩))
    by_cases hc : ∃ c, σ 1 (p ^ N.factorization p) = q ^ c
    · exact Finset.mem_union_right _ (mem_sources.mpr ⟨hpN, hpq, hpl, h1, hc⟩)
    refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
    have hpp := Nat.prime_of_mem_primeFactors hpN
    have hσ0 : σ 1 (p ^ N.factorization p) ≠ 0 :=
      (sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)).ne'
    obtain ⟨t, ht, htd, htq⟩ : ∃ t, t.Prime ∧ t ∣ σ 1 (p ^ N.factorization p) ∧ t ≠ q := by
      by_contra hno
      push Not at hno
      exact hc ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hσ0 fun hd ht => hno _ hd ht⟩
    obtain ⟨γ, -, hγ⟩ := hidx p hpN hpq
    have htl : t ≠ l := fun e => not_dvd_sigma_of_mod_ne_one hpp hl hγ h1 (e ▸ htd)
    have ht1 : t % l = 1 := (prime_dvd_sigma_of_succ_eq_pow hpp ht hl hγ htd).resolve_left htl
    have ht2 : t ≠ 2 := by
      rintro rfl
      rw [Nat.mod_eq_of_lt (by omega)] at ht1
      omega
    have htN := OPNStarter.force_prime h.perfect hpp rfl ht ht2 htd
    have htp : t ≠ p := fun e => h1 (e ▸ ht1)
    exact Finset.mem_biUnion.mpr ⟨t, mem_receivers.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨ht, htN, hN0⟩, htq, ht1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨htp.symm, hpN⟩, htd⟩⟩
  have hAle : ∀ s ∈ S, (A s).card ≤ N.factorization s := fun s hs =>
    card_feeders_le h.perfect (Nat.prime_of_mem_primeFactors (mem_receivers.mp hs).1)
      (hpf2 s (mem_receivers.mp hs).1)
  have hbi : (S.biUnion A).card ≤ ∑ s ∈ S, N.factorization s :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum hAle)
  have hqle := Finset.pred_card_le_card_erase (s := N.primeFactors) (a := q)
  have h1 := Finset.card_le_card hcover
  have h2 := Finset.card_insert_le l (S ∪ S.biUnion A ∪ U)
  have h3 := Finset.card_union_le (S ∪ S.biUnion A) U
  have h4 := Finset.card_union_le S (S.biUnion A)
  omega

/-- The sources are few. Under the hypotheses of the weighted form, with `q` the special prime,
`2 (l - 1) ^ #U ≤ C + #U + 3`: every source `p` has `p ^ (l - 2) ∣ α + 1` (`α = v_q(N)`), and
the number of divisors of `α + 1` is at most `ω(N) + 1` by Bang's theorem. -/
theorem two_mul_pred_pow_card_le {N q l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, 1 ≤ γ ∧ N.factorization p + 1 = l ^ γ) :
    2 * (l - 1) ^ (primePowIndexSources N q l).card ≤
      primePowIndexWeight N q l + (primePowIndexSources N q l).card + 3 := by
  have hw := card_primeFactors_le_of_prime_pow_index_weighted h hl hl2 hidx
  set U := primePowIndexSources N q l with hU
  have hN0 := h.ne_zero
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have hidx' : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, N.factorization p + 1 = l ^ γ :=
    fun p hp hpq => by obtain ⟨γ, -, hγ⟩ := hidx p hp hpq; exact ⟨γ, hγ⟩
  have hUprop : ∀ p ∈ U, p.Prime ∧ p ≠ 2 ∧ p ^ (l - 2) ∣ N.factorization q + 1 := by
    intro p hp
    obtain ⟨hpN, hpq, hpl, hp1, c, hc⟩ := mem_sources.mp hp
    have hpp := Nat.prime_of_mem_primeFactors hpN
    have hp2 : p ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hpN)
    obtain ⟨γ, hγ1, hγ⟩ := hidx p hpN hpq
    have hle : l ≤ l ^ γ := Nat.le_self_pow (by omega) l
    obtain ⟨β, hβ⟩ : ∃ β, N.factorization p = 2 * β := by
      obtain ⟨m, hm⟩ : Odd (l ^ γ) := (hl.odd_of_ne_two hl2).pow
      exact ⟨m, by omega⟩
    have hv := padicValNat_sigma_special_eq_of_prime_pow_index h hq hodd hl hidx' hpN hpq hpl hp1
    rw [hβ] at hc hv
    have hdvd := pow_dvd_succ_of_sigma_eq_pow hpp hp2 hq hpq (by omega) hc hv
    exact ⟨hpp, hp2, (pow_dvd_pow p (by omega)).trans hdvd⟩
  have hτ := two_mul_pow_le_card_divisors U (n := N.factorization q + 1) (b := l - 2)
    (by omega) (by obtain ⟨k, hk⟩ := hodd; exact ⟨k + 1, by omega⟩) (by omega) hUprop
  have hτ' := card_divisors_succ_le h hq hodd
  have hqN : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq,
    Nat.dvd_of_factorization_pos (by obtain ⟨k, hk⟩ := hodd; omega), hN0⟩
  have hcard := Finset.card_erase_add_one hqN
  rw [show l - 2 + 1 = l - 1 by omega] at hτ
  omega

/-- `B ^ 2 + 2 B + 4 < 2 ^ (B + 2)` for `B ≥ 1`. -/
private lemma sq_add_lt_two_pow_add_two {B : ℕ} (hB : 1 ≤ B) : B ^ 2 + 2 * B + 4 < 2 ^ (B + 2) := by
  induction B, hB using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h2 : 2 ^ (n + 1 + 2) = 2 * 2 ^ (n + 2) := by ring
    rw [h2]
    nlinarith

/-- Capped form: caps only on the receivers. If every ordinary index `e_p + 1` of the odd
perfect number `N` (special prime `q`) is a power `l ^ γ_p` (`γ_p ≥ 1`) of the odd prime `l`,
`v_l(N) ≤ B`, and `v_s(N) ≤ B` for every ordinary prime factor `s ≡ 1 (mod l)`, then `N` has at
most `B ^ 2 + 2 B + 2` distinct prime factors. No condition on `q` modulo `l` and no cap on the
other exponents is assumed. The cap `B` is a hypothesis; no bound on it is known, so this
excludes nothing. Whether this result is new was not verified against the literature. -/
theorem card_primeFactors_le_of_prime_pow_index_receivers {N q l B : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, 1 ≤ γ ∧ N.factorization p + 1 = l ^ γ)
    (hBl : N.factorization l ≤ B)
    (hB : ∀ s ∈ N.primeFactors, s ≠ q → s % l = 1 → N.factorization s ≤ B) :
    N.primeFactors.card ≤ B ^ 2 + 2 * B + 2 := by
  have hw := card_primeFactors_le_of_prime_pow_index_weighted h hl hl2 hidx
  have hτ := two_mul_pred_pow_card_le h hq hodd hl hl2 hidx
  have hSle := card_receivers_le h hl hl2 hidx
  have hidx' : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, N.factorization p + 1 = l ^ γ :=
    fun p hp hpq => by obtain ⟨γ, -, hγ⟩ := hidx p hp hpq; exact ⟨γ, hγ⟩
  have hlN : l ∣ N := dvd_of_succ_eq_pow h hq hodd hl hl2 hidx'
  have hl1 : 1 ≤ N.factorization l := (hl.dvd_iff_one_le_factorization h.ne_zero).mp hlN
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  unfold primePowIndexWeight at hw hτ
  set S := primePowIndexReceivers N q l with hS
  set u := (primePowIndexSources N q l).card with hu
  have hsum : ∑ s ∈ S, N.factorization s ≤ S.card * B := by
    have := Finset.sum_le_card_nsmul S (fun r => N.factorization r) B fun r hr => by
      obtain ⟨hrN, hrq, hr1⟩ := mem_receivers.mp hr
      exact hB r hrN hrq hr1
    rwa [smul_eq_mul] at this
  have hSB : S.card * B ≤ B * B := Nat.mul_le_mul_right B (hSle.trans hBl)
  have h2u : 2 ^ u ≤ (l - 1) ^ u := Nat.pow_le_pow_left (by omega) _
  have hBB : B ^ 2 = B * B := by ring
  have huB : u ≤ B := by
    by_contra hlt
    obtain ⟨k, hk⟩ : ∃ k, u = B + 1 + k := ⟨u - (B + 1), by omega⟩
    have key := sq_add_lt_two_pow_add_two (B := B) (by omega)
    have hk2 : k < 2 ^ k := Nat.lt_two_pow_self
    have hsplit : 2 ^ u = 2 ^ (B + 1) * 2 ^ k := by rw [hk, pow_add]
    have hX : 2 ^ (B + 2) = 2 * 2 ^ (B + 1) := by ring
    have hXpos : 1 ≤ 2 ^ (B + 1) := Nat.one_le_two_pow
    have m1 : 2 ^ (B + 1) * (k + 1) ≤ 2 ^ (B + 1) * 2 ^ k := Nat.mul_le_mul_left _ hk2
    have m2 : k ≤ 2 ^ (B + 1) * k := Nat.le_mul_of_pos_left k hXpos
    nlinarith
  omega

/-- The size bound: under the hypotheses of `card_primeFactors_le_of_prime_pow_index_receivers`,
`N < 2 ^ (4 ^ (B ^ 2 + 2 B + 2))` (Nielsen's bound `N < 2 ^ (4 ^ ω(N))`). -/
theorem lt_two_pow_four_pow_of_prime_pow_index_receivers {N q l B : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, 1 ≤ γ ∧ N.factorization p + 1 = l ^ γ)
    (hBl : N.factorization l ≤ B)
    (hB : ∀ s ∈ N.primeFactors, s ≠ q → s % l = 1 → N.factorization s ≤ B) :
    N < 2 ^ (4 ^ (B ^ 2 + 2 * B + 2)) :=
  lt_of_lt_of_le (lt_two_pow_four_pow h)
    (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num)
      (card_primeFactors_le_of_prime_pow_index_receivers h hq hodd hl hl2 hidx hBl hB)))

end OddPerfect

#print axioms OddPerfect.card_primeFactors_le_of_prime_pow_index_weighted
#print axioms OddPerfect.two_mul_pred_pow_card_le
#print axioms OddPerfect.card_primeFactors_le_of_prime_pow_index_receivers
#print axioms OddPerfect.lt_two_pow_four_pow_of_prime_pow_index_receivers
