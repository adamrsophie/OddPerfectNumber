import OddPerfect.EqualExponentCount

/-!
# The counting checker under divisible indices

Restricted result; no published source was checked; novelty not verified.

Setting: `N` is an odd perfect number with special prime `q`, `l` is an odd prime with
`l ∣ N` and `l ≠ q`, every ordinary prime factor `p` of `N` (that is, `p ≠ q`) has
`l ∣ v_p(N) + 1`, and `v_l(N) = l - 1`. The hypothesis "every ordinary index `v_p(N) + 1` is
divisible by `l`" contains the equal exponent family `v_p(N) = l - 1`. The case `l ∤ N` is not
treated here.

Every accepted certificate of `EqCount.checkCert` refutes this setting (`checkCert_sound_div`).
The proof is the landed soundness proof with two changes.

* A counted number `m` divides `σ(p ^ (l - 1))`, and `σ(p ^ (l - 1))` divides `σ(p ^ v_p(N))`
  because `l ∣ v_p(N) + 1`; so its prime factors other than `2` divide `N`.
* Each ordinary prime factor `r ≡ 1 (mod l)` contributes at least `1` to the `l`-adic counting
  bound, since `l ∣ v_r(N) + 1`; so at most `v_l(N) = l - 1` of them exist.

As a consequence (`floor_of_checkCert`), without the hypothesis on `v_l(N)`, an accepted
certificate gives `3 l - 1 ≤ v_l(N)`: the exponent `v_l(N)` is even and `l ∣ v_l(N) + 1`, and
`v_l(N) + 1 = l` is excluded.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect.EqCount

open OddPerfect.Pratt (trialPrime_sound)
open OddPerfect.EqChain (dvd_sigma_of_gm isP_sound)

section SoundDiv

variable {l N q : ℕ}

/-- At most `v_l(N) = l - 1` ordinary prime factors are `1` modulo `l` when every ordinary
index is divisible by `l`; so at most `l` prime factors of `N` are `1` modulo `l`. -/
theorem card_filter_le_div (h : OddPerfect N) (hl : l.Prime) (hl2 : l ≠ 2)
    (hdiv : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1)
    (hE : N.factorization l = l - 1) :
    (N.primeFactors.filter (fun p => p % l = 1)).card ≤ l ∧
      (N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1)).card ≤ l - 1 := by
  have : Fact l.Prime := ⟨hl⟩
  have hs := sum_padicValNat_succ_le h.perfect hl hl2
  have hc2 : (N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1)).card ≤ l - 1 := by
    rw [Finset.card_eq_sum_ones, ← hE]
    calc ∑ _ ∈ N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1), 1
        ≤ ∑ p ∈ N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1),
            padicValNat l (N.factorization p + 1) := by
          refine Finset.sum_le_sum fun p hp => ?_
          obtain ⟨hpN, hpq, -⟩ := Finset.mem_filter.mp hp
          rw [Nat.padicValNat_def]
          exact one_le_multiplicity_of_dvd (by omega) (hdiv p hpN hpq)
      _ ≤ ∑ p ∈ N.primeFactors.filter (fun p => p % l = 1),
            padicValNat l (N.factorization p + 1) :=
          Finset.sum_le_sum_of_subset fun p hp => by
            obtain ⟨hpN, -, h1⟩ := Finset.mem_filter.mp hp
            exact Finset.mem_filter.mpr ⟨hpN, h1⟩
      _ ≤ N.factorization l := hs
  refine ⟨?_, hc2⟩
  have hsub : N.primeFactors.filter (fun p => p % l = 1) ⊆
      insert q (N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1)) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_insert, Finset.mem_filter]
    by_cases hxq : x = q
    · exact Or.inl hxq
    · exact Or.inr ⟨hx.1, hxq, hx.2⟩
  have := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have := hl.two_le
  omega

/-- Soundness of `run` under divisible indices: an accepted walk refutes every state that
holds. -/
theorem run_sound_div {pc : List (ℕ × ℕ × List ℕ)} (hpc : Pratt.check pc = true)
    (hl : l.Prime) (hl2 : l ≠ 2) (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hdiv : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1)
    (hE : N.factorization l = l - 1)
    (hlN : l ∈ N.primeFactors) (hlq : l ≠ q) {qs : Option ℕ} {ex : List ℕ}
    (hc : Ctx q qs ex) :
    ∀ (c : List (ℕ × ℕ × ℕ)) (P k : ℕ), run l pc qs ex P k c = true → Holds l N P k → False := by
  have hN := h.ne_zero
  have hq4 := (special_mod_four h hq hodd).1
  have hl1 : 1 < l := hl.one_lt
  intro c
  induction c with
  | nil =>
    intro P k hr hs
    obtain ⟨hP0, hPf, hk⟩ := hs
    have hsub : P.primeFactors ⊆ N.primeFactors.filter (fun p => p % l = 1) := by
      intro r hr
      rw [Finset.mem_filter]
      exact ⟨Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hr, (hPf r hr).1, hN⟩,
        (hPf r hr).2⟩
    obtain ⟨hc1, hc2⟩ := card_filter_le_div h hl hl2 hdiv hE
    have hk1 := hk.trans ((Finset.card_le_card hsub).trans hc1)
    simp only [run, finalOK, Bool.or_eq_true, decide_eq_true_eq] at hr
    rcases hr with hr | hr
    · omega
    · cases hqs : qs with
      | none => rw [hqs] at hr; exact absurd hr (by simp)
      | some Q =>
        rw [hqs] at hr
        simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hr
        obtain ⟨hlk, hPQ⟩ := hr
        rw [hc.1 Q hqs] at hPQ
        have hsub' : P.primeFactors ⊆ N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1) := by
          intro r hr
          rw [Finset.mem_filter]
          refine ⟨Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hr, (hPf r hr).1,
            hN⟩, ?_, (hPf r hr).2⟩
          rintro rfl
          exact hPQ (Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mem_primeFactors hr))
        have := hk.trans ((Finset.card_le_card hsub').trans hc2)
        omega
  | cons e rest ih =>
    obtain ⟨p, m, a⟩ := e
    intro P k hr hs
    simp only [run, Bool.and_eq_true] at hr
    obtain ⟨⟨hpar, hpiece⟩, hnext⟩ := hr
    -- the parent is an ordinary prime factor
    have hpo : p.Prime ∧ p ∈ N.primeFactors ∧ p ≠ q := by
      simp only [parentOK, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hpar
      rcases hpar with rfl | ⟨⟨hpP, hpd⟩, hpn⟩
      · exact ⟨hl, hlN, hlq⟩
      · have hpP' := isP_sound hpc hpP
        exact ⟨hpP', Nat.mem_primeFactors.mpr ⟨hpP', dvdOK_sound h hq hodd hc hs hpP' hpd, hN⟩,
          neqOK_sound hq4 hc hpn⟩
    obtain ⟨hpP, hpN, hpq⟩ := hpo
    simp only [pieceOK, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
      beq_iff_eq] at hpiece
    obtain ⟨⟨⟨⟨hm1, hml⟩, hgm⟩, hcop⟩, hw⟩ := hpiece
    have hmΦ0 : m ∣ σ 1 (p ^ (l - 1)) := dvd_sigma_of_gm hpP hl1.le hgm
    have hmΦ : m ∣ σ 1 (p ^ N.factorization p) :=
      hmΦ0.trans (OPNExample.sigma_prime_pow_dvd hpP
        (by rw [Nat.sub_add_cancel hl1.le]; exact hdiv p hpN hpq))
    have hm0 : m ≠ 0 := by omega
    have hcop' : Nat.Coprime m P := hcop
    refine ih (P * m) (k + weight a) hnext ⟨mul_ne_zero hs.1 hm0, fun r hr => ?_, ?_⟩
    · rw [Nat.primeFactors_mul hs.1 hm0, Finset.mem_union] at hr
      rcases hr with hr | hr
      · exact hs.2.1 r hr
      · have hrP := Nat.prime_of_mem_primeFactors hr
        have hrm := Nat.dvd_of_mem_primeFactors hr
        have hrl : r % l = 1 := by
          rcases prime_dvd_sigma_prime_pow_of_prime_length hpP hrP hl (hrm.trans hmΦ0)
            with h1 | h1
          · subst h1
            exact absurd (Nat.mod_eq_zero_of_dvd hrm) hml
          · exact h1
        have hr2 : r ≠ 2 := by
          rintro rfl
          rw [Nat.mod_eq_of_lt (by have := hl.two_le; omega)] at hrl
          omega
        exact ⟨OPNStarter.force_prime h.perfect hpP rfl hrP hr2 (hrm.trans hmΦ), hrl⟩
    · rw [Nat.Coprime.primeFactors_mul hcop'.symm, Finset.card_union_of_disjoint
        hcop'.symm.disjoint_primeFactors]
      have := weight_le hm1 hw
      have := hs.2.2
      omega

end SoundDiv

/-- Soundness of an accepted certificate under divisible indices: if `l ∣ N`, `l ≠ q`, every
ordinary index `v_p(N) + 1` is divisible by `l` and `v_l(N) = l - 1`, there is no odd perfect
number `N` with special prime `q`. -/
theorem checkCert_sound_div {l : ℕ} {pc : List (ℕ × ℕ × List ℕ)}
    {main : List (ℕ × ℕ × ℕ)} {cases : List (ℕ × List (ℕ × ℕ × ℕ))}
    (hc : checkCert l pc main cases = true) {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hdiv : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1)
    (hlN : l ∣ N) (hlq : l ≠ q) (hE : N.factorization l = l - 1) : False := by
  simp only [checkCert, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨hlP, hl2⟩, hpc⟩, hmain⟩, hcases⟩ := hc
  have hl := trialPrime_sound hlP
  have hlN' : l ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hl, hlN, h.ne_zero⟩
  have hs : Holds l N 1 0 := ⟨one_ne_zero, by simp, by simp⟩
  by_cases hqc : q ∈ cases.map Prod.fst
  · obtain ⟨⟨Q, c⟩, hmem, hQ⟩ := List.mem_map.mp hqc
    exact run_sound_div hpc hl hl2 h hq hodd hdiv hE hlN' hlq
      ⟨fun Q' hQ' => by rw [← Option.some.inj hQ']; exact hQ, by simp⟩ c 1 0
      (hcases _ hmem) hs
  · exact run_sound_div hpc hl hl2 h hq hodd hdiv hE hlN' hlq
      ⟨by simp, fun r hr hrq => hqc (hrq ▸ hr)⟩ main 1 0 hmain hs

/-- The landed `checkCert_sound_of_ne` in the case `l ∣ N`, recovered from
`checkCert_sound_div`. -/
theorem checkCert_sound_of_ne_of_dvd {l : ℕ} {pc : List (ℕ × ℕ × List ℕ)}
    {main : List (ℕ × ℕ × ℕ)} {cases : List (ℕ × List (ℕ × ℕ × ℕ))}
    (hc : checkCert l pc main cases = true) {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) (hlq : l ≠ q)
    (hlN : l ∣ N) : False := by
  have hl1 := (checkCert_prime hc).1.one_lt
  have hlN' : l ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨(checkCert_prime hc).1, hlN, h.ne_zero⟩
  exact checkCert_sound_div hc h hq hodd
    (fun p hp hpq => by rw [hexp p hp hpq, Nat.sub_add_cancel hl1.le]) hlN hlq
    (hexp l hlN' hlq)

/-- The exponent floor: under divisible indices, with `l ∣ N` and `l ≠ q`, an accepted
certificate gives `3 l - 1 ≤ v_l(N)`. -/
theorem floor_of_checkCert {l : ℕ} {pc : List (ℕ × ℕ × List ℕ)}
    {main : List (ℕ × ℕ × ℕ)} {cases : List (ℕ × List (ℕ × ℕ × ℕ))}
    (hc : checkCert l pc main cases = true) {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hdiv : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1)
    (hlN : l ∣ N) (hlq : l ≠ q) : 3 * l - 1 ≤ N.factorization l := by
  obtain ⟨hl, hl2⟩ := checkCert_prime hc
  have hlN' : l ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hl, hlN, h.ne_zero⟩
  obtain ⟨r, hr⟩ := even_factorization_of_ne h hq hodd hl hlq
  obtain ⟨t, ht⟩ := hdiv l hlN' hlq
  have hlo : l % 2 = 1 := Nat.odd_iff.mp (hl.odd_of_ne_two hl2)
  have hl1 := hl.one_lt
  by_contra hlt
  have hlt' : N.factorization l + 2 ≤ 3 * l := by omega
  have ht3 : t < 3 := by
    by_contra h3
    push Not at h3
    nlinarith
  interval_cases t
  · omega
  · exact checkCert_sound_div hc h hq hodd hdiv hlN hlq (by omega)
  · omega

/-- The exponent floor for `l ≡ 3 (mod 4)`: then `l` is not the special prime. -/
theorem floor_of_checkCert_mod_four {l : ℕ} {pc : List (ℕ × ℕ × List ℕ)}
    {main : List (ℕ × ℕ × ℕ)} {cases : List (ℕ × List (ℕ × ℕ × ℕ))}
    (hc : checkCert l pc main cases = true) (hl4 : l % 4 = 3) {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hdiv : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1)
    (hlN : l ∣ N) : 3 * l - 1 ≤ N.factorization l :=
  floor_of_checkCert hc h hq hodd hdiv hlN fun hlq => by
    have := (special_mod_four h hq hodd).1
    omega

end OddPerfect.EqCount

#print axioms OddPerfect.EqCount.card_filter_le_div
#print axioms OddPerfect.EqCount.run_sound_div
#print axioms OddPerfect.EqCount.checkCert_sound_div
#print axioms OddPerfect.EqCount.checkCert_sound_of_ne_of_dvd
#print axioms OddPerfect.EqCount.floor_of_checkCert
#print axioms OddPerfect.EqCount.floor_of_checkCert_mod_four
