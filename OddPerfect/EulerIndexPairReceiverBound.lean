import OddPerfect.EulerIndexPairFrame
import OddPerfect.EulerIndexPairEmitters
import OddPerfect.EulerIndexPairRows
import OddPerfect.PureRows
import OddPerfect.NagellPrime
import OddPerfect.Abundancy
import OddPerfect.EulerIndexPairReceiverSieve

/-!
# Two prime Euler index, branch `v = 1`: the receiver is at least 43

Restricted result; no published source was checked; novelty not verified.

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly the two prime factors
`r ≠ s`, oriented by a frame `PairFrame N q r s t u`. In the branch `v = 1`, that is
`σ(t ^ e) = q * u` with `e = v_t(N)`:

* `PairFrame.receiver_not_three_dvd`: `3 ∤ N`.
* `PairFrame.receiver_card_le`: `ω(N) ≤ u + 1 + z`, where `z` counts the outsiders (prime
  factors other than `q, t, u`) whose row `σ(p ^ e_p)` is prime to `t`.
* `PairFrame.receiver_pure_outsider`: for `u` in `sieveU`, such an outsider forces
  `u = 31` and `p = 5`.
* `PairFrame.receiver_absent`: for a row `(u, z, A, L)` of `ReceiverSieve.sieveTable`, no
  prime of `A` divides `N`.
* `PairFrame.receiver_ge`: `43 ≤ u` and `u ≠ 47`; `eulerIndex_pair_receiver_ge` is the form
  without a frame.

The family is not excluded by this. The odd perfect number conjecture is open, and nothing
here decides it.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

open ReceiverSieve

/-- The receivers of the sieve table. -/
def sieveU : List ℕ := [11, 13, 17, 19, 23, 29, 31, 37, 41, 47]

theorem sieveU_eq : sieveU = sieveTable.map Prod.fst := by decide +kernel

/-- Table facts: each listed prime is below its receiver, and `z ≥ 1` at `u = 31`. -/
theorem sieveTable_facts :
    sieveTable.all (fun r => (r.1 != 31 || decide (1 ≤ r.2.1)) &&
      (r.2.2.1.map Prod.fst).all (fun p => decide (p < r.1))) = true := by
  decide +kernel

/-- The odd primes `ℓ ∣ u - 1` for the receivers of the table. -/
theorem sieveU_lengths : ∀ u ∈ sieveU, ∀ ℓ < u, ℓ.Prime → 3 ≤ ℓ → u % ℓ = 1 →
    (u, ℓ) ∈ [(11, 5), (13, 3), (19, 3), (23, 11), (29, 7), (31, 3), (31, 5), (37, 3),
      (41, 5), (47, 23)] := by
  intro u hu
  simp only [sieveU, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact @of_decide_eq_true _ (@Nat.decidableBallLT _ _ fun _ _ => inferInstance)
      (by decide +kernel)

/-- The primes in `[11, 47]` other than 43 are the receivers of the table. -/
theorem mem_sieveU : ∀ u < 48, u.Prime → 11 ≤ u → u ≠ 43 → u ∈ sieveU :=
  @of_decide_eq_true _ (@Nat.decidableBallLT 48 _ fun _ _ => inferInstance) (by decide +kernel)

theorem lt_of_mod_eq_one {a u : ℕ} (ha : a.Prime) (h : a % u = 1) : u < a := by
  by_contra hle
  push Not at hle
  rcases lt_or_eq_of_le hle with hlt | rfl
  · rw [Nat.mod_eq_of_lt hlt] at h; exact ha.ne_one h
  · rw [Nat.mod_self] at h; exact absurd h (by omega)

theorem five_le_of_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) : 5 ≤ p := by
  by_contra hc
  push Not at hc
  interval_cases p <;> first | exact absurd rfl h2 | exact absurd rfl h3 | norm_num at hp

theorem pow_odd_mod_four {a w : ℕ} (ha : a % 4 = 3) (hw : Odd w) : a ^ w % 4 = 3 := by
  obtain ⟨k, rfl⟩ := hw
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, pow_add, Nat.mul_mod, ih, Nat.pow_mod,
      ha]

theorem geom_sum_five_mod_four {p : ℕ} (hp : Odd p) : (∑ i ∈ range 5, p ^ i) % 4 = 1 := by
  have h := Nat.odd_iff.mp hp
  rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h1 | h3
  · rw [geom_sum_mod_four_of_one h1]
  · exact geom_sum_mod_four_of_three h3 (by decide)

variable {N q m r s t u : ℕ}

namespace PairFrame

/-- The basic facts of the branch `v = 1` for a frame. -/
theorem vOne_basic (F : PairFrame N q r s t u) (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s})
    (hv : σ 1 (t ^ N.factorization t) = q * u) :
    u = N.factorization t + 1 ∧ 11 ≤ u ∧ t % u = 1 ∧ q % u = 1 ∧
      ∑ i ∈ range u, t ^ i = q * u ∧ u < t ∧ u < q ∧ N.factorization q = 1 ∧
      (∃ j, 0 < j ∧ Odd j ∧ ∑ i ∈ range (N.factorization u + 1), u ^ i = t ^ j) ∧
      Even (N.factorization u) := by
  obtain ⟨ht, ht2, v', j', hA', hj0, hjo, hret, -, -, -, hbr⟩ :=
    F.emitter_ten_all h hq hN hqm hr hs hrs hJ
  have hv1 : 1 = v' := F.v_eq hq (by rw [pow_one]; exact hv) hA'
  rcases hbr with ⟨hv0, -⟩ | ⟨-, hue, hu11, htu, hqu, -⟩
  · omega
  have hu := F.u_prime
  have hR : ∑ i ∈ range u, t ^ i = q * u := by
    have := hv
    rw [sigma_one_apply_prime_pow ht, ← hue] at this
    exact this
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hvq : N.factorization q = 1 := by
    rw [hN, Nat.factorization_mul hq.ne_zero (pow_ne_zero _ hm), Finsupp.add_apply,
      hq.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (fun hd => hqm (hq.dvd_of_dvd_pow hd))]
  have hf0 : N.factorization u ≠ 0 := by
    intro h0
    rw [h0, sigma_one_apply_prime_pow hu, zero_add, sum_range_one, pow_zero] at hret
    exact absurd hret.symm (Nat.one_lt_pow hj0.ne' ht.one_lt).ne'
  have hfe := (sigma_prime_pow_eq_prime_pow_row hu (by omega) ht ht2 hf0 hret).1
  refine ⟨hue, hu11, htu, hqu, hR, lt_of_mod_eq_one ht htu, lt_of_mod_eq_one hq hqu, hvq,
    ⟨j', hj0, hjo, ?_⟩, hfe⟩
  rw [← sigma_one_apply_prime_pow hu]; exact hret

/-- The outsiders of the frame are the prime factors other than `q, t, u`. -/
theorem mem_outsider (F : PairFrame N q r s t u) {p : ℕ} :
    p ∈ N.primeFactors \ {q, r, s} ↔ p ∈ N.primeFactors ∧ p ≠ q ∧ p ≠ t ∧ p ≠ u := by
  have : ({q, r, s} : Finset ℕ) = {q, t, u} := by
    rw [show ({q, r, s} : Finset ℕ) = insert q {r, s} from rfl, ← F.pair]
  rw [this]
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]

/-- In the branch `v = 1`, `3 ∤ N`. -/
theorem receiver_not_three_dvd (F : PairFrame N q r s t u) (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s})
    (hv : σ 1 (t ^ N.factorization t) = q * u) : ¬ 3 ∣ N := by
  obtain ⟨-, hu11, -, -, hR, hut, huq, -, ⟨j, -, hjo, hret⟩, hfe⟩ :=
    F.vOne_basic h hq hN hqm hr hs hrs hJ hv
  have hq3 := mod_three_of_receiver F.u_prime (by omega) hR hret hfe hjo
  intro h3
  have h3N : 3 ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, h.2.2.ne'⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hout, -⟩ := F.cofactor h hq hN hqm hr hs hrs hJ
  obtain ⟨-, hdvd, -⟩ := hout 3 h3N (by omega) (by omega) (by omega)
  have he3 : N.factorization 3 ≠ 0 :=
    (Nat.prime_three.factorization_pos_of_dvd h.2.2.ne' h3).ne'
  have := (dvd_pow_self 3 he3).trans hdvd
  omega

/-- Support cap in the branch `v = 1`: `ω(N) ≤ u + 1 + z`, where `z` counts the outsiders
whose row is prime to `t`. -/
theorem receiver_card_le (F : PairFrame N q r s t u) (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s})
    (hv : σ 1 (t ^ N.factorization t) = q * u) :
    N.primeFactors.card ≤ u + 1 +
      ((N.primeFactors \ {q, r, s}).filter fun p => ¬ t ∣ σ 1 (p ^ N.factorization p)).card := by
  obtain ⟨hue, hu11, -⟩ := F.vOne_basic h hq hN hqm hr hs hrs hJ hv
  obtain ⟨-, -, -, j, hj0, -, -, hled, -⟩ := F.t_count h hq hN hqm hr hs hrs hJ
  set O := N.primeFactors \ {q, r, s}
  set x : ℕ → ℕ := fun p => (σ 1 (p ^ N.factorization p)).factorization t
  have h1 : (O.filter fun p => t ∣ σ 1 (p ^ N.factorization p)).card ≤ ∑ p ∈ O, x p := by
    rw [card_eq_sum_ones]
    refine le_trans (sum_le_sum fun p hp => ?_) (sum_le_sum_of_subset (filter_subset _ _))
    have hpt := (mem_filter.mp hp).2
    have hpos : σ 1 (p ^ N.factorization p) ≠ 0 :=
      (ArithmeticFunction.sigma_pos 1 _ (pow_ne_zero _ (Nat.pos_of_mem_primeFactors
        (mem_sdiff.mp (mem_filter.mp hp).1).1).ne')).ne'
    exact F.t_prime.factorization_pos_of_dvd hpos hpt
  have h2 := card_filter_add_card_filter_not (s := O)
    (fun p => t ∣ σ 1 (p ^ N.factorization p))
  have h3 : N.primeFactors.card ≤ O.card + 3 :=
    le_trans card_le_card_sdiff_add_card (Nat.add_le_add_left card_le_three _)
  have h4 : ∑ p ∈ O, x p ≤ u - 2 := by
    have : N.factorization t = j + ∑ p ∈ O, x p := hled
    omega
  omega

/-- Pure rows into `u`: for `u` a receiver of the table, an outsider whose row is prime to
`t` forces `u = 31` and `p = 5`. -/
theorem receiver_pure_outsider (F : PairFrame N q r s t u) (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s})
    (hv : σ 1 (t ^ N.factorization t) = q * u) (huU : u ∈ sieveU) {p : ℕ}
    (hp : p ∈ N.primeFactors \ {q, r, s}) (hpt : ¬ t ∣ σ 1 (p ^ N.factorization p)) :
    u = 31 ∧ p = 5 := by
  obtain ⟨-, hu11, -, -, -, -, -, hvq, -⟩ := F.vOne_basic h hq hN hqm hr hs hrs hJ hv
  have h3 := F.receiver_not_three_dvd h hq hN hqm hr hs hrs hJ hv
  have hu := F.u_prime
  obtain ⟨hpN, hpq, hpt', hpu⟩ := F.mem_outsider.mp hp
  obtain ⟨-, -, -, -, -, -, -, -, -, hout, -⟩ := F.cofactor h hq hN hqm hr hs hrs hJ
  obtain ⟨⟨x, y, hrow⟩, -, -⟩ := hout p hpN hpq hpt' hpu
  have hpp := Nat.prime_of_mem_primeFactors hpN
  have hpd := Nat.dvd_of_mem_primeFactors hpN
  have hp2 : p ≠ 2 := by rintro rfl; exact h.not_two_dvd hpd
  have hp3 : p ≠ 3 := by rintro rfl; exact h3 hpd
  have hp5 : 5 ≤ p := five_le_of_prime hpp hp2 hp3
  have hx0 : x = 0 := by
    by_contra hx
    exact hpt (by rw [hrow]; exact Dvd.dvd.mul_right (dvd_pow_self t hx) _)
  rw [hx0, pow_zero, one_mul] at hrow
  set g := N.factorization p
  have hge : Even g := even_factorization_of_ne h hq (by rw [hvq]; exact odd_one) hpp hpq
  have hg0 : g ≠ 0 := (hpp.factorization_pos_of_dvd h.2.2.ne' hpd).ne'
  have hl := prime_succ_of_sigma_prime_pow_eq_prime_pow hpp hp2 hge hg0 hu hrow
  have hmod := receiver_mod_index_of_pure hpp hp2 (by obtain ⟨k, hk⟩ := hge; omega) hu hrow
  have hy : Odd y := by
    rcases odd_weight_or_three_pow_four hpp hp2 hge hg0 hu hrow with hy | ⟨rfl, -⟩
    · exact hy
    · exact absurd rfl hp3
  have hlu : g + 1 < u := by
    by_contra hc
    push Not at hc
    rcases lt_or_eq_of_le hc with hc | hc
    · rw [Nat.mod_eq_of_lt hc] at hmod; omega
    · rw [← hc, Nat.mod_self] at hmod; omega
  have hsum : ∑ i ∈ range (g + 1), p ^ i = u ^ y := by
    rw [← sigma_one_apply_prime_pow hpp]; exact hrow
  have hmem := sieveU_lengths u huU (g + 1) hlu hl (by obtain ⟨k, hk⟩ := hge; omega) hmod
  have hy1 : 1 ≤ y := by obtain ⟨k, rfl⟩ := hy; omega
  have hpodd : Odd p := hpp.odd_of_ne_two hp2
  have phi : ∀ U : ℕ, U.Prime → u = U → g + 1 = 3 → p ^ 2 + p + 1 = U := by
    intro U hU hUu hg3
    rw [hg3] at hsum
    have hphi : phi3 p = u ^ y := by
      rw [phi3, ← hsum]
      simp only [sum_range_succ, sum_range_zero, pow_zero, pow_one]
      ring
    rw [hUu] at hphi
    have := phi3_eq_prime_pow_exponent hU hpp hy1 hphi
    rw [this, pow_one, phi3] at hphi
    exact hphi
  have four : ∀ U : ℕ, u = U → U % 4 = 3 → g + 1 = 5 → False := by
    intro U hUu hU4 hg5
    rw [hg5, hUu] at hsum
    have := pow_odd_mod_four hU4 hy
    rw [← hsum, geom_sum_five_mod_four hpodd] at this
    omega
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact (four 11 h1 (by norm_num) h2).elim
  · have := phi 13 (by norm_num) h1 h2
    have : p ≤ 3 := by nlinarith
    omega
  · have := phi 19 (by norm_num) h1 h2
    have : p ≤ 4 := by nlinarith
    omega
  · rw [h2, h1] at hsum
    exact (geom_sum_eleven_ne_twentythree_pow p hy hsum).elim
  · rw [h2, h1] at hsum
    exact (geom_sum_seven_ne_twentynine_pow p hy hsum).elim
  · have := phi 31 (by norm_num) h1 h2
    have : p ≤ 5 := by nlinarith
    exact ⟨h1, by omega⟩
  · exact (four 31 h1 (by norm_num) h2).elim
  · have h37 := phi 37 (by norm_num) h1 h2
    have : p ≤ 5 := by nlinarith
    have hp5' : p = 5 := by omega
    rw [hp5'] at h37
    norm_num at h37
  · rw [h2, h1] at hsum
    exact (geom_sum_five_ne_fortyone_pow p hy hsum).elim
  · rw [h2, h1] at hsum
    exact (geom_sum_twentythree_ne_fortyseven_pow p hy hsum).elim

/-- For a row `(u, z, A, L)` of the sieve table, no prime of `A` divides `N`. -/
theorem receiver_absent (F : PairFrame N q r s t u) (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s})
    (hv : σ 1 (t ^ N.factorization t) = q * u) {z : ℕ} {A : List (ℕ × List ℕ)} {L : List ℕ}
    (hrow : (u, z, A, L) ∈ sieveTable) {p : ℕ} (hpA : p ∈ A.map Prod.fst) :
    p ∉ N.primeFactors := by
  intro hpN
  obtain ⟨-, -, htu, -, hR, hut, huq, hvq, -⟩ := F.vOne_basic h hq hN hqm hr hs hrs hJ hv
  have hfacts := List.all_eq_true.mp sieveTable_facts _ hrow
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hfacts
  have hpu : p < u := hfacts.2 p hpA
  obtain ⟨pr, hprA, rfl⟩ := List.mem_map.mp hpA
  have hspec := ((sieveTable_spec hrow).1 pr hprA)
  have h3 := F.receiver_not_three_dvd h hq hN hqm hr hs hrs hJ hv
  obtain ⟨-, -, -, -, -, -, -, -, -, hout, -⟩ := F.cofactor h hq hN hqm hr hs hrs hJ
  obtain ⟨⟨x, y, hrw⟩, hdq, -⟩ := hout pr.1 hpN (by omega) (by omega) (by omega)
  have hpp := Nat.prime_of_mem_primeFactors hpN
  have hpd := Nat.dvd_of_mem_primeFactors hpN
  have hp2 : pr.1 ≠ 2 := by rintro h2; rw [h2] at hpd; exact h.not_two_dvd hpd
  have hp3 : pr.1 ≠ 3 := by rintro h3'; rw [h3'] at hpd; exact h3 hpd
  set g := N.factorization pr.1
  have hge : Even g := even_factorization_of_ne h hq (by rw [hvq]; exact odd_one) hpp
    (by omega)
  have hg0 : g ≠ 0 := (hpp.factorization_pos_of_dvd h.2.2.ne' hpd).ne'
  have hsum : ∑ i ∈ range (g + 1), pr.1 ^ i = t ^ x * u ^ y := by
    rw [← sigma_one_apply_prime_pow hpp]; exact hrw
  rcases Nat.eq_zero_or_pos y with hy0 | hy
  · rw [hy0, pow_zero, mul_one] at hrw hsum
    have hx : Odd x := by
      rcases odd_weight_or_three_pow_four hpp hp2 hge hg0 F.t_prime hrw with hx | ⟨h3', -⟩
      · exact hx
      · exact absurd h3' hp3
    exact pureOK_spec hpp hspec.2 (Nat.succ_pos g) hx hsum
      ((dvd_pow_self _ hg0).trans hdq) hR
  · exact mixedOK_spec F.u_prime hspec.1 F.t_prime htu hge.add_one hy hsum

/-- In the branch `v = 1`: `43 ≤ u` and `u ≠ 47`. -/
theorem receiver_ge (F : PairFrame N q r s t u) (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s})
    (hv : σ 1 (t ^ N.factorization t) = q * u) : 43 ≤ u ∧ u ≠ 47 := by
  obtain ⟨-, hu11, -⟩ := F.vOne_basic h hq hN hqm hr hs hrs hJ hv
  by_contra hc
  have huU : u ∈ sieveU := by
    rcases Nat.lt_or_ge u 48 with hlt | hge
    · exact mem_sieveU u hlt F.u_prime hu11 (by omega)
    · exfalso; omega
  have huU' := huU
  rw [sieveU_eq] at huU'
  obtain ⟨⟨u', z, A, L⟩, hrow, hu'⟩ := List.mem_map.mp huU'
  simp only at hu'
  subst hu'
  have h3 := F.receiver_not_three_dvd h hq hN hqm hr hs hrs hJ hv
  have hP : ∀ p ∈ N.primeFactors, p.Prime ∧ 5 ≤ p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    refine ⟨hpp, five_le_of_prime hpp ?_ ?_⟩
    · rintro rfl; exact h.not_two_dvd hpd
    · rintro rfl; exact h3 hpd
  have hPA : ∀ p ∈ N.primeFactors, p ∉ A.map Prod.fst := fun p hp hpA =>
    F.receiver_absent h hq hN hqm hr hs hrs hJ hv hrow hpA hp
  have hfacts := List.all_eq_true.mp sieveTable_facts _ hrow
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, List.all_eq_true,
    decide_eq_true_eq] at hfacts
  have hz : ((N.primeFactors \ {q, r, s}).filter
      fun p => ¬ t ∣ σ 1 (p ^ N.factorization p)).card ≤ z := by
    have hpure : ∀ p ∈ (N.primeFactors \ {q, r, s}).filter
        (fun p => ¬ t ∣ σ 1 (p ^ N.factorization p)), u' = 31 ∧ p = 5 := fun p hp =>
      F.receiver_pure_outsider h hq hN hqm hr hs hrs hJ hv huU (mem_filter.mp hp).1
        (mem_filter.mp hp).2
    by_cases h31 : u' = 31
    · have hz1 : 1 ≤ z := hfacts.1.resolve_left (by simpa using h31)
      have hsub : (N.primeFactors \ {q, r, s}).filter
          (fun p => ¬ t ∣ σ 1 (p ^ N.factorization p)) ⊆ {5} := fun p hp => by
        rw [Finset.mem_singleton]; exact (hpure p hp).2
      exact le_trans (card_le_card hsub) (by simpa using hz1)
    · rw [Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun p hp =>
        h31 (hpure p hp).1)]
      exact Nat.zero_le _
  have hcard := F.receiver_card_le h hq hN hqm hr hs hrs hJ hv
  have hlt := (sieveTable_spec hrow).2 N.primeFactors hP hPA (by omega)
  have hN1 : 1 < N := by
    have hqN : q ∣ N := by rw [hN]; exact dvd_mul_right q _
    exact lt_of_lt_of_le hq.one_lt (Nat.le_of_dvd h.2.2 hqN)
  exact not_perfect_of_prod_le_two hN1 hlt.le h.2

end PairFrame

/-- The family form: in the two prime Euler index family, the oriented pair `(t, u)` satisfies,
in the branch `v = 1`, `3 ∤ N`, `43 ≤ u` and `u ≠ 47`. -/
theorem eulerIndex_pair_receiver_ge (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧
      (∃ v, σ 1 (t ^ N.factorization t) = q * u ^ v) ∧
      (σ 1 (t ^ N.factorization t) = q * u → ¬ 3 ∣ N ∧ 43 ≤ u ∧ u ≠ 47) := by
  obtain ⟨t, u, F⟩ := exists_pairFrame h hq hN hqm hr hs hrs hJ
  exact ⟨t, u, F.pair, F.ne, F.emit, fun hv =>
    ⟨F.receiver_not_three_dvd h hq hN hqm hr hs hrs hJ hv,
      F.receiver_ge h hq hN hqm hr hs hrs hJ hv⟩⟩

end OddPerfect

#print axioms OddPerfect.sieveU_eq
#print axioms OddPerfect.sieveTable_facts
#print axioms OddPerfect.sieveU_lengths
#print axioms OddPerfect.mem_sieveU
#print axioms OddPerfect.lt_of_mod_eq_one
#print axioms OddPerfect.five_le_of_prime
#print axioms OddPerfect.pow_odd_mod_four
#print axioms OddPerfect.geom_sum_five_mod_four
#print axioms OddPerfect.PairFrame.vOne_basic
#print axioms OddPerfect.PairFrame.mem_outsider
#print axioms OddPerfect.PairFrame.receiver_not_three_dvd
#print axioms OddPerfect.PairFrame.receiver_card_le
#print axioms OddPerfect.PairFrame.receiver_pure_outsider
#print axioms OddPerfect.PairFrame.receiver_absent
#print axioms OddPerfect.PairFrame.receiver_ge
#print axioms OddPerfect.eulerIndex_pair_receiver_ge
