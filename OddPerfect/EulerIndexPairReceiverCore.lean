import OddPerfect.EulerIndexPairReceiverBound

/-!
# Two prime Euler index, branch `v = 1`: the frame of the receiver packing

Restricted result; no published source was checked; novelty not verified. The odd perfect
number conjecture remains open.

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly the two prime factors
`r ≠ s`, oriented by a frame `PairFrame N q r s t u`. In the branch `v = 1`, that is
`σ(t ^ e) = q * u` with `e = v_t(N)`:

* `PairFrame.absent_of_tests`: a prime accepted by the mixed and the pure test, other than
  `u` and not `1` modulo `u`, does not divide `N` (also above the receiver).
* `PairFrame.pure_outsider_row`: an outsider whose row is prime to `t` has an odd prime row
  length `d` with `u ≡ 1 (mod d)` and row `R_d(p) = u ^ w`, `w` odd.
* `PairFrame.core_card_le`: removing the pure outsiders outside a set `C` leaves at most
  `u + 1 + #C` prime factors.
* `ReceiverSieve.keptLengths`, `ReceiverSieve.packRow`: the computed set of pure row lengths
  and the certificate of one receiver.
* `PairFrame.false_of_packRow_of_tail`: an accepted certificate is impossible, given the
  center statement for pure rows into a common receiver as a hypothesis.

Each receiver needs its own finite certificate; no uniform statement over all receivers is
proved. The branch `v = 0` and the family are not excluded.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

open ReceiverSieve

/-- A geometric sum of length `1 (mod 4)` with odd base is `1 (mod 4)`. -/
theorem geom_sum_mod_four_of_len_one {p d : ℕ} (hp : Odd p) (hd : d % 4 = 1) :
    (∑ i ∈ range d, p ^ i) % 4 = 1 := by
  have h := Nat.odd_iff.mp hp
  rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h1 | h3
  · rw [geom_sum_mod_four_of_one h1, hd]
  · exact geom_sum_mod_four_of_three h3 (Nat.odd_iff.mpr (by omega))

namespace ReceiverSieve

/-- The pure row lengths that the two cheap rules do not discharge. Computed, never supplied. -/
def keptLengths (u : ℕ) : List ℕ :=
  (List.range u).filter fun d => decide (3 ≤ d) && decide d.Prime && u % d == 1 &&
    !(d == 3 && (List.range u).all fun p => p % 2 == 0 || p * p + p + 1 != u) &&
    !(u % 4 == 3 && d % 4 == 1)

/-- One receiver certificate: absent primes with their tests, the envelope of the core, and
the envelope times the tail factors below 2. -/
def packRow (u : ℕ) (A : List (ℕ × List ℕ)) (L : List ℕ) : Bool :=
  A.all (fun pr => mixedOK u pr.1 pr.2 && pureOK u pr.1 && pr.1 != u && pr.1 % u != 1) &&
    envOK (A.map Prod.fst) 5 L && L.length == u + 1 + (keptLengths u).length &&
    decide (L.prod * ((keptLengths u).map fun d => 5 ^ (d - 1) - 1).prod <
      2 * (L.map fun b => b - 1).prod * ((keptLengths u).map fun d => 5 ^ (d - 1) - 2).prod)

/-- The absent prime tests of a certificate, as a separate function (used to split kernel
checks into pieces). -/
def absentOK (u : ℕ) (A : List (ℕ × List ℕ)) : Bool :=
  A.all fun pr => mixedOK u pr.1 pr.2 && pureOK u pr.1 && pr.1 != u && pr.1 % u != 1

/-- The length and inequality part of a certificate. -/
def tailOK (u : ℕ) (L : List ℕ) : Bool :=
  L.length == u + 1 + (keptLengths u).length &&
    decide (L.prod * ((keptLengths u).map fun d => 5 ^ (d - 1) - 1).prod <
      2 * (L.map fun b => b - 1).prod * ((keptLengths u).map fun d => 5 ^ (d - 1) - 2).prod)

/-- The lower end after an envelope segment. -/
def envNext (lo : ℕ) (L : List ℕ) : ℕ := L.foldl (fun _ b => b + 1) lo

/-- A certificate from its three parts. -/
theorem packRow_of_parts {u : ℕ} {A : List (ℕ × List ℕ)} {L : List ℕ}
    (h1 : absentOK u A = true) (h2 : envOK (A.map Prod.fst) 5 L = true)
    (h3 : tailOK u L = true) : packRow u A L = true := by
  unfold absentOK at h1
  unfold tailOK at h3
  unfold packRow
  simp only [h1, h2, Bool.true_and]
  exact h3

/-- The absent tests split along a list append. -/
theorem absentOK_append {u : ℕ} {A₁ A₂ : List (ℕ × List ℕ)} (h1 : absentOK u A₁ = true)
    (h2 : absentOK u A₂ = true) : absentOK u (A₁ ++ A₂) = true := by
  unfold absentOK at *
  rw [List.all_append, h1, h2, Bool.true_and]

/-- The envelope test splits along a list append. -/
theorem envOK_append (A : List ℕ) (lo : ℕ) (L₁ L₂ : List ℕ) :
    envOK A lo (L₁ ++ L₂) = (envOK A lo L₁ && envOK (L₁.reverse ++ A) (envNext lo L₁) L₂) := by
  induction L₁ generalizing A lo with
  | nil => simp [envOK, envNext]
  | cons b L₁ ih =>
    simp only [List.cons_append, envOK, ih, envNext, List.foldl_cons, List.reverse_cons,
      List.append_assoc, List.cons_append, List.nil_append, Bool.and_assoc]

theorem envOK_of_append {A : List ℕ} {lo : ℕ} {L₁ L₂ : List ℕ} (h1 : envOK A lo L₁ = true)
    (h2 : envOK (L₁.reverse ++ A) (envNext lo L₁) L₂ = true) : envOK A lo (L₁ ++ L₂) = true := by
  rw [envOK_append, h1, h2, Bool.true_and]

/-- The facts carried by a kept length. -/
theorem keptLengths_facts {u d : ℕ} (h : d ∈ keptLengths u) : d < u ∧ 3 ≤ d ∧ d.Prime := by
  unfold keptLengths at h
  rw [List.mem_filter] at h
  obtain ⟨hmem, hb⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  exact ⟨List.mem_range.mp hmem, hb.1.1.1.1, hb.1.1.1.2⟩

/-- A length that passes both discharge rules is kept. -/
theorem mem_keptLengths_of {u d : ℕ} (hdu : d < u) (hd3 : 3 ≤ d) (hd : d.Prime)
    (hud : u % d = 1) (h3 : d = 3 → ∃ p < u, p % 2 = 1 ∧ p * p + p + 1 = u)
    (h4 : ¬ (u % 4 = 3 ∧ d % 4 = 1)) : d ∈ keptLengths u := by
  unfold keptLengths
  rw [List.mem_filter]
  refine ⟨List.mem_range.mpr hdu, ?_⟩
  have e1 : (d == 3 && (List.range u).all fun p => p % 2 == 0 || p * p + p + 1 != u) =
      false := by
    by_cases h : d = 3
    · obtain ⟨p, hpu, hp2, hpe⟩ := h3 h
      have hall : ¬ ((List.range u).all fun p => p % 2 == 0 || p * p + p + 1 != u) = true := by
        rw [List.all_eq_true]
        intro hc
        have := hc p (List.mem_range.mpr hpu)
        simp [hp2, hpe] at this
      rw [Bool.eq_false_iff.mpr hall, Bool.and_false]
    · simp [h]
  have e2 : (u % 4 == 3 && d % 4 == 1) = false := by
    by_cases h : u % 4 = 3
    · have : d % 4 ≠ 1 := fun h' => h4 ⟨h, h'⟩
      simp [h, this]
    · simp [h]
  rw [e1, e2]
  simp [hd3, hd, hud]

/-- The kept lengths have no duplicates. -/
theorem keptLengths_nodup (u : ℕ) : (keptLengths u).Nodup :=
  List.Nodup.filter _ List.nodup_range

/-- The tail factors as a quotient of two natural products. -/
theorem tail_prod_eq {K : List ℕ} (hK : ∀ d ∈ K, 2 ≤ d) :
    (K.map fun d => ((5 : ℚ) ^ (d - 1) - 1) / ((5 : ℚ) ^ (d - 1) - 2)).prod =
      (((K.map fun d => 5 ^ (d - 1) - 1).prod : ℕ) : ℚ) /
        (((K.map fun d => 5 ^ (d - 1) - 2).prod : ℕ) : ℚ) := by
  induction K with
  | nil => simp
  | cons d K ih =>
    have hd := hK d (by simp)
    have h5 : 5 ≤ 5 ^ (d - 1) :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 1 ≤ d - 1))
    simp only [List.map_cons, List.prod_cons]
    rw [ih fun c hc => hK c (by simp [hc]), div_mul_div_comm, Nat.cast_mul, Nat.cast_mul,
      Nat.cast_sub (by omega : 1 ≤ 5 ^ (d - 1)), Nat.cast_sub (by omega : 2 ≤ 5 ^ (d - 1))]
    simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]

/-- A product of factors at least 1 grows with the index set. -/
theorem prod_le_prod_of_subset_one_le {s t : Finset ℕ} {f : ℕ → ℚ} (hst : s ⊆ t)
    (hf : ∀ p ∈ t, 1 ≤ f p) : ∏ p ∈ s, f p ≤ ∏ p ∈ t, f p := by
  rw [← prod_sdiff hst]
  have h1 : (1 : ℚ) ≤ ∏ p ∈ t \ s, f p := by
    have := prod_le_prod₀ (s := t \ s) (f := fun _ => (1 : ℚ)) (fun _ _ => zero_le_one)
      (fun p hp => hf p (mem_sdiff.mp hp).1)
    simpa using this
  have h0 : (0 : ℚ) ≤ ∏ p ∈ s, f p :=
    prod_nonneg fun p hp => le_trans zero_le_one (hf p (hst hp))
  exact le_mul_of_one_le_left h0 h1

end ReceiverSieve

variable {N q m r s t u : ℕ}

namespace PairFrame

/-- absent prime by direct tests, also above the receiver -/
theorem absent_of_tests (F : PairFrame N q r s t u) (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s})
    (hv : σ 1 (t ^ N.factorization t) = q * u) {p : ℕ} {rs : List ℕ}
    (hmix : mixedOK u p rs = true) (hpure : pureOK u p = true) (hpu : p ≠ u)
    (hp1 : p % u ≠ 1) : p ∉ N.primeFactors := by
  intro hpN
  obtain ⟨-, -, htu, hqu, hR, -, -, hvq, -⟩ := F.vOne_basic h hq hN hqm hr hs hrs hJ hv
  have hpq : p ≠ q := fun e => hp1 (e ▸ hqu)
  have hpt : p ≠ t := fun e => hp1 (e ▸ htu)
  have h3 := F.receiver_not_three_dvd h hq hN hqm hr hs hrs hJ hv
  obtain ⟨-, -, -, -, -, -, -, -, -, hout, -⟩ := F.cofactor h hq hN hqm hr hs hrs hJ
  obtain ⟨⟨x, y, hrw⟩, hdq, -⟩ := hout p hpN hpq hpt hpu
  have hpp := Nat.prime_of_mem_primeFactors hpN
  have hpd := Nat.dvd_of_mem_primeFactors hpN
  have hp2 : p ≠ 2 := by rintro rfl; exact h.not_two_dvd hpd
  have hp3 : p ≠ 3 := by rintro rfl; exact h3 hpd
  set g := N.factorization p
  have hge : Even g := even_factorization_of_ne h hq (by rw [hvq]; exact odd_one) hpp hpq
  have hg0 : g ≠ 0 := (hpp.factorization_pos_of_dvd h.2.2.ne' hpd).ne'
  have hsum : ∑ i ∈ range (g + 1), p ^ i = t ^ x * u ^ y := by
    rw [← sigma_one_apply_prime_pow hpp]; exact hrw
  rcases Nat.eq_zero_or_pos y with hy0 | hy
  · rw [hy0, pow_zero, mul_one] at hrw hsum
    have hx : Odd x := by
      rcases odd_weight_or_three_pow_four hpp hp2 hge hg0 F.t_prime hrw with hx | ⟨h3', -⟩
      · exact hx
      · exact absurd h3' hp3
    exact pureOK_spec hpp hpure (Nat.succ_pos g) hx hsum ((dvd_pow_self _ hg0).trans hdq) hR
  · exact mixedOK_spec F.u_prime hmix F.t_prime htu hge.add_one hy hsum

/-- a pure outsider has an odd prime row length dividing `u - 1` -/
theorem pure_outsider_row (F : PairFrame N q r s t u) (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s})
    (hv : σ 1 (t ^ N.factorization t) = q * u) {p : ℕ}
    (hp : p ∈ N.primeFactors \ {q, r, s}) (hpt : ¬ t ∣ σ 1 (p ^ N.factorization p)) :
    (N.factorization p + 1).Prime ∧ 3 ≤ N.factorization p + 1 ∧
      u % (N.factorization p + 1) = 1 ∧
      ∃ w, Odd w ∧ ∑ i ∈ range (N.factorization p + 1), p ^ i = u ^ w := by
  obtain ⟨-, -, -, -, -, -, -, hvq, -⟩ := F.vOne_basic h hq hN hqm hr hs hrs hJ hv
  have h3 := F.receiver_not_three_dvd h hq hN hqm hr hs hrs hJ hv
  have hu := F.u_prime
  obtain ⟨hpN, hpq, hpt', hpu⟩ := F.mem_outsider.mp hp
  obtain ⟨-, -, -, -, -, -, -, -, -, hout, -⟩ := F.cofactor h hq hN hqm hr hs hrs hJ
  obtain ⟨⟨x, y, hrow⟩, -, -⟩ := hout p hpN hpq hpt' hpu
  have hpp := Nat.prime_of_mem_primeFactors hpN
  have hpd := Nat.dvd_of_mem_primeFactors hpN
  have hp2 : p ≠ 2 := by rintro rfl; exact h.not_two_dvd hpd
  have hp3 : p ≠ 3 := by rintro rfl; exact h3 hpd
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
  refine ⟨hl, by obtain ⟨k, hk⟩ := hge; omega, hmod, y, hy, ?_⟩
  rw [← sigma_one_apply_prime_pow hpp]; exact hrow

/-- the core after removing pure outsiders outside a set of centers -/
theorem core_card_le (F : PairFrame N q r s t u) (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s})
    (hv : σ 1 (t ^ N.factorization t) = q * u) (C : Finset ℕ) :
    (N.primeFactors \ (((N.primeFactors \ {q, r, s}).filter
      fun p => ¬ t ∣ σ 1 (p ^ N.factorization p)) \ C)).card ≤ u + 1 + C.card := by
  have hcard := F.receiver_card_le h hq hN hqm hr hs hrs hJ hv
  have hZ : ((N.primeFactors \ {q, r, s}).filter
      fun p => ¬ t ∣ σ 1 (p ^ N.factorization p)) ⊆ N.primeFactors :=
    fun p hp => (mem_sdiff.mp (mem_filter.mp hp).1).1
  have h1 := card_sdiff_add_card_eq_card hZ
  have hsub : N.primeFactors \ (((N.primeFactors \ {q, r, s}).filter
      fun p => ¬ t ∣ σ 1 (p ^ N.factorization p)) \ C) ⊆
      (N.primeFactors \ ((N.primeFactors \ {q, r, s}).filter
        fun p => ¬ t ∣ σ 1 (p ^ N.factorization p))) ∪ C := by
    intro p hp
    rw [mem_sdiff, mem_sdiff, not_and, not_not] at hp
    rw [mem_union, mem_sdiff]
    by_cases hpC : p ∈ C
    · exact Or.inr hpC
    · exact Or.inl ⟨hp.1, fun hz => hpC (hp.2 hz)⟩
  have h2 := card_le_card hsub
  have h3 := card_union_le (N.primeFactors \ ((N.primeFactors \ {q, r, s}).filter
    fun p => ¬ t ∣ σ 1 (p ^ N.factorization p))) C
  omega

/-- Every pure outsider has its row length among the kept lengths. -/
theorem pure_length_kept (F : PairFrame N q r s t u) (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s})
    (hv : σ 1 (t ^ N.factorization t) = q * u) {p : ℕ}
    (hp : p ∈ N.primeFactors \ {q, r, s}) (hpt : ¬ t ∣ σ 1 (p ^ N.factorization p)) :
    N.factorization p + 1 ∈ keptLengths u := by
  obtain ⟨-, hu11, -⟩ := F.vOne_basic h hq hN hqm hr hs hrs hJ hv
  have hu := F.u_prime
  have h3 := F.receiver_not_three_dvd h hq hN hqm hr hs hrs hJ hv
  obtain ⟨hdp, hd3, hud, w, hw, hsum⟩ := F.pure_outsider_row h hq hN hqm hr hs hrs hJ hv hp hpt
  have hpN := (mem_sdiff.mp hp).1
  have hpp := Nat.prime_of_mem_primeFactors hpN
  have hpd := Nat.dvd_of_mem_primeFactors hpN
  have hp5 : 5 ≤ p := five_le_of_prime hpp (by rintro rfl; exact h.not_two_dvd hpd)
    (by rintro rfl; exact h3 hpd)
  have hpodd : Odd p := hpp.odd_of_ne_two (by omega)
  generalize N.factorization p + 1 = d at hdp hd3 hud hsum ⊢
  have hdu : d < u := by
    by_contra hc
    push Not at hc
    rcases lt_or_eq_of_le hc with hc | hc
    · rw [Nat.mod_eq_of_lt hc] at hud; omega
    · rw [← hc, Nat.mod_self] at hud; omega
  refine mem_keptLengths_of hdu hd3 hdp hud ?_ ?_
  · intro hd
    rw [hd] at hsum
    have hphi : phi3 p = u ^ w := by
      rw [phi3, ← hsum]
      simp only [sum_range_succ, sum_range_zero, pow_zero, pow_one]
      ring
    have hw1 := phi3_eq_prime_pow_exponent hu hpp (by obtain ⟨k, rfl⟩ := hw; omega) hphi
    rw [hw1, pow_one, phi3] at hphi
    refine ⟨p, by nlinarith, Nat.odd_iff.mp hpodd, by rw [← hphi]; ring⟩
  · rintro ⟨hu4, hd4⟩
    have h1 := geom_sum_mod_four_of_len_one hpodd hd4
    rw [hsum, pow_odd_mod_four hu4 hw] at h1
    omega

/-- An accepted certificate is impossible, given the center statement `htail` (the statement
of `exists_center_of_common_receiver`) as a hypothesis. -/
theorem false_of_packRow_of_tail (F : PairFrame N q r s t u) (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime)
    (hrs : r ≠ s) (hJ : (eulerIndex q 1 m).primeFactors = {r, s})
    (hv : σ 1 (t ^ N.factorization t) = q * u)
    (htail : ∀ (d u B : ℕ) (S : Finset ℕ), d.Prime → 3 ≤ d → u.Prime → u ≠ d → 3 ≤ B →
      (∀ p ∈ S, p.Prime ∧ B ≤ p ∧ ∃ w, ∑ i ∈ Finset.range d, p ^ i = u ^ w) →
      ∃ C ⊆ S, C.card ≤ 1 ∧
        ∏ p ∈ S \ C, ((p : ℚ) / ((p : ℚ) - 1)) ≤
          ((B : ℚ) ^ (d - 1) - 1) / ((B : ℚ) ^ (d - 1) - 2))
    {A : List (ℕ × List ℕ)} {L : List ℕ} (hrow : packRow u A L = true) : False := by
  have hu := F.u_prime
  have h3 := F.receiver_not_three_dvd h hq hN hqm hr hs hrs hJ hv
  simp only [packRow, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hrow
  obtain ⟨⟨⟨hA, hL⟩, hlen⟩, hlt⟩ := hrow
  have hP : ∀ p ∈ N.primeFactors, p.Prime ∧ 5 ≤ p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    refine ⟨hpp, five_le_of_prime hpp ?_ ?_⟩
    · rintro rfl; exact h.not_two_dvd hpd
    · rintro rfl; exact h3 hpd
  have hf1 : ∀ p ∈ N.primeFactors, (1 : ℚ) ≤ (p : ℚ) / ((p : ℚ) - 1) := fun p hp =>
    one_le_div_sub_one (by have := (hP p hp).2; omega)
  set K := keptLengths u with hK
  set Z := (N.primeFactors \ {q, r, s}).filter
    fun p => ¬ t ∣ σ 1 (p ^ N.factorization p) with hZ
  have hZP : Z ⊆ N.primeFactors := fun p hp => (mem_sdiff.mp (mem_filter.mp hp).1).1
  have hZK : ∀ p ∈ Z, N.factorization p + 1 ∈ K := fun p hp =>
    F.pure_length_kept h hq hN hqm hr hs hrs hJ hv (mem_filter.mp hp).1 (mem_filter.mp hp).2
  -- one center set for each kept length
  have hcen : ∀ d ∈ K.toFinset, ∃ C, C ⊆ Z.filter (fun p => N.factorization p + 1 = d) ∧
      C.card ≤ 1 ∧
      ∏ p ∈ Z.filter (fun p => N.factorization p + 1 = d) \ C, ((p : ℚ) / ((p : ℚ) - 1)) ≤
        ((5 : ℚ) ^ (d - 1) - 1) / ((5 : ℚ) ^ (d - 1) - 2) := by
    intro d hd
    obtain ⟨hdu, hd3, hdp⟩ := keptLengths_facts (List.mem_toFinset.mp hd)
    obtain ⟨C, hCS, hC1, hCp⟩ := htail d u 5 (Z.filter fun p => N.factorization p + 1 = d)
      hdp hd3 hu (by omega) (by norm_num) (by
        intro p hp
        obtain ⟨hpZ, hpd⟩ := mem_filter.mp hp
        obtain ⟨-, -, -, w, -, hsum⟩ := F.pure_outsider_row h hq hN hqm hr hs hrs hJ hv
          (mem_filter.mp hpZ).1 (mem_filter.mp hpZ).2
        rw [hpd] at hsum
        exact ⟨(hP p (hZP hpZ)).1, (hP p (hZP hpZ)).2, w, hsum⟩)
    refine ⟨C, hCS, hC1, ?_⟩
    simpa only [Nat.cast_ofNat] using hCp
  choose! Cf hCsub hCcard hCprod using hcen
  set C := K.toFinset.biUnion Cf with hC
  have hCc : C.card ≤ K.length :=
    calc C.card ≤ ∑ d ∈ K.toFinset, (Cf d).card := card_biUnion_le
      _ ≤ ∑ d ∈ K.toFinset, 1 := sum_le_sum fun d hd => hCcard d hd
      _ = K.toFinset.card := (card_eq_sum_ones _).symm
      _ ≤ K.length := List.toFinset_card_le K
  -- the core
  have hG := F.core_card_le h hq hN hqm hr hs hrs hJ hv C
  rw [← hZ] at hG
  have hGenv : ∏ p ∈ N.primeFactors \ (Z \ C), ((p : ℚ) / ((p : ℚ) - 1)) ≤
      (L.map fun b : ℕ => (b : ℚ) / (b - 1)).prod := by
    refine prod_le_envelope hL (fun p hp => hP p (mem_sdiff.mp hp).1) (fun p hp hpA => ?_)
      (by omega)
    obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp hpA
    have hpr' := List.all_eq_true.mp hA pr hpr
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hpr'
    exact F.absent_of_tests h hq hN hqm hr hs hrs hJ hv hpr'.1.1.1 hpr'.1.1.2 hpr'.1.2 hpr'.2
      (mem_sdiff.mp hp).1
  -- the tail
  have hTle : ∏ p ∈ Z \ C, ((p : ℚ) / ((p : ℚ) - 1)) ≤
      (K.map fun d => ((5 : ℚ) ^ (d - 1) - 1) / ((5 : ℚ) ^ (d - 1) - 2)).prod := by
    rw [← List.prod_toFinset _ (keptLengths_nodup u),
      ← prod_fiberwise_of_maps_to (g := fun p => N.factorization p + 1) (t := K.toFinset)
        (fun p hp => List.mem_toFinset.mpr (hZK p (mem_sdiff.mp hp).1))]
    refine prod_le_prod₀ (fun d _ => prod_nonneg fun p hp => le_trans zero_le_one
      (hf1 p (hZP (mem_sdiff.mp (mem_filter.mp hp).1).1))) fun d hd => ?_
    refine le_trans (prod_le_prod_of_subset_one_le ?_ fun p hp => hf1 p
      (hZP (mem_filter.mp (mem_sdiff.mp hp).1).1)) (hCprod d hd)
    intro p hp
    obtain ⟨hpT, hpd⟩ := mem_filter.mp hp
    obtain ⟨hpZ, hpC⟩ := mem_sdiff.mp hpT
    exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨hpZ, hpd⟩, fun hc => hpC (mem_biUnion.mpr ⟨d, hd, hc⟩)⟩
  -- the inequality
  have hLge := envOK_ge hL
  have hK2 : ∀ d ∈ K, 2 ≤ d := fun d hd => by have := (keptLengths_facts hd).2.1; omega
  rw [tail_prod_eq hK2] at hTle
  rw [prod_map_eq_div fun b hb => by have := hLge b hb; omega] at hGenv
  have hLm : 0 < (L.map fun b => b - 1).prod := List.prod_pos fun c hc => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    have := hLge b hb; omega
  have hKd : 0 < (K.map fun d => 5 ^ (d - 1) - 2).prod := List.prod_pos fun c hc => by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have := hK2 d hd
    have : 5 ≤ 5 ^ (d - 1) :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 1 ≤ d - 1))
    omega
  have hsplit := prod_sdiff (f := fun p : ℕ => (p : ℚ) / ((p : ℚ) - 1))
    (show Z \ C ⊆ N.primeFactors from fun p hp => hZP (mem_sdiff.mp hp).1)
  have hTnn : (0 : ℚ) ≤ ∏ p ∈ Z \ C, ((p : ℚ) / ((p : ℚ) - 1)) :=
    prod_nonneg fun p hp => le_trans zero_le_one (hf1 p (hZP (mem_sdiff.mp hp).1))
  have hEnn : (0 : ℚ) ≤ (L.prod : ℚ) / (((L.map fun b => b - 1).prod : ℕ) : ℚ) := by
    positivity
  have hcast : ((L.prod * (K.map fun d => 5 ^ (d - 1) - 1).prod : ℕ) : ℚ) <
      ((2 * (L.map fun b => b - 1).prod * (K.map fun d => 5 ^ (d - 1) - 2).prod : ℕ) : ℚ) := by
    exact_mod_cast hlt
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hcast
  have hbound : ∏ p ∈ N.primeFactors, ((p : ℚ) / ((p : ℚ) - 1)) < 2 := by
    rw [← hsplit]
    refine lt_of_le_of_lt (mul_le_mul hGenv hTle hTnn hEnn) ?_
    rw [div_mul_div_comm, div_lt_iff₀ (mul_pos (by exact_mod_cast hLm) (by exact_mod_cast hKd))]
    linarith
  have hN1 : 1 < N := by
    have hqN : q ∣ N := by rw [hN]; exact dvd_mul_right q _
    exact lt_of_lt_of_le hq.one_lt (Nat.le_of_dvd h.2.2 hqN)
  exact not_perfect_of_prod_le_two hN1 hbound.le h.2

end PairFrame

end OddPerfect

#print axioms OddPerfect.geom_sum_mod_four_of_len_one
#print axioms OddPerfect.ReceiverSieve.packRow_of_parts
#print axioms OddPerfect.ReceiverSieve.absentOK_append
#print axioms OddPerfect.ReceiverSieve.envOK_append
#print axioms OddPerfect.ReceiverSieve.envOK_of_append
#print axioms OddPerfect.ReceiverSieve.keptLengths_facts
#print axioms OddPerfect.ReceiverSieve.mem_keptLengths_of
#print axioms OddPerfect.ReceiverSieve.keptLengths_nodup
#print axioms OddPerfect.ReceiverSieve.tail_prod_eq
#print axioms OddPerfect.ReceiverSieve.prod_le_prod_of_subset_one_le
#print axioms OddPerfect.PairFrame.absent_of_tests
#print axioms OddPerfect.PairFrame.pure_outsider_row
#print axioms OddPerfect.PairFrame.core_card_le
#print axioms OddPerfect.PairFrame.pure_length_kept
#print axioms OddPerfect.PairFrame.false_of_packRow_of_tail
