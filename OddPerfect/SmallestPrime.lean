import OddPerfect.Abundancy

/-!
# The smallest prime factor of an odd perfect number

Classical bounds on the smallest prime factor of an odd perfect number `N` in terms of the
number `ω(N)` of distinct prime factors: Servais (`p₁ ≤ ω`) and Grün (`3 p₁ < 2 ω + 6`),
together with the lower bounds `ω ≥ 7` when `3 ∤ N` and `ω ≥ 15` when `3 ∤ N` and `5 ∤ N`.
All rest on `2 < ∏ p/(p-1)` over the prime factors and finite set product bounds.

Stronger bounds are published and are not proved here: J. Zelinsky (INTEGERS 21 (2021), A76,
Corollary 4) proves `ω(N) ≥ 2 * p₁ + 2` for an odd perfect number with smallest prime factor
`p₁`, which is stronger than both bounds of Servais and of Grün. The bounds `7` and `15` below
use only the product inequality, so they hold for every odd number of abundancy at least 2
that is not divisible by 3 (respectively by 3 and 5).
-/

namespace OddPerfect

/-- If every element of a finite set `S` is at least `m ≥ 2`, then
`∏ s ∈ S, s/(s-1) ≤ 1 + |S|/(m-1)`, the telescoped product over `m, m+1, …, m+|S|-1`. -/
theorem prod_div_sub_one_le (S : Finset ℕ) {m : ℕ} (hm : 2 ≤ m) (hS : ∀ s ∈ S, m ≤ s) :
    ∏ s ∈ S, (s : ℚ) / (s - 1) ≤ 1 + S.card / (m - 1) := by
  induction S using Finset.induction_on_min generalizing m with
  | empty => simp
  | insert a S ha ih =>
    have haS : a ∉ S := fun h => lt_irrefl a (ha a h)
    have hma : m ≤ a := hS a (Finset.mem_insert_self a S)
    have h1 := ih (m := a + 1) (by omega) (fun s hs => ha s hs)
    rw [Finset.prod_insert haS, Finset.card_insert_of_notMem haS]
    have hm' : (2 : ℚ) ≤ m := by exact_mod_cast hm
    have ha' : (m : ℚ) ≤ a := by exact_mod_cast hma
    have hpos : (0 : ℚ) ≤ (a : ℚ) / (a - 1) := div_nonneg (by linarith) (by linarith)
    push_cast at h1 ⊢
    rw [add_sub_cancel_right] at h1
    calc (a : ℚ) / (a - 1) * ∏ s ∈ S, (s : ℚ) / (s - 1)
        ≤ (a : ℚ) / (a - 1) * (1 + S.card / a) := mul_le_mul_of_nonneg_left h1 hpos
      _ = 1 + (S.card + 1) / (a - 1) := by
          have : (a : ℚ) - 1 ≠ 0 := by linarith
          have : (a : ℚ) ≠ 0 := by linarith
          field_simp; ring
      _ ≤ 1 + (S.card + 1) / (m - 1) := by
          gcongr
          all_goals first | positivity | linarith

/-- If every element of a finite set `S` is odd and at least `m ≥ 3`, then
`(∏ s ∈ S, s/(s-1))^2 ≤ 1 + 2|S|/(m-2)`, from the telescoped product over `m, m+2, …`. -/
theorem sq_prod_div_sub_one_le (S : Finset ℕ) {m : ℕ} (hm : 3 ≤ m)
    (hS : ∀ s ∈ S, m ≤ s ∧ Odd s) :
    (∏ s ∈ S, (s : ℚ) / (s - 1)) ^ 2 ≤ 1 + 2 * S.card / (m - 2) := by
  induction S using Finset.induction_on_min generalizing m with
  | empty => simp
  | insert a S ha ih =>
    have haS : a ∉ S := fun h => lt_irrefl a (ha a h)
    obtain ⟨hma, hao⟩ := hS a (Finset.mem_insert_self a S)
    have h1 := ih (m := a + 2) (by omega) (fun s hs => by
      obtain ⟨hs1, hs2⟩ := hS s (Finset.mem_insert_of_mem hs)
      have := ha s hs
      refine ⟨?_, hs2⟩
      obtain ⟨i, rfl⟩ := hao; obtain ⟨j, rfl⟩ := hs2; omega)
    rw [Finset.prod_insert haS, Finset.card_insert_of_notMem haS, mul_pow]
    have hm' : (3 : ℚ) ≤ m := by exact_mod_cast hm
    have ha' : (m : ℚ) ≤ a := by exact_mod_cast hma
    push_cast at h1 ⊢
    calc ((a : ℚ) / (a - 1)) ^ 2 * (∏ s ∈ S, (s : ℚ) / (s - 1)) ^ 2
        ≤ ((a : ℚ) / (a - 1)) ^ 2 * (1 + 2 * S.card / (a + 2 - 2)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 1 + 2 * (S.card + 1) / (a - 2) := by
          have h2 : (0 : ℚ) < a - 2 := by linarith
          have h3 : (0 : ℚ) < a - 1 := by linarith
          have h4 : (0 : ℚ) < a := by linarith
          have hk : (0 : ℚ) ≤ S.card := by positivity
          have e1 : ((a : ℚ) / (a - 1)) ^ 2 * (1 + 2 * S.card / (a + 2 - 2))
              = a * (a + 2 * S.card) / (a - 1) ^ 2 := by
            rw [show (a : ℚ) + 2 - 2 = a by ring]; field_simp
          have e2 : (1 : ℚ) + 2 * (S.card + 1) / (a - 2) = (a + 2 * S.card) / (a - 2) := by
            field_simp; ring
          rw [e1, e2, div_le_div_iff₀ (by positivity) h2]
          nlinarith [add_nonneg h4.le (mul_nonneg zero_le_two hk)]
      _ ≤ 1 + 2 * (S.card + 1) / (m - 2) := by
          gcongr
          all_goals first | positivity | linarith


private theorem f_anti {m x : ℕ} (hm : 2 ≤ m) (hx : m ≤ x) :
    (x : ℚ) / (x - 1) ≤ (m : ℚ) / (m - 1) := by
  have hm' : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hx' : (m : ℚ) ≤ x := by exact_mod_cast hx
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

private theorem f_one_le {x : ℕ} (hx : 2 ≤ x) : (1 : ℚ) ≤ (x : ℚ) / (x - 1) := by
  have hx' : (2 : ℚ) ≤ x := by exact_mod_cast hx
  rw [le_div_iff₀ (by linarith)]; linarith

/-- Comparison with an explicit set `T`: if `T` consists of numbers in `[2, L]`, every element
of `S` is at least `2`, every element of `S` outside `T` exceeds `L`, and `|S| < |T|`, then
`(∏ s ∈ S, s/(s-1)) * (L/(L-1)) ≤ ∏ t ∈ T, t/(t-1)`. -/
theorem prod_div_sub_one_mul_le_of_card_lt {S T : Finset ℕ} {L : ℕ}
    (hT : ∀ t ∈ T, 2 ≤ t ∧ t ≤ L) (hS : ∀ s ∈ S, 2 ≤ s) (hST : ∀ s ∈ S, s ∉ T → L < s)
    (hcard : S.card < T.card) :
    (∏ s ∈ S, (s : ℚ) / (s - 1)) * ((L : ℚ) / (L - 1)) ≤ ∏ t ∈ T, (t : ℚ) / (t - 1) := by
  set f : ℕ → ℚ := fun x => (x : ℚ) / (x - 1) with hf
  have hL : 2 ≤ L := by
    obtain ⟨t, ht⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
    exact (hT t ht).1.trans (hT t ht).2
  have hc1 : (1 : ℚ) ≤ f L := f_one_le hL
  have hsz : (S \ T).card + 1 ≤ (T \ S).card := by
    have h1 := Finset.card_sdiff_add_card_inter S T
    have h2 := Finset.card_sdiff_add_card_inter T S
    rw [Finset.inter_comm] at h2
    omega
  obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq hsz
  have hfS : ∀ s ∈ S, 0 ≤ f s := fun s hs => (zero_le_one.trans (f_one_le (hS s hs)))
  have step1 : ∏ s ∈ S \ T, f s ≤ f L ^ (S \ T).card := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod (fun s hs => hfS s (Finset.mem_sdiff.mp hs).1)
    intro s hs
    obtain ⟨hs1, hs2⟩ := Finset.mem_sdiff.mp hs
    exact f_anti hL (hST s hs1 hs2).le
  have step2 : f L ^ R.card ≤ ∏ r ∈ R, f r := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod (fun _ _ => by positivity)
    intro r hr
    have := hT r (Finset.mem_sdiff.mp (hRsub hr)).1
    exact f_anti this.1 this.2
  have hdisj : Disjoint (S ∩ T) R := by
    rw [Finset.disjoint_left]
    intro x hx hxR
    exact (Finset.mem_sdiff.mp (hRsub hxR)).2 (Finset.mem_inter.mp hx).1
  have step3 : ∏ x ∈ (S ∩ T) ∪ R, f x ≤ ∏ t ∈ T, f t := by
    apply Finset.prod_le_prod_of_subset_of_one_le
    · intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact (Finset.mem_inter.mp h).2
      · exact (Finset.mem_sdiff.mp (hRsub h)).1
    · intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact hfS x (Finset.mem_inter.mp h).1
      · exact zero_le_one.trans (f_one_le (hT x (Finset.mem_sdiff.mp (hRsub h)).1).1)
    · intro x hx _
      exact f_one_le (hT x hx).1
  rw [Finset.prod_union hdisj] at step3
  rw [← Finset.prod_inter_mul_prod_sdiff S T, hRcard, pow_succ] at *
  have hI : 0 ≤ ∏ x ∈ S ∩ T, f x :=
    Finset.prod_nonneg fun x hx => hfS x (Finset.mem_inter.mp hx).1
  calc (∏ x ∈ S ∩ T, f x) * (∏ x ∈ S \ T, f x) * f L
      ≤ (∏ x ∈ S ∩ T, f x) * (f L ^ (S \ T).card * f L) := by
        rw [mul_assoc]; gcongr
    _ ≤ (∏ x ∈ S ∩ T, f x) * ∏ r ∈ R, f r := by gcongr
    _ ≤ _ := step3


private theorem ne_one {N : ℕ} (h : OddPerfect N) : N ≠ 1 := by
  rintro rfl
  have hp1 := h.perfect
  simp [Nat.Perfect] at hp1

/-- For an odd perfect number, the product of `p/(p-1)` over its prime factors exceeds two. -/
theorem two_lt_prod_primeFactors {N : ℕ} (h : OddPerfect N) :
    2 < ∏ p ∈ N.primeFactors, (p : ℚ) / (p - 1) := by
  have hN : 1 < N := by have := h.pos; have := ne_one h; omega
  have := abundancy_lt_prod hN
  rwa [(perfect_iff_abundancy_eq_two h.pos).mp h.perfect] at this

private theorem minFac_le_of_mem {N p : ℕ} (hp : p ∈ N.primeFactors) : N.minFac ≤ p :=
  Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hp).two_le (Nat.dvd_of_mem_primeFactors hp)

/-- Servais (1888): the smallest prime factor is at most the number of distinct prime factors. -/
theorem minFac_le_card_primeFactors {N : ℕ} (h : OddPerfect N) :
    N.minFac ≤ N.primeFactors.card := by
  have hm : 2 ≤ N.minFac := (Nat.minFac_prime (ne_one h)).two_le
  have h1 := prod_div_sub_one_le N.primeFactors hm (fun p hp => minFac_le_of_mem hp)
  have h2 := two_lt_prod_primeFactors h
  have hm' : (2 : ℚ) ≤ N.minFac := by exact_mod_cast hm
  have h3 : (N.minFac : ℚ) - 1 < N.primeFactors.card := by
    have : (1 : ℚ) < N.primeFactors.card / (N.minFac - 1) := by linarith
    rwa [one_lt_div (by linarith)] at this
  have : (N.minFac : ℚ) < N.primeFactors.card + 1 := by linarith
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-- The smallest prime factor of an odd perfect number is at least three. -/
theorem three_le_minFac {N : ℕ} (h : OddPerfect N) : 3 ≤ N.minFac := by
  have hp := Nat.minFac_prime (ne_one h)
  have h2 : N.minFac ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.minFac_dvd N)
  have := hp.two_le
  omega

/-- Grün (1952): `p₁ < (2/3) ω + 2`. -/
theorem three_mul_minFac_lt {N : ℕ} (h : OddPerfect N) :
    3 * N.minFac < 2 * N.primeFactors.card + 6 := by
  have hm := three_le_minFac h
  have h1 := sq_prod_div_sub_one_le N.primeFactors hm (fun p hp => ⟨minFac_le_of_mem hp,
    (Nat.prime_of_mem_primeFactors hp).odd_of_ne_two (fun h2 =>
      h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hp))⟩)
  have h2 := two_lt_prod_primeFactors h
  have hm' : (3 : ℚ) ≤ N.minFac := by exact_mod_cast hm
  have h4 : (4 : ℚ) < (∏ p ∈ N.primeFactors, (p : ℚ) / (p - 1)) ^ 2 := by nlinarith
  have h3 : 3 * ((N.minFac : ℚ) - 2) < 2 * N.primeFactors.card := by
    have : (3 : ℚ) < 2 * N.primeFactors.card / (N.minFac - 2) := by linarith
    rw [lt_div_iff₀ (by linarith)] at this
    linarith
  have : (3 * N.minFac : ℚ) < 2 * N.primeFactors.card + 6 := by linarith
  exact_mod_cast this

/-- If `3 ∤ N` for an odd perfect number `N`, then `N` has at least seven distinct prime
factors. -/
theorem seven_le_card_primeFactors_of_not_three_dvd {N : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N) :
    7 ≤ N.primeFactors.card := by
  have hge : ∀ p ∈ N.primeFactors, 5 ≤ p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hd := Nat.dvd_of_mem_primeFactors hp
    have : p ≠ 2 := fun e => h.not_two_dvd (e ▸ hd)
    have : p ≠ 3 := fun e => h3 (e ▸ hd)
    have : p ≠ 4 := fun e => by subst e; norm_num at hpp
    have := hpp.two_le
    omega
  by_contra hlt
  have key := prod_div_sub_one_mul_le_of_card_lt (S := N.primeFactors)
    (T := {5, 7, 11, 13, 17, 19, 23}) (L := 23)
    (by intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht; omega)
    (fun s hs => (by have := hge s hs; omega))
    (by
      intro s hs hsT
      have hpp := Nat.prime_of_mem_primeFactors hs
      have := hge s hs
      by_contra hle
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsT
      interval_cases s
      all_goals first | omega | norm_num at hpp)
    (by rw [show ({5, 7, 11, 13, 17, 19, 23} : Finset ℕ).card = 7 by rfl]; omega)
  have h2 := two_lt_prod_primeFactors h
  have hval : (∏ t ∈ ({5, 7, 11, 13, 17, 19, 23} : Finset ℕ), (t : ℚ) / (t - 1))
      < 2 * ((23 : ℕ) / ((23 : ℕ) - 1)) := by
    norm_num [Finset.prod_insert]
  linarith

/-- If `3 ∤ N` and `5 ∤ N` for an odd perfect number `N`, then `N` has at least fifteen
distinct prime factors. -/
theorem fifteen_le_card_primeFactors_of_not_three_dvd_of_not_five_dvd {N : ℕ}
    (h : OddPerfect N) (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N) :
    15 ≤ N.primeFactors.card := by
  have hge : ∀ p ∈ N.primeFactors, 7 ≤ p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hd := Nat.dvd_of_mem_primeFactors hp
    have : p ≠ 2 := fun e => h.not_two_dvd (e ▸ hd)
    have : p ≠ 3 := fun e => h3 (e ▸ hd)
    have : p ≠ 5 := fun e => h5 (e ▸ hd)
    have : p ≠ 4 := fun e => by subst e; norm_num at hpp
    have : p ≠ 6 := fun e => by subst e; norm_num at hpp
    have := hpp.two_le
    omega
  by_contra hlt
  have key := prod_div_sub_one_mul_le_of_card_lt (S := N.primeFactors)
    (T := {7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61}) (L := 61)
    (by intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht; omega)
    (fun s hs => (by have := hge s hs; omega))
    (by
      intro s hs hsT
      have hpp := Nat.prime_of_mem_primeFactors hs
      have := hge s hs
      by_contra hle
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsT
      interval_cases s
      all_goals first | omega | norm_num at hpp)
    (by
      rw [show ({7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61} : Finset ℕ).card
        = 15 by rfl]
      omega)
  have h2 := two_lt_prod_primeFactors h
  have hval : (∏ t ∈ ({7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61} : Finset ℕ),
      (t : ℚ) / (t - 1)) < 2 * ((61 : ℕ) / ((61 : ℕ) - 1)) := by
    norm_num [Finset.prod_insert]
  linarith

end OddPerfect

#print axioms OddPerfect.prod_div_sub_one_le
#print axioms OddPerfect.sq_prod_div_sub_one_le
#print axioms OddPerfect.prod_div_sub_one_mul_le_of_card_lt
#print axioms OddPerfect.two_lt_prod_primeFactors
#print axioms OddPerfect.minFac_le_card_primeFactors
#print axioms OddPerfect.three_le_minFac
#print axioms OddPerfect.three_mul_minFac_lt
#print axioms OddPerfect.seven_le_card_primeFactors_of_not_three_dvd
#print axioms OddPerfect.fifteen_le_card_primeFactors_of_not_three_dvd_of_not_five_dvd
