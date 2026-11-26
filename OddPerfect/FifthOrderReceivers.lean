import OddPerfect.SpecialPrime
import OddPerfect.Cyclotomic

/-!
# Prime factors of order a power of 5 modulo which 5 has that order

Let `N` be an odd perfect number and `e = v_5(N)`. For every `j ≥ 1` with `5 ^ j ∣ e + 1`, the
number `N` has two distinct prime factors `r ≡ 3 (mod 4)` such that the multiplicative order of
5 modulo `r` is exactly `5 ^ j`. Primes for different `j` differ, since their orders differ. So
with `s = v_5(e + 1)`, the number `N` has at least `2 s` prime factors `≡ 3 (mod 4)`.
When `5 ∤ e + 1` (in particular when `5 ∤ N`) the count statement is trivial, since `s = 0`.

Proof: write `5 ^ (j - 1) = 2 k + 1`, `z = 5 ^ k` and `x = 5 z ^ 2 = 5 ^ (5 ^ (j - 1))`. The
Aurifeuillean identity `x ^ 4 + x ^ 3 + x ^ 2 + x + 1 = (x ^ 2 + 3 x + 1) ^ 2 - 5 x (x + 1) ^ 2`
splits `Φ = x ^ 4 + x ^ 3 + x ^ 2 + x + 1` as `L * M` with
`L = 25 z ^ 4 - 25 z ^ 3 + 15 z ^ 2 - 5 z + 1` and `M = 25 z ^ 4 + 25 z ^ 3 + 15 z ^ 2 + 5 z + 1`.
Since `z ≡ 1 (mod 4)`, both are `≡ 3 (mod 4)`, so each has a prime factor `≡ 3 (mod 4)`; and
`L`, `M` are coprime. Modulo a prime factor `r` of `Φ`, `x` has order 5, so 5 has order `5 ^ j`.
That order divides `e + 1`, so `r ∣ 5 ^ (e + 1) - 1 = 4 σ(5 ^ e)`, and `r ∣ N`.

Restricted result; no published source was checked; novelty not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FifthOrderReceivers

/-- A number that is `3` modulo `4` has a prime factor that is `3` modulo `4`. -/
private theorem forr_prime_dvd_mod_four_eq_three (n : ℕ) (hn : n % 4 = 3) :
    ∃ r, r.Prime ∧ r ∣ n ∧ r % 4 = 3 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn1 : n ≠ 1 := by omega
    have hmp : n.minFac.Prime := Nat.minFac_prime hn1
    obtain ⟨k, hk⟩ := Nat.minFac_dvd n
    by_cases h3 : n.minFac % 4 = 3
    · exact ⟨n.minFac, hmp, ⟨k, hk⟩, h3⟩
    have hm2 : n.minFac ≠ 2 := by
      intro h2
      rw [h2] at hk
      omega
    have hm1 : n.minFac % 4 = 1 := by
      rcases hmp.eq_two_or_odd with h | h
      · exact absurd h hm2
      · omega
    have hk3 : k % 4 = 3 := by
      have := Nat.mul_mod n.minFac k 4
      rw [← hk, hm1] at this
      omega
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hk
        omega
      · exact h
    have hklt : k < n := by
      have := hmp.two_le
      nlinarith
    obtain ⟨r, hr, hrk, hr4⟩ := ih k hklt hk3
    exact ⟨r, hr, hrk.trans (Dvd.intro_left _ hk.symm), hr4⟩

/-- The Aurifeuillean pieces, written with `z = 4 c + 1` and without subtraction. -/
def lo (c : ℕ) : ℕ := 25 * (4 * c) * (4 * c + 1) ^ 3 + 15 * (4 * c) ^ 2 + 25 * (4 * c) + 11

/-- The second Aurifeuillean piece, with `z = 4 c + 1`. -/
def hi (c : ℕ) : ℕ :=
  25 * (4 * c + 1) ^ 4 + 25 * (4 * c + 1) ^ 3 + 15 * (4 * c + 1) ^ 2 + 5 * (4 * c + 1) + 1

/-- `L * M = Φ(x)` with `x = 5 z ^ 2`. -/
theorem lo_mul_hi (c : ℕ) :
    lo c * hi c = (5 * (4 * c + 1) ^ 2) ^ 4 + (5 * (4 * c + 1) ^ 2) ^ 3 +
      (5 * (4 * c + 1) ^ 2) ^ 2 + 5 * (4 * c + 1) ^ 2 + 1 := by
  unfold lo hi
  ring

theorem lo_mod_four (c : ℕ) : lo c % 4 = 3 := by
  have : lo c = 4 * (25 * c * (4 * c + 1) ^ 3 + 60 * c ^ 2 + 25 * c + 2) + 3 := by
    unfold lo
    ring
  rw [this, Nat.mul_add_mod]

theorem hi_mod_four (c : ℕ) : hi c % 4 = 3 := by
  have : hi c = 4 * (1600 * c ^ 4 + 2000 * c ^ 3 + 960 * c ^ 2 + 210 * c + 17) + 3 := by
    unfold hi
    ring
  rw [this, Nat.mul_add_mod]

/-- `L` and `M` have no common prime factor. -/
theorem not_dvd_lo_and_hi {c p : ℕ} (hp : p.Prime) (hL : p ∣ lo c) (hM : p ∣ hi c) : False := by
  set z := 4 * c + 1 with hz
  set x := 5 * z ^ 2 with hx
  set A := x ^ 2 + 3 * x + 1 with hA
  have hsum : lo c + hi c = 2 * A := by
    simp only [lo, hi, hA, hx, hz]
    ring
  have hdiff : hi c = lo c + 2 * (5 * z * (x + 1)) := by
    simp only [lo, hi, hx, hz]
    ring
  have hp2 : p ≠ 2 := by
    rintro rfl
    have := lo_mod_four c
    omega
  have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have hpA : p ∣ A := hcop.dvd_of_dvd_mul_left (hsum ▸ dvd_add hL hM)
  have hpB : p ∣ 5 * z * (x + 1) :=
    hcop.dvd_of_dvd_mul_left ((Nat.dvd_add_right hL).mp (hdiff ▸ hM))
  have hA5 : A = 5 * (5 * z ^ 4 + 3 * z ^ 2) + 1 := by
    simp only [hA, hx]
    ring
  have hA1 : A + 1 = (x + 1) * (x + 2) := by
    simp only [hA]
    ring
  have hAz : A = z * (25 * z ^ 3 + 15 * z) + 1 := by
    simp only [hA, hx]
    ring
  rcases (Nat.Prime.dvd_mul hp).mp hpB with h5z | hx1
  · rcases (Nat.Prime.dvd_mul hp).mp h5z with h5 | hzd
    · rw [hA5] at hpA
      exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (h5.mul_right _)).mp hpA))
    · rw [hAz] at hpA
      exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (hzd.mul_right _)).mp hpA))
  · have : p ∣ A + 1 := hA1 ▸ hx1.mul_right _
    exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hpA).mp this))

/-- A prime factor of `Φ(5 ^ (5 ^ n))` other than 5 has order `5 ^ (n + 1)` for 5. -/
theorem orderOf_eq_of_dvd {n r : ℕ} (hr : r.Prime) (hr5 : r ≠ 5)
    (hd : r ∣ (5 ^ 5 ^ n) ^ 4 + (5 ^ 5 ^ n) ^ 3 + (5 ^ 5 ^ n) ^ 2 + 5 ^ 5 ^ n + 1) :
    orderOf (5 : ZMod r) = 5 ^ (n + 1) := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hΦ : ((5 : ZMod r) ^ 5 ^ n) ^ 4 + ((5 : ZMod r) ^ 5 ^ n) ^ 3 +
      ((5 : ZMod r) ^ 5 ^ n) ^ 2 + (5 : ZMod r) ^ 5 ^ n + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ r).mpr hd
    push_cast at this
    exact this
  have h50 : (5 : ZMod r) ≠ 0 := by
    intro h0
    have : ((5 : ℕ) : ZMod r) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hr5 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp this)
  apply orderOf_eq_prime_pow
  · intro h1
    rw [h1] at hΦ
    apply h50
    linear_combination hΦ
  · rw [pow_succ, pow_mul]
    linear_combination ((5 : ZMod r) ^ 5 ^ n - 1) * hΦ

/-- If 5 has order dividing `e + 1` modulo an odd prime `r`, then `r ∣ σ(5 ^ e)`. -/
theorem dvd_sigma_of_orderOf_dvd {r e : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : orderOf (5 : ZMod r) ∣ e + 1) : r ∣ σ 1 (5 ^ e) := by
  have hpow : (5 : ZMod r) ^ (e + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp h
  have hkey : ((σ 1 (5 ^ e) * (5 - 1) : ℕ) : ZMod r) = 0 := by
    rw [sigma_prime_pow_mul_pred Nat.prime_five, Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num)),
      Nat.cast_pow, Nat.cast_ofNat, hpow, Nat.cast_one, sub_self]
  have hd := (ZMod.natCast_eq_zero_iff _ r).mp hkey
  have hcop : Nat.Coprime r (5 - 1) := by
    rw [show (5 - 1 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
  exact hcop.dvd_of_dvd_mul_right hd

end FifthOrderReceivers

open FifthOrderReceivers

variable {N : ℕ}

/-- **Two receivers of each order `5 ^ j`.** Let `N` be an odd perfect number and `j ≥ 1` with
`5 ^ j ∣ v_5(N) + 1`. Then `N` has two distinct prime factors `r ≡ 3 (mod 4)` modulo which 5 has
multiplicative order exactly `5 ^ j`. Restricted result; no published source was checked;
novelty not verified. -/
theorem exists_two_fifth_order_receivers (h : OddPerfect N) {j : ℕ} (hj : 1 ≤ j)
    (hdvd : 5 ^ j ∣ N.factorization 5 + 1) :
    ∃ r₁ r₂, r₁ ≠ r₂ ∧ r₁ ∈ N.primeFactors ∧ r₂ ∈ N.primeFactors ∧ r₁ % 4 = 3 ∧ r₂ % 4 = 3 ∧
      orderOf (5 : ZMod r₁) = 5 ^ j ∧ orderOf (5 : ZMod r₂) = 5 ^ j := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  obtain ⟨k, hk⟩ : Odd (5 ^ n) := Odd.pow (by decide)
  have hz4 : 5 ^ k % 4 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  obtain ⟨c, hc⟩ : ∃ c, 5 ^ k = 4 * c + 1 := ⟨5 ^ k / 4, by omega⟩
  have hx : 5 ^ 5 ^ n = 5 * (4 * c + 1) ^ 2 := by
    rw [hk, ← hc]
    ring
  have hΦ := lo_mul_hi c
  rw [← hx] at hΦ
  -- each piece is `≡ 3 (mod 4)`, so it has a prime factor `≡ 3 (mod 4)`
  obtain ⟨r₁, hr₁, hr₁d, hr₁4⟩ := forr_prime_dvd_mod_four_eq_three _ (lo_mod_four c)
  obtain ⟨r₂, hr₂, hr₂d, hr₂4⟩ := forr_prime_dvd_mod_four_eq_three _ (hi_mod_four c)
  have hgood (r : ℕ) (hr : r.Prime) (hr4 : r % 4 = 3) (hd : r ∣ lo c * hi c) :
      r ∈ N.primeFactors ∧ orderOf (5 : ZMod r) = 5 ^ (n + 1) := by
    have hord := orderOf_eq_of_dvd hr (by omega) (hΦ ▸ hd)
    refine ⟨Nat.mem_primeFactors.mpr ⟨hr, ?_, h.ne_zero⟩, hord⟩
    exact OPNStarter.force_prime h.perfect Nat.prime_five rfl hr (by omega)
      (dvd_sigma_of_orderOf_dvd hr (by omega) (hord ▸ hdvd))
  obtain ⟨hm₁, ho₁⟩ := hgood r₁ hr₁ hr₁4 (hr₁d.mul_right _)
  obtain ⟨hm₂, ho₂⟩ := hgood r₂ hr₂ hr₂4 (hr₂d.mul_left _)
  refine ⟨r₁, r₂, ?_, hm₁, hm₂, hr₁4, hr₂4, ho₁, ho₂⟩
  rintro rfl
  exact not_dvd_lo_and_hi hr₁ hr₁d hr₂d

/-- **Fifth order receivers.** For an odd perfect number `N` with `s = v_5(v_5(N) + 1)`, at least
`2 s` distinct prime factors of `N` are `≡ 3 (mod 4)`. The statement is trivial when
`5 ∤ v_5(N) + 1`. Restricted result; no published source was checked; novelty not verified. -/
theorem two_mul_padicValNat_le_card_mod_four_eq_three (h : OddPerfect N) :
    2 * padicValNat 5 (N.factorization 5 + 1) ≤
      (N.primeFactors.filter (fun p => p % 4 = 3)).card := by
  classical
  obtain ⟨s, hs⟩ : ∃ s, padicValNat 5 (N.factorization 5 + 1) = s := ⟨_, rfl⟩
  rw [hs]
  set F := N.primeFactors.filter (fun p => p % 4 = 3)
  let T : ℕ → Finset ℕ := fun j => F.filter (fun r => orderOf (5 : ZMod r) = 5 ^ j)
  have hdisj : ((Finset.Icc 1 s : Finset ℕ) : Set ℕ).PairwiseDisjoint T := by
    intro a _ b _ hab
    refine Finset.disjoint_left.mpr fun r hra hrb => hab ?_
    have h1 := (Finset.mem_filter.mp hra).2
    have h2 := (Finset.mem_filter.mp hrb).2
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 5) (h1.symm.trans h2)
  have htwo : ∀ j ∈ Finset.Icc 1 s, 2 ≤ (T j).card := by
    intro j hj
    have hj1 := (Finset.mem_Icc.mp hj).1
    have hle : j ≤ padicValNat 5 (N.factorization 5 + 1) := hs ▸ (Finset.mem_Icc.mp hj).2
    rw [Nat.padicValNat_def] at hle
    have hdvd : 5 ^ j ∣ N.factorization 5 + 1 :=
      (Nat.pow_dvd_iff_le_multiplicity (by norm_num) (by omega)).mpr hle
    obtain ⟨r₁, r₂, hne, hm₁, hm₂, h₁4, h₂4, ho₁, ho₂⟩ :=
      exists_two_fifth_order_receivers h hj1 hdvd
    have hsub : ({r₁, r₂} : Finset ℕ) ⊆ T j := by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hm₁, h₁4⟩, ho₁⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hm₂, h₂4⟩, ho₂⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hne] at this
    exact this
  have hsum := Finset.card_nsmul_le_sum (Finset.Icc 1 s) (fun j => (T j).card) 2 htwo
  rw [← Finset.card_biUnion hdisj, Nat.card_Icc, smul_eq_mul] at hsum
  have hsub : (Finset.Icc 1 s).biUnion T ⊆ F := by
    intro r hr
    obtain ⟨j, -, hrj⟩ := Finset.mem_biUnion.mp hr
    exact (Finset.mem_filter.mp hrj).1
  have := Finset.card_le_card hsub
  omega

end OddPerfect

#print axioms OddPerfect.FifthOrderReceivers.lo_mul_hi
#print axioms OddPerfect.FifthOrderReceivers.lo_mod_four
#print axioms OddPerfect.FifthOrderReceivers.hi_mod_four
#print axioms OddPerfect.FifthOrderReceivers.not_dvd_lo_and_hi
#print axioms OddPerfect.FifthOrderReceivers.orderOf_eq_of_dvd
#print axioms OddPerfect.FifthOrderReceivers.dvd_sigma_of_orderOf_dvd
#print axioms OddPerfect.exists_two_fifth_order_receivers
#print axioms OddPerfect.two_mul_padicValNat_le_card_mod_four_eq_three
