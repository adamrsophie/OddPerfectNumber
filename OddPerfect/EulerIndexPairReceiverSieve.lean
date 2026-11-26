import Mathlib

/-!
# Two prime Euler index, branch `v = 1`: the prime 3 and a receiver sieve

Restricted result; no published source was checked; novelty not verified.

Arithmetic facts used in the branch `v = 1` of the two prime Euler index family, stated with
explicit hypotheses on natural numbers. Write `R_n(x) = ∑ i ∈ range n, x ^ i`.

* `mod_three_of_receiver`: if `u > 3` is prime, `R_u(t) = q u` and `R_(f+1)(u) = t ^ j` with
  `f` even and `j` odd, then `q ≡ 1 (mod 3)`.
* `mixedOK_spec`: the decidable test `mixedOK u p rs` excludes every row
  `R_n(p) = t ^ x * u ^ y` with `n` odd, `y > 0`, `t` prime and `t ≡ 1 (mod u)`.
* `pureOK_spec`: the decidable test `pureOK u p` excludes every row `R_n(p) = t ^ x` with `x`
  odd, when `p ∣ q + 1` and `R_u(t) = q u`.
* `prod_le_envelope`: for a set `P` of primes at least 5 avoiding a list `A`, with
  `P.card ≤ L.length`, the product of `p / (p - 1)` over `P` is at most the same product over
  `L`, when `envOK A 5 L` certifies that `L` lists the first primes at least 5 outside `A`.
* `sieveTable_spec`: for each receiver `u` in `sieveTable` (the primes 11 to 47 except 43),
  both tests accept every listed prime `p`, and every set of at most `u + 1 + z` primes at
  least 5 avoiding those `p` has `∏ p / (p - 1) < 2`.
-/

namespace OddPerfect
namespace ReceiverSieve

open Finset

/-- The geometric sum `R_n(x)`, by recursion; it reduces in the kernel. -/
def gsum : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, x => gsum n x + x ^ n

theorem gsum_eq (n x : ℕ) : gsum n x = ∑ i ∈ range n, x ^ i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [gsum, ih, sum_range_succ]

/-! ## The prime 3 -/

/-- A residue modulo 3 times the sum of its first six powers is zero. -/
theorem geom_six_zmod_three (x : ZMod 3) : x * ∑ i ∈ range 6, x ^ i = 0 := by
  revert x; decide

/-- A geometric sum of length `6 m + 1` is `1` in `ZMod 3`. -/
theorem geom_zmod_three (x : ZMod 3) (m : ℕ) : ∑ i ∈ range (6 * m + 1), x ^ i = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 6 * (m + 1) + 1 = 6 * m + 1 + 6 by ring, sum_range_add, ih]
    have hb : ∑ i ∈ range 6, x ^ (6 * m + 1 + i) =
        x ^ (6 * m) * (x * ∑ i ∈ range 6, x ^ i) := by
      rw [mul_sum, mul_sum]
      exact sum_congr rfl fun i _ => by ring
    rw [hb, geom_six_zmod_three, mul_zero, add_zero]

/-- Item 1. If `u > 3` is prime, `R_u(t) = q u` and `R_(f+1)(u) = t ^ j` with `f` even and
`j` odd, then `q ≡ 1 (mod 3)`. -/
theorem mod_three_of_receiver {u q t f j : ℕ} (hu : u.Prime) (hu3 : 3 < u)
    (hR : ∑ i ∈ range u, t ^ i = q * u) (hret : ∑ i ∈ range (f + 1), u ^ i = t ^ j)
    (hf : Even f) (hj : Odd j) : q % 3 = 1 := by
  have hodd : u % 2 = 1 := Nat.odd_iff.mp (hu.odd_of_ne_two (by omega))
  have h3 : u % 3 ≠ 0 := by
    intro h
    have := (Nat.Prime.eq_one_or_self_of_dvd hu 3 (Nat.dvd_of_mod_eq_zero h))
    omega
  have hR' : ∑ i ∈ range u, (t : ZMod 3) ^ i = (q : ZMod 3) * u := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 3) hR
  have key : (q : ZMod 3) = 1 := by
    rcases (by omega : u % 3 = 1 ∨ u % 3 = 2) with h1 | h2
    · have hu1 : (u : ZMod 3) = 1 := by rw [← ZMod.natCast_mod, h1]; rfl
      obtain ⟨m, hm⟩ : ∃ m, u = 6 * m + 1 := ⟨u / 6, by omega⟩
      rw [hu1, hm, geom_zmod_three] at hR'
      linear_combination -hR'
    · have hu2 : (u : ZMod 3) = -1 := by rw [← ZMod.natCast_mod, h2]; decide
      have hret' : ∑ i ∈ range (f + 1), (u : ZMod 3) ^ i = (t : ZMod 3) ^ j := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 3) hret
      have hne : ¬ Even (f + 1) := by
        rw [Nat.not_even_iff_odd]; exact hf.add_one
      rw [hu2, neg_one_geom_sum] at hret'
      simp only [hne, ↓reduceIte] at hret'
      obtain ⟨k, rfl⟩ := hj
      have hx2 : ∀ x : ZMod 3, x = 0 ∨ x ^ 2 = 1 := by decide
      have ht1 : (t : ZMod 3) = 1 := by
        rcases hx2 (t : ZMod 3) with h0 | h1
        · rw [h0, zero_pow (by omega)] at hret'
          exact absurd hret' (by decide)
        · rw [pow_succ, pow_mul, h1, one_pow, one_mul] at hret'
          exact hret'.symm
      rw [ht1] at hR'
      simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at hR'
      rw [hu2] at hR'
      linear_combination hR'
  have hq3 : q % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases h : q % 3
  · rw [← ZMod.natCast_mod, h] at key; exact absurd key (by decide)
  · rfl
  · rw [← ZMod.natCast_mod, h] at key; exact absurd key (by decide)

/-- Consequence of item 1: `3 ∤ q + 1`. -/
theorem not_three_dvd_succ_of_receiver {u q t f j : ℕ} (hu : u.Prime) (hu3 : 3 < u)
    (hR : ∑ i ∈ range u, t ^ i = q * u) (hret : ∑ i ∈ range (f + 1), u ^ i = t ^ j)
    (hf : Even f) (hj : Odd j) : ¬ 3 ∣ q + 1 := by
  have := mod_three_of_receiver hu hu3 hR hret hf hj
  omega

/-! ## Mixed rows -/

/-- `R_(d k)(x) = R_d(x) * R_k(x ^ d)`. -/
theorem geom_sum_mul_len (x d k : ℕ) :
    ∑ i ∈ range (d * k), x ^ i = (∑ i ∈ range d, x ^ i) * ∑ j ∈ range k, (x ^ d) ^ j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show d * (k + 1) = d * k + d by ring, sum_range_add, ih, sum_range_succ, mul_add]
    congr 1
    rw [sum_mul]
    exact sum_congr rfl fun i _ => by rw [pow_add, pow_mul, mul_comm]

theorem gsum_dvd {d n : ℕ} (x : ℕ) (h : d ∣ n) : gsum d x ∣ gsum n x := by
  obtain ⟨k, rfl⟩ := h
  rw [gsum_eq, gsum_eq, geom_sum_mul_len]
  exact Dvd.intro _ rfl

/-- If `u ∣ R_n(p)` then `p ^ n ≡ 1 (mod u)`. -/
theorem pow_mod_of_dvd_gsum {u n p : ℕ} (hu : 1 < u) (h : u ∣ gsum n p) : p ^ n % u = 1 := by
  rw [gsum_eq] at h
  have h0 : ((∑ i ∈ range n, p ^ i : ℕ) : ZMod u) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  have h1 : ((p ^ n : ℕ) : ZMod u) = ((1 : ℕ) : ZMod u) := by
    push_cast at h0 ⊢
    have := geom_sum_mul (p : ZMod u) n
    rw [h0, zero_mul] at this
    linear_combination -this
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hu] at h1
  exact h1

/-- A minimal exponent `d` with `p ^ d ≡ 1 (mod u)` divides every such exponent. -/
theorem dvd_of_minimal {u p d n : ℕ} (hu : 1 < u) (hdpos : 0 < d) (hd : p ^ d % u = 1)
    (hmin : ∀ k < d, 0 < k → p ^ k % u ≠ 1) (hn : p ^ n % u = 1) : d ∣ n := by
  have hk : p ^ (n % d) % u = 1 := by
    have e : p ^ n = (p ^ d) ^ (n / d) * p ^ (n % d) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have e2 : (p ^ d) ^ (n / d) % u = 1 := by
      rw [Nat.pow_mod, hd, one_pow, Nat.mod_eq_of_lt hu]
    rw [e, Nat.mul_mod, e2, one_mul, Nat.mod_mod] at hn
    exact hn
  by_contra hnd
  have hpos : 0 < n % d := Nat.pos_of_ne_zero fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0)
  exact hmin _ (Nat.mod_lt _ hdpos) hpos hk

/-- Item 2, the mixed row test. It looks for the order `d` of `p` modulo `u` (least `d > 0`
with `p ^ d ≡ 1`) and accepts when `d` is even, or when a listed number `r` divides `R_d(p)`,
is prime to `u` and has `r % u ≠ 1` (for instance the part of `R_d(p)` prime to `u`, or one
of its prime factors). -/
def mixedOK (u p : ℕ) (rs : List ℕ) : Bool :=
  (List.range u).any fun d => decide (0 < d) && p ^ d % u == 1 &&
    (List.range d).all (fun k => k == 0 || p ^ k % u != 1) &&
    (d % 2 == 0 || rs.any fun r => gsum d p % r == 0 && r % u != 0 && r % u != 1)

/-- Item 2. An accepted mixed test excludes every row `R_n(p) = t ^ x * u ^ y` with `n` odd,
`y > 0`, `t` prime and `t ≡ 1 (mod u)`. -/
theorem mixedOK_spec {u p : ℕ} {rs : List ℕ} (hu : u.Prime) (h : mixedOK u p rs = true)
    {t n x y : ℕ} (ht : t.Prime) (htu : t % u = 1) (hn : Odd n) (hy : 0 < y)
    (hrow : ∑ i ∈ range n, p ^ i = t ^ x * u ^ y) : False := by
  rw [← gsum_eq] at hrow
  have hu1 := hu.one_lt
  have hun : u ∣ gsum n p := by
    rw [hrow]; exact Dvd.dvd.mul_left (dvd_pow_self u hy.ne') _
  have hpn := pow_mod_of_dvd_gsum hu1 hun
  simp only [mixedOK, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨d, -, ⟨⟨⟨hd0, hd⟩, hmin⟩, hcase⟩⟩ := h
  have hmin' : ∀ k < d, 0 < k → p ^ k % u ≠ 1 := fun k hk hk0 => by
    rcases hmin k hk with h0 | h1
    · omega
    · exact h1
  have hdn := dvd_of_minimal hu1 hd0 hd hmin' hpn
  rcases hcase with hev | ⟨r, -, ⟨⟨hr, hr0⟩, hr1⟩⟩
  · obtain ⟨c, rfl⟩ := hdn
    rw [Nat.odd_mul] at hn
    exact (Nat.not_even_iff_odd.mpr hn.1) (Nat.even_iff.mpr hev)
  · have hrd : r ∣ gsum n p := (Nat.dvd_of_mod_eq_zero hr).trans (gsum_dvd p hdn)
    rw [hrow] at hrd
    have hcop : Nat.Coprime r (u ^ y) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp
        ((Nat.Prime.coprime_iff_not_dvd hu).mpr fun hd' => hr0 (Nat.mod_eq_zero_of_dvd hd'))))
    obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow ht).mp (hcop.dvd_of_dvd_mul_right hrd)
    apply hr1
    rw [Nat.pow_mod, htu, one_pow, Nat.mod_eq_of_lt hu1]

/-! ## Pure rows -/

/-- Strips factors 2, with fuel. -/
def oddPartAux : ℕ → ℕ → ℕ
  | 0, m => m
  | k + 1, m => if m % 2 = 0 ∧ 0 < m then oddPartAux k (m / 2) else m

/-- The odd part of `m > 0`. -/
def oddPart (m : ℕ) : ℕ := oddPartAux m m

theorem exists_two_pow_mul_oddPartAux (k m : ℕ) : ∃ a, m = 2 ^ a * oddPartAux k m := by
  induction k generalizing m with
  | zero => exact ⟨0, by simp [oddPartAux]⟩
  | succ k ih =>
    by_cases hc : m % 2 = 0 ∧ 0 < m
    · obtain ⟨a, ha⟩ := ih (m / 2)
      refine ⟨a + 1, ?_⟩
      simp only [oddPartAux, hc.1, hc.2, and_self, ↓reduceIte]
      rw [pow_succ, mul_comm (2 ^ a) 2, mul_assoc, ← ha]
      omega
    · exact ⟨0, by simp only [oddPartAux, hc, ↓reduceIte]; simp⟩

/-- Item 3, the pure row test: no residue `x` modulo `p` has `x ^ h ≡ 1` and
`R_u(x) + u ≡ 0`, where `h` is the odd part of `p - 1`. -/
def pureOK (u p : ℕ) : Bool :=
  (List.range p).all fun x => !(x ^ oddPart (p - 1) % p == 1 && (gsum u x + u) % p == 0)

/-- Item 3. An accepted pure test excludes every row `R_n(p) = t ^ x` with `n > 0` and `x`
odd, when `p ∣ q + 1` and `R_u(t) = q u`. -/
theorem pureOK_spec {u p : ℕ} (hp : p.Prime) (h : pureOK u p = true) {t q n x : ℕ}
    (hn : 0 < n) (hx : Odd x) (hrow : ∑ i ∈ range n, p ^ i = t ^ x) (hpq : p ∣ q + 1)
    (hR : ∑ i ∈ range u, t ^ i = q * u) : False := by
  have := Fact.mk hp
  have hrow' : ∑ i ∈ range n, (p : ZMod p) ^ i = (t : ZMod p) ^ x := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) hrow
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [ZMod.natCast_self, sum_range_succ'] at hrow'
  simp only [ne_eq, Nat.add_one_ne_zero, not_false_eq_true, zero_pow, sum_const_zero,
    pow_zero, zero_add] at hrow'
  have htx : (t : ZMod p) ^ x = 1 := hrow'.symm
  have ht0 : (t : ZMod p) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by obtain ⟨k, rfl⟩ := hx; omega)] at htx
    exact zero_ne_one htx
  have hF : (t : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ht0
  have hg : (t : ZMod p) ^ (x.gcd (p - 1)) = 1 := pow_gcd_eq_one.mpr ⟨htx, hF⟩
  obtain ⟨a, ha⟩ := exists_two_pow_mul_oddPartAux (p - 1) (p - 1)
  have hgd : x.gcd (p - 1) ∣ oddPart (p - 1) := by
    have h1 : x.gcd (p - 1) ∣ 2 ^ a * oddPart (p - 1) := by
      rw [oddPart, ← ha]; exact Nat.gcd_dvd_right _ _
    have hc : Nat.Coprime (x.gcd (p - 1)) (2 ^ a) :=
      Nat.Coprime.pow_right _ (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _)
        (Nat.coprime_two_right.mpr hx))
    exact hc.dvd_of_dvd_mul_left h1
  have hth : (t : ZMod p) ^ oddPart (p - 1) = 1 := by
    obtain ⟨c, hc⟩ := hgd
    rw [hc, pow_mul, hg, one_pow]
  have hR' : ∑ i ∈ range u, (t : ZMod p) ^ i = (q : ZMod p) * u := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) hR
  have hq : ((q + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpq
  push_cast at hq
  simp only [pureOK, List.all_eq_true, List.mem_range, Bool.not_eq_true', Bool.and_eq_false_iff,
    beq_eq_false_iff_ne, ne_eq] at h
  rcases h (t % p) (Nat.mod_lt _ hp.pos) with h1 | h2
  · apply h1
    have e : (((t % p) ^ oddPart (p - 1) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      push_cast; rw [ZMod.natCast_mod, hth]
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hp.one_lt] at e
    exact e
  · apply h2
    have e : ((gsum u (t % p) + u : ℕ) : ZMod p) = 0 := by
      rw [gsum_eq]; push_cast; rw [ZMod.natCast_mod, hR']
      linear_combination (u : ZMod p) * hq
    exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp e)

/-! ## Prime envelope -/

/-- The bound `x/(x-1) ≤ m/(m-1)` for natural numbers `2 ≤ m ≤ x`. -/
theorem div_sub_one_le_of_le {m x : ℕ} (hm : 2 ≤ m) (hx : m ≤ x) :
    (x : ℚ) / (x - 1) ≤ (m : ℚ) / (m - 1) := by
  have hm' : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hx' : (m : ℚ) ≤ x := by exact_mod_cast hx
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem one_le_div_sub_one {m : ℕ} (hm : 2 ≤ m) : (1 : ℚ) ≤ (m : ℚ) / (m - 1) := by
  have hm' : (2 : ℚ) ≤ m := by exact_mod_cast hm
  rw [le_div_iff₀ (by linarith)]; linarith

/-- `envOK A lo L` checks that `L` lists, in increasing order, the primes at least 5 that are
outside `A`, starting from `lo`, with no such prime skipped. -/
def envOK (A : List ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | lo, b :: L => decide (Nat.Prime b) && decide (lo ≤ b) && decide (5 ≤ b) && !A.contains b &&
      (List.range' lo (b - lo)).all (fun c => !(decide (Nat.Prime c)) || A.contains c) &&
      envOK (b :: A) (b + 1) L

theorem envOK_ge {A : List ℕ} {lo : ℕ} {L : List ℕ} (h : envOK A lo L = true) :
    ∀ b ∈ L, 5 ≤ b := by
  induction L generalizing A lo with
  | nil => simp
  | cons b L ih =>
    simp only [envOK, Bool.and_eq_true, decide_eq_true_eq] at h
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1.1.1.2
    · exact ih h.2 c hc

theorem one_le_prod_map {L : List ℕ} (hL : ∀ b ∈ L, 2 ≤ b) :
    (1 : ℚ) ≤ (L.map fun b : ℕ => (b : ℚ) / (b - 1)).prod := by
  induction L with
  | nil => simp
  | cons b L ih =>
    rw [List.map_cons, List.prod_cons]
    exact one_le_mul_of_one_le_of_one_le (one_le_div_sub_one (hL b (by simp)))
      (ih fun c hc => hL c (by simp [hc]))

theorem prod_le_envelope_aux (L : List ℕ) :
    ∀ (A : List ℕ) (lo : ℕ), envOK A lo L = true →
      (∀ c, c.Prime → 5 ≤ c → c < lo → c ∈ A) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ 5 ≤ p ∧ p ∉ A) → P.card ≤ L.length →
      ∏ p ∈ P, ((p : ℚ) / (p - 1)) ≤ (L.map fun b : ℕ => (b : ℚ) / (b - 1)).prod := by
  induction L with
  | nil =>
    intro A lo _ _ P _ hc
    simp only [List.length_nil, Nat.le_zero, Finset.card_eq_zero] at hc
    subst hc; simp
  | cons b L ih =>
    intro A lo h hinv P hP hc
    have hge := envOK_ge h
    simp only [envOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      List.all_eq_true, List.mem_range'_1, Bool.or_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not, List.elem_eq_mem] at h
    obtain ⟨⟨⟨⟨⟨_, hlo⟩, hb5⟩, _⟩, hgap⟩, hrest⟩ := h
    have hgap' : ∀ c, c.Prime → lo ≤ c → c < b → c ∈ A := by
      intro c hc hlc hcb
      rcases hgap c ⟨hlc, by omega⟩ with h1 | h1
      · exact absurd hc h1
      · simpa using h1
    have hinv' : ∀ c, c.Prime → 5 ≤ c → c < b + 1 → c ∈ b :: A := by
      intro c hc hc5 hcb
      rcases lt_or_ge c lo with h1 | h1
      · exact List.mem_cons_of_mem _ (hinv c hc hc5 h1)
      · rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hcb) with h2 | h2
        · exact List.mem_cons_of_mem _ (hgap' c hc h1 h2)
        · rw [h2]; exact List.mem_cons_self
    have hbp : ∀ p ∈ P, b ≤ p := by
      intro p hp
      obtain ⟨hpp, hp5, hpA⟩ := hP p hp
      by_contra hlt
      push Not at hlt
      rcases lt_or_ge p lo with h1 | h1
      · exact hpA (hinv p hpp hp5 h1)
      · exact hpA (hgap' p hpp h1 hlt)
    have hY := ih (b :: A) (b + 1) hrest hinv'
    have hf0 : ∀ p ∈ P, (0 : ℚ) ≤ (p : ℚ) / (p - 1) := fun p hp =>
      le_trans zero_le_one (one_le_div_sub_one (by have := (hP p hp).2.1; omega))
    rw [List.map_cons, List.prod_cons]
    have hfb : (1 : ℚ) ≤ (b : ℚ) / (b - 1) := one_le_div_sub_one (by omega)
    by_cases hbP : b ∈ P
    · rw [← Finset.mul_prod_erase P _ hbP]
      refine mul_le_mul_of_nonneg_left (hY (P.erase b) ?_ ?_) (by linarith)
      · intro p hp
        obtain ⟨hne, hp'⟩ := Finset.mem_erase.mp hp
        obtain ⟨h1, h2, h3⟩ := hP p hp'
        exact ⟨h1, h2, by simp [hne, h3]⟩
      · rw [Finset.card_erase_of_mem hbP]; simp at hc; omega
    · rcases P.eq_empty_or_nonempty with rfl | ⟨m, hm⟩
      · rw [Finset.prod_empty]
        exact one_le_mul_of_one_le_of_one_le hfb
          (one_le_prod_map fun c hc => by have := hge c (by simp [hc]); omega)
      · rw [← Finset.mul_prod_erase P _ hm]
        refine mul_le_mul (div_sub_one_le_of_le (by omega) (hbp m hm)) (hY (P.erase m) ?_ ?_)
          (Finset.prod_nonneg fun p hp => hf0 p (Finset.mem_of_mem_erase hp)) (by linarith)
        · intro p hp
          have hp' := Finset.mem_of_mem_erase hp
          obtain ⟨h1, h2, h3⟩ := hP p hp'
          refine ⟨h1, h2, ?_⟩
          simp only [List.mem_cons, not_or]
          exact ⟨fun e => hbP (e ▸ hp'), h3⟩
        · rw [Finset.card_erase_of_mem hm]; simp at hc; omega

/-- Item 4, prime envelope. If `envOK A 5 L` holds (so `L` lists the first `L.length` primes at
least 5 outside `A`), then for every set `P` of primes at least 5 outside `A` with
`P.card ≤ L.length`, `∏ p ∈ P, p / (p - 1) ≤ ∏ b ∈ L, b / (b - 1)`. -/
theorem prod_le_envelope {A L : List ℕ} (hL : envOK A 5 L = true) {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ 5 ≤ p) (hPA : ∀ p ∈ P, p ∉ A) (hcard : P.card ≤ L.length) :
    ∏ p ∈ P, ((p : ℚ) / (p - 1)) ≤ (L.map fun b : ℕ => (b : ℚ) / (b - 1)).prod :=
  prod_le_envelope_aux L A 5 hL (fun _ _ h5 h => absurd h (by omega)) P
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2, hPA p hp⟩) hcard

/-- The rational envelope as a quotient of two natural products. -/
theorem prod_map_eq_div {L : List ℕ} (hL : ∀ b ∈ L, 1 ≤ b) :
    (L.map fun b : ℕ => (b : ℚ) / (b - 1)).prod =
      (L.prod : ℚ) / (((L.map fun b => b - 1).prod : ℕ) : ℚ) := by
  induction L with
  | nil => simp
  | cons b L ih =>
    rw [List.map_cons, List.prod_cons, ih fun c hc => hL c (by simp [hc]), List.prod_cons,
      List.map_cons, List.prod_cons, div_mul_div_comm, Nat.cast_mul, Nat.cast_mul,
      Nat.cast_sub (hL b (by simp)), Nat.cast_one]

theorem prod_map_lt_two {L : List ℕ} (hL : ∀ b ∈ L, 2 ≤ b)
    (h : L.prod < 2 * (L.map fun b => b - 1).prod) :
    (L.map fun b : ℕ => (b : ℚ) / (b - 1)).prod < 2 := by
  rw [prod_map_eq_div fun b hb => by have := hL b hb; omega]
  have hpos : 0 < (L.map fun b => b - 1).prod := by
    apply List.prod_pos
    intro c hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    have := hL b hb; omega
  rw [div_lt_iff₀ (by exact_mod_cast hpos)]
  exact_mod_cast h

/-! ## The table -/

/-- One receiver row: both tests accept each listed prime (with its divisor list), `L` is the
envelope of length `u + 1 + z` outside the listed primes, and the envelope is below 2. -/
def sieveRow (u z : ℕ) (A : List (ℕ × List ℕ)) (L : List ℕ) : Bool :=
  A.all (fun pr => mixedOK u pr.1 pr.2 && pureOK u pr.1) && envOK (A.map Prod.fst) 5 L &&
    L.length == u + 1 + z && decide (L.prod < 2 * (L.map fun b => b - 1).prod)

theorem sieveRow_spec {u z : ℕ} {A : List (ℕ × List ℕ)} {L : List ℕ}
    (h : sieveRow u z A L = true) :
    (∀ pr ∈ A, mixedOK u pr.1 pr.2 = true ∧ pureOK u pr.1 = true) ∧
    ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ 5 ≤ p) → (∀ p ∈ P, p ∉ A.map Prod.fst) →
      P.card ≤ u + 1 + z → ∏ p ∈ P, ((p : ℚ) / (p - 1)) < 2 := by
  simp only [sieveRow, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨hA, hL⟩, hlen⟩, hlt⟩ := h
  refine ⟨hA, fun P hP hPA hc => ?_⟩
  have hge := envOK_ge hL
  exact lt_of_le_of_lt (prod_le_envelope hL hP hPA (by omega))
    (prod_map_lt_two (fun b hb => by have := hge b hb; omega) hlt)

/-- The receivers `u`, the number `z` of possible pure rows into `u`, the primes `p` with
their divisor lists, and the envelopes. -/
def sieveTable : List (ℕ × ℕ × List (ℕ × List ℕ) × List ℕ) :=
  [(11, 0, [(5, [71])], [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]),
   (13, 0, [(5, [])], [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59]),
   (17, 0, [(5, []), (7, []), (13, [])],
    [11, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83]),
   (19, 0, [(5, [25699]), (7, [3]), (11, [7]), (13, []), (17, [307])],
    [19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103]),
   (23, 0, [(5, []), (13, [6493334761]), (17, []), (19, [])],
    [7, 11, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103,
     107, 109, 113]),
   (29, 0, [(5, []), (7, [4733]), (11, []), (17, []), (19, []), (23, [5336717])],
    [13, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109,
     113, 127, 131, 137, 139, 149, 151, 157, 163]),
   (31, 1, [(7, [25524524247]), (11, []), (13, []), (17, []), (19, [27206320842069531]),
     (23, []), (29, [])],
    [5, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
     127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181]),
   (37, 0, [(5, []), (7, [181773]), (11, []), (13, []), (17, []), (23, []), (31, [])],
    [19, 29, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
     127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211]),
   (41, 0, [(5, []), (7, []), (11, []), (13, []), (17, []), (23, []), (29, []), (37, [46981])],
    [19, 31, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127,
     131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227,
     229, 233, 239]),
   (47, 0, [(5, []), (7, [97052295532201831]), (11, []), (13, []),
     (17, [26552618219228090162977481]), (29, []), (41, []), (43, [])],
    [19, 23, 31, 37, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127,
     131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227,
     229, 233, 239, 241, 251, 257, 263, 269, 271])]

/-- Item 5. Every row of the table passes its checks (kernel evaluation). -/
theorem sieveTable_ok :
    sieveTable.all (fun r => sieveRow r.1 r.2.1 r.2.2.1 r.2.2.2) = true := by
  decide +kernel

/-- Item 5. For each receiver row `(u, z, A, L)` of the table, both tests accept every prime
of `A`, and every set of at most `u + 1 + z` primes at least 5 outside `A` has
`∏ p / (p - 1) < 2`. -/
theorem sieveTable_spec {u z : ℕ} {A : List (ℕ × List ℕ)} {L : List ℕ}
    (hr : (u, z, A, L) ∈ sieveTable) :
    (∀ pr ∈ A, mixedOK u pr.1 pr.2 = true ∧ pureOK u pr.1 = true) ∧
    ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ 5 ≤ p) → (∀ p ∈ P, p ∉ A.map Prod.fst) →
      P.card ≤ u + 1 + z → ∏ p ∈ P, ((p : ℚ) / (p - 1)) < 2 :=
  sieveRow_spec (List.all_eq_true.mp sieveTable_ok _ hr)

end ReceiverSieve
end OddPerfect

#print axioms OddPerfect.ReceiverSieve.gsum_eq
#print axioms OddPerfect.ReceiverSieve.mod_three_of_receiver
#print axioms OddPerfect.ReceiverSieve.not_three_dvd_succ_of_receiver
#print axioms OddPerfect.ReceiverSieve.geom_sum_mul_len
#print axioms OddPerfect.ReceiverSieve.gsum_dvd
#print axioms OddPerfect.ReceiverSieve.pow_mod_of_dvd_gsum
#print axioms OddPerfect.ReceiverSieve.dvd_of_minimal
#print axioms OddPerfect.ReceiverSieve.mixedOK_spec
#print axioms OddPerfect.ReceiverSieve.exists_two_pow_mul_oddPartAux
#print axioms OddPerfect.ReceiverSieve.pureOK_spec
#print axioms OddPerfect.ReceiverSieve.prod_le_envelope
#print axioms OddPerfect.ReceiverSieve.prod_map_lt_two
#print axioms OddPerfect.ReceiverSieve.sieveRow_spec
#print axioms OddPerfect.ReceiverSieve.sieveTable_ok
#print axioms OddPerfect.ReceiverSieve.sieveTable_spec
#print axioms OddPerfect.ReceiverSieve.geom_six_zmod_three
#print axioms OddPerfect.ReceiverSieve.geom_zmod_three
#print axioms OddPerfect.ReceiverSieve.div_sub_one_le_of_le
#print axioms OddPerfect.ReceiverSieve.one_le_div_sub_one
#print axioms OddPerfect.ReceiverSieve.envOK_ge
#print axioms OddPerfect.ReceiverSieve.one_le_prod_map
#print axioms OddPerfect.ReceiverSieve.prod_le_envelope_aux
#print axioms OddPerfect.ReceiverSieve.prod_map_eq_div
