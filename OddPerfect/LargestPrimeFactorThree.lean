import OddPerfect.LargestPrimeFactorTwo

/-!
# Modular row certificates for the largest prime factor search

`OddPerfect.LargestPrimeFactorTwo` certifies a row of the search `LPF.search` by showing, for
every odd prime `r ≤ (B - 3) / 2 + 1` outside a short list `X`, that `σ (p ^ (r - 1))` has a
prime factor above `B`. It computes the number `σ (p ^ (r - 1))` itself, which has about
`r log p` digits. This module proves a checker, `LPF3.exists_primeFactor_gt_of_cert3`, for
the same search in which these numbers are only computed modulo smaller numbers.

Let `r` be an odd prime. A prime factor `q ≠ r` of `σ (p ^ (r - 1))` is `1` modulo `2 r`, and
`r ^ 2` does not divide `σ (p ^ (r - 1))` (lifting the exponent). Let `M_r` be the product of
the primes `q ≤ B` with `q ≡ 1 (mod 2 r)`; a global list `DR` holds the pairs `(r, M_r)` with
`M_r ≠ 1` and is checked once (`drOK`). For a row prime `p` the number
`x = σ (p ^ (r - 1)) mod M_r` is computed from `p ^ r mod (p - 1) M_r` in three steps of base
`128`, and `S = gcd (x, M_r)`. If `S = 1`, or if `σ (p ^ (r - 1)) / S` is again coprime to
`M_r` (computed modulo `S M_r`), and `r S < 2 ^ ((r - 1) ⌊log₂ p⌋)`, then the quotient
`σ (p ^ (r - 1)) / S` is above `r`, is not divisible by `r ^ 2` and has no prime factor `q ≤ B`
other than `r`; so it has a prime factor above `B`. For a prime `r` with no prime `q ≤ B`,
`q ≡ 1 (mod 2 r)`, the same argument needs no computation at all.

The checks use `Nat.mod`, `Nat.mul` and the other functions directly, which the kernel evaluates
faster than the notation. All checks are run by the kernel (`decide +kernel`) on data found
outside Lean.
-/

namespace OddPerfect

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace LPF3

open LPF LPF2

/-! ## The checks -/

/-- `b ^ e % m`, computed with the digits of `e` in base `128` (exact for every `e`). -/
def pw (b m e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.mod (Nat.pow (Nat.mod (Nat.mul (Nat.mod (Nat.pow (Nat.mod (Nat.pow b
    (Nat.div e 16384)) m) 128) m) (Nat.mod (Nat.pow b (Nat.mod (Nat.div e 128) 128)) m)) m) 128) m)
    (Nat.mod (Nat.pow b (Nat.mod e 128)) m)) m

/-- `σ (p ^ (r - 1)) % m` for `p ≥ 3`, from `p ^ r % ((p - 1) m)`. -/
def phiMod (p r m : ℕ) : ℕ :=
  Nat.div (Nat.sub (pw p (Nat.mul (Nat.sub p 1) m) r) 1) (Nat.sub p 1)

/-- `gcd x M`, computed as `gcd (M % x) x`. -/
def gcdR (x M : ℕ) : ℕ := Nat.gcd (Nat.mod M x) x

/-- With `x = σ (p ^ (r - 1)) % (S M_r)`: `S ∣ x`, `x / S` is coprime to `M_r`, and
`r S < 2 ^ ((r - 1) w)`, where `w = ⌊log₂ p⌋` and so `2 ^ ((r - 1) w) ≤ p ^ (r - 1)`. -/
def killS (w r Mr S x : ℕ) : Bool :=
  Nat.beq (Nat.mod x S) 0 && Nat.beq (gcdR (Nat.div x S) Mr) 1 &&
    Nat.blt (Nat.mul r S) (Nat.pow 2 (Nat.mul (Nat.sub r 1) w))

/-- The check for `S = gcd (σ (p ^ (r - 1)), M_r)`. -/
def killH (p w r Mr S : ℕ) : Bool :=
  bif Nat.beq S 1 then true else killS w r Mr S (phiMod p r (Nat.mul S Mr))

/-- `σ (p ^ (r - 1))` has a prime factor above `B` when `M_r` is a multiple of every prime
`q ≤ B` with `q ≡ 1 (mod 2 r)`; the divisor `S` is computed. -/
def killG (p w r Mr : ℕ) : Bool := killH p w r Mr (gcdR (phiMod p r Mr) Mr)

/-- The divisor `S` listed for `r`, or `0`. -/
def lookS (r : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | a :: l => bif Nat.beq a.1 r then a.2 else lookS r l

/-- One entry `(r, M_r)` of `DR` for the row prime `p`: `r` is killed with the computed divisor,
lies in `X`, or is killed with the divisor listed in `EXS`; `w = ⌊log₂ p⌋`. -/
def stepOK (p w : ℕ) (X : List ℕ) (EXS : List (ℕ × ℕ)) (x : ℕ × ℕ) : Bool :=
  killG p w x.1 x.2 || memB x.1 X ||
    killS w x.1 x.2 (lookS x.1 EXS) (phiMod p x.1 (Nat.mul (lookS x.1 EXS) x.2))

/-- Primality for `n < (K + 1) ^ 2`: trial division for `n ≤ K`, and `gcd (n, Q) = 1` above,
where `Q = 2 ∏ primesUpTo K`. -/
def primeG (Q K n : ℕ) : Bool :=
  bif Nat.blt K n then Nat.beq (Nat.gcd (Nat.mod Q n) n) 1 else isPrimeF n

/-- `c` if `c` is prime (by `primeG`), else `1`. -/
def pick (Q K c : ℕ) : ℕ := bif primeG Q K c then c else 1

/-- The product of the primes among `2 k r + 1`, `1 ≤ k ≤ K'`. -/
def cprodP (Q K r : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => Nat.mul (pick Q K (Nat.add (Nat.mul (Nat.mul 2 (k + 1)) r) 1)) (cprodP Q K r k)

/-- The global list `DR`: walking the primes `r` of the list, an entry `(r, M_r)` of `DR` has
`M_r` the product of the primes `2 k r + 1 ≤ B`, and every other `r` has no such prime. -/
def drOK (B Q K : ℕ) : List ℕ → List (ℕ × ℕ) → Bool
  | [], [] => true
  | [], _ :: _ => false
  | r :: l, [] =>
      Nat.beq (cprodP Q K r (Nat.div (Nat.sub B 1) (Nat.mul 2 r))) 1 && drOK B Q K l []
  | r :: l, x :: DR => bif Nat.beq x.1 r then
        Nat.beq (cprodP Q K r (Nat.div (Nat.sub B 1) (Nat.mul 2 r))) x.2 && drOK B Q K l DR
      else Nat.beq (cprodP Q K r (Nat.div (Nat.sub B 1) (Nat.mul 2 r))) 1 &&
        drOK B Q K l (x :: DR)

/-- The certificate `(p, R, X, EXS, EX)` of the row `R` of `p`: every entry of `DR` passes
`stepOK`, and `X`, `EX` and the list `L` are used as in `LPF2.rowOK`. -/
def rowOK3 (M XU : ℕ) (DR : List (ℕ × ℕ)) (L : List ℕ)
    (c : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)) : Bool :=
  DR.all (stepOK c.1 (Nat.log2 c.1) c.2.2.1 c.2.2.2.1) && Nat.beq (XU % xpow c.2.2.1) 0 &&
    c.2.2.2.2.all (fun x => killOK M c.1 x.1 x.2) &&
    L.all (fun e => !parityOK c.1 e || memB e c.2.1 ||
      !Nat.beq (xpow c.2.2.1 % (e + 1)) 0 || c.2.2.2.2.any (fun x => Nat.beq ((e + 1) % x.1) 0))

/-! ## Facts copied from the second checker -/

private theorem nbeq_iff {a b : ℕ} : (!Nat.beq a b) = true ↔ a ≠ b := by
  cases h : Nat.beq a b
  · simpa using Nat.ne_of_beq_eq_false h
  · simpa using Nat.eq_of_beq_eq_true h

private theorem noDiv_sound {n : ℕ} : ∀ {f d : ℕ}, noDiv n f d = true →
    ∀ k, d ≤ k → k < d + f → k * k ≤ n → ¬ k ∣ n
  | 0, d, _, k, h1, h2, _ => by omega
  | f + 1, d, h, k, h1, h2, h3 => by
    simp only [noDiv, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, nbeq_iff] at h
    rcases h with h | ⟨hd, h⟩
    · have := Nat.mul_le_mul h1 h1; omega
    · rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact fun hk => hd (Nat.mod_eq_zero_of_dvd hk)
      · exact noDiv_sound h k hlt (by omega) h3

private theorem noDiv_complete {n : ℕ} : ∀ {f d : ℕ}, 2 ≤ d → (∀ k, d ≤ k → k < n → ¬ k ∣ n) →
    noDiv n f d = true
  | 0, _, _, _ => rfl
  | f + 1, d, hd, h => by
    simp only [noDiv, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, nbeq_iff]
    by_cases hlt : n < d * d
    · exact Or.inl hlt
    · right
      have hdn : d < n := by nlinarith
      exact ⟨fun h0 => h d le_rfl hdn (Nat.dvd_of_mod_eq_zero h0),
        noDiv_complete (by omega) fun k hk => h k (by omega)⟩

private theorem isPrimeF_iff {n : ℕ} : isPrimeF n = true ↔ n.Prime := by
  simp only [isPrimeF, Bool.and_eq_true, Nat.ble_eq]
  constructor
  · rintro ⟨h2, h⟩
    rw [Nat.prime_def_minFac]
    refine ⟨h2, ?_⟩
    by_contra hne
    have hlt : n.minFac < n := lt_of_le_of_ne (Nat.minFac_le (by omega)) hne
    have hsq := Nat.minFac_sq_le_self (by omega) (fun hp => hne (Nat.Prime.minFac_eq hp))
    have h2m := (Nat.minFac_prime (by omega : n ≠ 1)).two_le
    exact noDiv_sound h n.minFac h2m (by omega) (by rw [← pow_two]; exact hsq)
      (Nat.minFac_dvd n)
  · intro hp
    refine ⟨hp.two_le, noDiv_complete le_rfl fun k hk hkn hd => ?_⟩
    have := (Nat.prime_def_lt.mp hp).2 k hkn hd
    omega

private theorem mem_primesUpTo {B q : ℕ} : q ∈ primesUpTo B ↔ q ≤ B ∧ q ≠ 2 ∧ q.Prime := by
  simp only [primesUpTo, List.mem_filter, List.mem_range, Bool.and_eq_true, isPrimeF_iff,
    nbeq_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, h2, h3⟩


private theorem memB_iff {q : ℕ} : ∀ {l : List ℕ}, memB q l = true ↔ q ∈ l
  | [] => by simp [memB]
  | a :: l => by
    simp only [memB, Bool.or_eq_true, Nat.beq_eq, memB_iff, List.mem_cons]
    exact ⟨fun h => h.elim (fun h => Or.inl h.symm) Or.inr,
      fun h => h.elim (fun h => Or.inl h.symm) Or.inr⟩

private theorem gs_mul (p e : ℕ) : gs p e * (p - 1) = p ^ (e + 1) - 1 :=
  Nat.div_mul_cancel (Nat.sub_one_dvd_pow_sub_one p (e + 1))

/-- `σ (p ^ (d - 1)) ∣ σ (p ^ (n - 1))` when `d ∣ n`. -/
private theorem gs_dvd {p d n : ℕ} (hp : 2 ≤ p) (hd : 0 < d) (hdn : d ∣ n) (hn : 0 < n) :
    gs p (d - 1) ∣ gs p (n - 1) := by
  have h1 := gs_mul p (d - 1)
  have h2 := gs_mul p (n - 1)
  rw [Nat.sub_add_cancel hd] at h1
  rw [Nat.sub_add_cancel hn] at h2
  have h3 : p ^ d - 1 ∣ p ^ n - 1 := Nat.pow_sub_one_dvd_pow_sub_one p hdn
  rw [← h1, ← h2] at h3
  exact Nat.dvd_of_mul_dvd_mul_right (by omega) h3

/-- `σ (p ^ (r - 1)) = r` modulo a prime `q` with `p ≡ 1 (mod q)`. -/
private theorem dvd_of_cast_eq_one {p q r : ℕ} [Fact q.Prime] (hp : 2 ≤ p)
    (h1 : ((p : ℕ) : ZMod q) = 1) (hq : q ∣ gs p (r - 1)) (hr : 0 < r) : q ∣ r := by
  have hsum : gs p (r - 1) = ∑ k ∈ Finset.range r, p ^ k := by
    rw [Nat.geomSum_eq hp, gs, Nat.sub_add_cancel hr]
  rw [← ZMod.natCast_eq_zero_iff] at hq ⊢
  rw [hsum] at hq
  push_cast at hq
  simpa [h1] using hq

/-- Every prime factor `q ≠ r` of `σ (p ^ (r - 1))`, `r` prime, satisfies `r ∣ q - 1`. -/
private theorem dvd_sub_one_of_dvd_gs {p q r : ℕ} (hp : 2 ≤ p) (hr : r.Prime) (hq : q.Prime)
    (hqd : q ∣ gs p (r - 1)) (hqr : q ≠ r) : r ∣ q - 1 := by
  have := Fact.mk hq
  have hpow : q ∣ p ^ r - 1 := by
    have := gs_mul p (r - 1)
    rw [Nat.sub_add_cancel hr.pos] at this
    rw [← this]; exact hqd.mul_right _
  have hone : 1 ≤ p ^ r := Nat.one_le_pow _ _ (by omega)
  have hcast : ((p : ZMod q)) ^ r = 1 := by
    have := (ZMod.natCast_eq_natCast_iff (p ^ r) 1 q).mpr
      ((Nat.modEq_iff_dvd' hone).mpr hpow).symm
    simpa using this
  have hord : orderOf (p : ZMod q) ∣ r := orderOf_dvd_of_pow_eq_one hcast
  rcases (Nat.dvd_prime hr).mp hord with h1 | h1
  · exfalso
    rw [orderOf_eq_one_iff] at h1
    exact hqr ((Nat.prime_dvd_prime_iff_eq hq hr).mp (dvd_of_cast_eq_one hp h1 hqd hr.pos))
  · have hne : (p : ZMod q) ≠ 0 := by
      intro h0
      rw [h0, zero_pow hr.ne_zero] at hcast
      exact zero_ne_one hcast
    rw [← h1]
    exact ZMod.orderOf_dvd_card_sub_one hne

/-- For odd `p` and odd prime `r`, every prime factor `q ≠ r` of `σ (p ^ (r - 1))` is
`1` modulo `2 r`. -/
private theorem two_mul_dvd_sub_one {p q r : ℕ} (hp : 2 ≤ p) (hpo : p % 2 = 1) (hr : r.Prime)
    (hr2 : r ≠ 2) (hq : q.Prime) (hqd : q ∣ gs p (r - 1)) (hqr : q ≠ r) : 2 * r ∣ q - 1 := by
  have h1 := dvd_sub_one_of_dvd_gs hp hr hq hqd hqr
  have hq2 : q ≠ 2 := by
    rintro rfl
    have := Fact.mk Nat.prime_two
    have hc : ((p : ℕ) : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.mpr (Nat.odd_iff.mpr hpo)
    have := dvd_of_cast_eq_one hp hc hqd hr.pos
    exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp this).symm
  have h2 : 2 ∣ q - 1 := by
    rcases hq.eq_two_or_odd with he | ho
    · exact absurd he hq2
    · exact ⟨q / 2, by omega⟩
  have hcop : Nat.Coprime 2 r :=
    (Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2)
  exact hcop.mul_dvd_of_dvd_of_dvd h2 h1

/-- A killed number `d` gives a prime factor of `σ (p ^ (d - 1))` above `B`. -/
private theorem killOK_sound {B p d S : ℕ} (h : killOK (2 * (primesUpTo B).prod) p d S = true) :
    ∃ q, q.Prime ∧ B < q ∧ q ∣ gs p (d - 1) := by
  simp only [killOK, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨⟨hS, hu⟩, hc⟩ := h
  set u := gs p (d - 1) / S
  have hud : u ∣ gs p (d - 1) := Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero hS)
  have hq := Nat.minFac_prime (show u ≠ 1 by omega)
  refine ⟨u.minFac, hq, ?_, (Nat.minFac_dvd u).trans hud⟩
  by_contra hle
  push Not at hle
  have hM : u.minFac ∣ 2 * (primesUpTo B).prod := by
    by_cases h2 : u.minFac = 2
    · rw [h2]; exact dvd_mul_right 2 _
    · exact (List.dvd_prod (mem_primesUpTo.mpr ⟨hle, h2, hq⟩)).mul_left 2
  have := Nat.dvd_gcd (Nat.minFac_dvd u) hM
  rw [hc] at this
  exact hq.one_lt.ne' (Nat.dvd_one.mp this)

private theorem listOK_sound {XU : ℕ} : ∀ {f : ℕ} {L : List ℕ}, listOK XU f L = true →
    ∀ e, 1 ≤ e → e ≤ f → (e + 1) ∣ XU → e ∈ L
  | 0, _, _, e, h1, h2, _ => by omega
  | f + 1, L, h, e, h1, h2, hd => by
    unfold listOK at h
    cases L with
    | nil =>
      simp only [Bool.and_eq_true, nbeq_iff] at h
      rcases Nat.eq_or_lt_of_le h2 with rfl | hlt
      · exact absurd (Nat.mod_eq_zero_of_dvd hd) h.1
      · exact listOK_sound h.2 e h1 (by omega) hd
    | cons a L' =>
      simp only at h
      cases ha : Nat.beq a (f + 1) <;> rw [ha] at h <;> simp only [cond] at h
      · simp only [Bool.and_eq_true, nbeq_iff] at h
        rcases Nat.eq_or_lt_of_le h2 with rfl | hlt
        · exact absurd (Nat.mod_eq_zero_of_dvd hd) h.1
        · exact listOK_sound h.2 e h1 (by omega) hd
      · rw [Nat.beq_eq] at ha
        rcases Nat.eq_or_lt_of_le h2 with rfl | hlt
        · rw [← ha]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (listOK_sound h e h1 (by omega) hd)

/-- A number below `2 ^ 20` whose prime factors lie in `2 :: X` divides `xpow X`. -/
private theorem dvd_xpow {X : List ℕ} {n : ℕ} (hn : 0 < n) (hn20 : n < 2 ^ 20)
    (h : ∀ q, q.Prime → q ∣ n → q = 2 ∨ q ∈ X) : n ∣ xpow X := by
  unfold xpow
  by_cases hY : 2 * X.prod = 0
  · rw [hY]; simp
  have hY20 : (2 * X.prod) ^ 20 ≠ 0 := pow_ne_zero _ hY
  rw [← Nat.factorization_le_iff_dvd hn.ne' hY20]
  intro q
  rw [Nat.factorization_pow]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  by_cases hq : q.Prime
  · by_cases hqn : q ∣ n
    · have hqY : q ∣ 2 * X.prod := by
        rcases h q hq hqn with rfl | hx
        · exact dvd_mul_right 2 _
        · exact (List.dvd_prod hx).mul_left 2
      have h1 : 1 ≤ (2 * X.prod).factorization q :=
        (hq.dvd_iff_one_le_factorization hY).mp hqY
      have h2 : n.factorization q < 20 := by
        have hle : q ^ n.factorization q ≤ n := Nat.le_of_dvd hn (Nat.ordProj_dvd n q)
        have h3 : q ^ n.factorization q < q ^ 20 :=
          lt_of_le_of_lt hle (lt_of_lt_of_le hn20 (Nat.pow_le_pow_left hq.two_le 20))
        exact (Nat.pow_lt_pow_iff_right hq.one_lt).mp h3
      nlinarith
    · rw [Nat.factorization_eq_zero_of_not_dvd hqn]; omega
  · rw [Nat.factorization_eq_zero_of_not_prime n hq]; omega
/-! ## Modular arithmetic of the checks -/

private theorem pw_eq (b m e : ℕ) : pw b m e = b ^ e % m := by
  show ((((b ^ (e / 16384) % m) ^ 128 % m) * (b ^ (e / 128 % 128) % m) % m) ^ 128 % m) *
    (b ^ (e % 128) % m) % m = b ^ e % m
  have he : e = (e / 16384 * 128 + e / 128 % 128) * 128 + e % 128 := by omega
  have A : (b ^ (e / 16384) % m) ^ 128 % m ≡ (b ^ (e / 16384)) ^ 128 [MOD m] :=
    (Nat.mod_modEq _ _).trans ((Nat.mod_modEq _ m).pow 128)
  have B1 : (b ^ (e / 16384) % m) ^ 128 % m * (b ^ (e / 128 % 128) % m) % m ≡
      (b ^ (e / 16384)) ^ 128 * b ^ (e / 128 % 128) [MOD m] :=
    (Nat.mod_modEq _ _).trans (A.mul (Nat.mod_modEq _ m))
  have C : ((b ^ (e / 16384) % m) ^ 128 % m * (b ^ (e / 128 % 128) % m) % m) ^ 128 % m ≡
      ((b ^ (e / 16384)) ^ 128 * b ^ (e / 128 % 128)) ^ 128 [MOD m] :=
    (Nat.mod_modEq _ _).trans (B1.pow 128)
  have D : ((b ^ (e / 16384) % m) ^ 128 % m * (b ^ (e / 128 % 128) % m) % m) ^ 128 % m *
      (b ^ (e % 128) % m) % m ≡
      ((b ^ (e / 16384)) ^ 128 * b ^ (e / 128 % 128)) ^ 128 * b ^ (e % 128) [MOD m] :=
    (Nat.mod_modEq _ _).trans (C.mul (Nat.mod_modEq _ m))
  have hb : ((b ^ (e / 16384)) ^ 128 * b ^ (e / 128 % 128)) ^ 128 * b ^ (e % 128) = b ^ e := by
    rw [← pow_mul, ← pow_add, ← pow_mul, ← pow_add, ← he]
  rw [hb] at D
  rw [← D, Nat.mod_mod]

private theorem gs_ge {p : ℕ} (hp : 2 ≤ p) (e : ℕ) : p ^ e ≤ gs p e := by
  have h1 : 1 ≤ p ^ e := Nat.one_le_pow _ _ (by omega)
  have h3 : p ^ e * (p - 1) + p ^ e = p ^ (e + 1) := by
    rw [pow_succ, ← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have h4 : p ^ e * (p - 1) ≤ gs p e * (p - 1) := by rw [gs_mul]; omega
  exact Nat.le_of_mul_le_mul_right h4 (by omega)

private theorem gs_pos {p : ℕ} (hp : 2 ≤ p) (e : ℕ) : 0 < gs p e :=
  lt_of_lt_of_le (Nat.one_le_pow _ _ (by omega)) (gs_ge hp e)

private theorem phiMod_eq {p r : ℕ} (hp : 3 ≤ p) (hr : 1 ≤ r) (m : ℕ) :
    phiMod p r m = gs p (r - 1) % m := by
  show (pw p ((p - 1) * m) r - 1) / (p - 1) = _
  rw [pw_eq]
  have hg := gs_mul p (r - 1)
  rw [Nat.sub_add_cancel hr] at hg
  have hone : 1 ≤ p ^ r := Nat.one_le_pow _ _ (by omega)
  set Φ := gs p (r - 1)
  have hpr : p ^ r = (p - 1) * Φ + 1 := by rw [mul_comm]; omega
  have key : p ^ r % ((p - 1) * m) = (p - 1) * (Φ % m) + 1 := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp [hpr]
    · have hd := Nat.mod_add_div Φ m
      have e1 : p ^ r = (p - 1) * (Φ % m) + 1 + (p - 1) * m * (Φ / m) := by
        rw [hpr]; conv_lhs => rw [← hd]
        ring
      rw [e1, Nat.add_mul_mod_self_left]
      apply Nat.mod_eq_of_lt
      have := Nat.mod_lt Φ h0
      have h2 : (p - 1) * (Φ % m + 1) ≤ (p - 1) * m := Nat.mul_le_mul_left _ (by omega)
      have h3 : 2 ≤ p - 1 := by omega
      nlinarith
  rw [key, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by omega)]

private theorem gcdR_eq (x M : ℕ) : gcdR x M = Nat.gcd x M := (Nat.gcd_rec x M).symm

/-! ## Killing a prime `r` -/

/-- `r ^ 2 ∤ σ (p ^ (r - 1))` for an odd prime `r`. -/
private theorem sq_not_dvd {p r : ℕ} (hp : 2 ≤ p) (hr : r.Prime) (hr2 : r ≠ 2) :
    ¬ r ^ 2 ∣ gs p (r - 1) := by
  intro h
  have := Fact.mk hr
  have hg := gs_mul p (r - 1)
  rw [Nat.sub_add_cancel hr.pos] at hg
  have hrg : r ∣ gs p (r - 1) := (dvd_pow_self r two_ne_zero).trans h
  have hpow : r ∣ p ^ r - 1 := by rw [← hg]; exact hrg.mul_right _
  have hone : 1 ≤ p ^ r := Nat.one_le_pow _ _ (by omega)
  have hp1 : r ∣ p - 1 := by
    have hc : ((p : ZMod r)) ^ r = 1 := by
      have := (ZMod.natCast_eq_natCast_iff (p ^ r) 1 r).mpr
        ((Nat.modEq_iff_dvd' hone).mpr hpow).symm
      simpa using this
    rw [ZMod.pow_card] at hc
    have h1 : p ≡ 1 [MOD r] := (ZMod.natCast_eq_natCast_iff p 1 r).mp (by simpa using hc)
    exact (Nat.modEq_iff_dvd' (by omega)).mp h1.symm
  have hrp : ¬ r ∣ p := by
    intro h'
    have := Nat.dvd_sub h' hp1
    rw [show p - (p - 1) = 1 by omega] at this
    exact hr.one_lt.ne' (Nat.dvd_one.mp this)
  have hlte := padicValNat.pow_sub_pow (p := r) (hr.odd_of_ne_two hr2) (by omega : 1 < p)
    (by simpa using hp1) hrp hr.ne_zero
  have hg0 : gs p (r - 1) ≠ 0 := (gs_pos hp _).ne'
  rw [one_pow, padicValNat_self, ← hg, padicValNat.mul hg0 (by omega)] at hlte
  have h2 := (padicValNat_dvd_iff_le hg0).mp h
  omega

private theorem two_pow_le {p : ℕ} (hp : 2 ≤ p) (k : ℕ) : 2 ^ (k * Nat.log2 p) ≤ p ^ k := by
  rw [mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.log2_self_le (by omega)) k

private theorem lt_two_pow_pred {r : ℕ} (hr : 3 ≤ r) : r < 2 ^ (r - 1) := by
  induction r, hr using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have : 2 ^ (n + 1 - 1) = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

private theorem small_size {p r : ℕ} (hp : 2 ≤ p) (hr3 : 3 ≤ r) :
    r < 2 ^ ((r - 1) * Nat.log2 p) := by
  have h1 : 1 ≤ Nat.log2 p := (Nat.le_log2 (by omega)).mpr (by simpa using hp)
  exact lt_of_lt_of_le (lt_two_pow_pred hr3)
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ h1))

/-- The core of every kill: a divisor `S` of `σ (p ^ (r - 1))` with `r S < 2 ^ (r - 1)` whose
cofactor is coprime to a multiple `M_r` of all primes `q ≤ B`, `q ≡ 1 (mod 2 r)`, and
`r S < 2 ^ ((r - 1) ⌊log₂ p⌋)`. -/
private theorem core_kill {B p r Mr S : ℕ} (hp : 2 ≤ p) (hpo : p % 2 = 1) (hr : r.Prime)
    (hr2 : r ≠ 2) (hcomp : ∀ q, q.Prime → q ≤ B → 2 * r ∣ q - 1 → q ∣ Mr)
    (hS : S ∣ gs p (r - 1)) (hcop : Nat.gcd (gs p (r - 1) / S) Mr = 1)
    (hsize : r * S < 2 ^ ((r - 1) * Nat.log2 p)) :
    ∃ q, q.Prime ∧ B < q ∧ q ∣ gs p (r - 1) := by
  set Φ := gs p (r - 1) with hΦ
  set u := Φ / S with hu
  have hSu : S * u = Φ := Nat.mul_div_cancel' hS
  have hge : 2 ^ ((r - 1) * Nat.log2 p) ≤ Φ := (two_pow_le hp _).trans (gs_ge hp (r - 1))
  have hur : r < u := by
    by_contra hle
    push Not at hle
    have := Nat.mul_le_mul_left S hle
    nlinarith
  have hud : u ∣ Φ := Dvd.intro_left S hSu
  have hsq : ¬ r ^ 2 ∣ u := fun h => sq_not_dvd hp hr hr2 (h.trans hud)
  have hex : ∃ q, q.Prime ∧ q ∣ u ∧ q ≠ r := by
    by_contra hno
    push Not at hno
    have hu0 : u ≠ 0 := by omega
    obtain ⟨k, hpow⟩ : ∃ k, u = r ^ k :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hu0 (fun hd hdu => hno _ hd hdu)⟩
    rcases Nat.lt_or_ge k 2 with hk | hk
    · have : u ≤ r := by
        rw [hpow]
        calc r ^ k ≤ r ^ 1 := Nat.pow_le_pow_right hr.pos (by omega)
          _ = r := pow_one r
      omega
    · exact hsq (hpow ▸ pow_dvd_pow r hk)
  obtain ⟨q, hq, hqu, hqr⟩ := hex
  refine ⟨q, hq, ?_, hqu.trans hud⟩
  by_contra hle
  push Not at hle
  have h2r := two_mul_dvd_sub_one hp hpo hr hr2 hq (hqu.trans hud) hqr
  have := Nat.dvd_gcd hqu (hcomp q hq hle h2r)
  rw [hcop] at this
  exact hq.one_lt.ne' (Nat.dvd_one.mp this)

private theorem killS_sound {B p r Mr S : ℕ} (hp3 : 3 ≤ p) (hpo : p % 2 = 1) (hr : r.Prime)
    (hr2 : r ≠ 2) (hcomp : ∀ q, q.Prime → q ≤ B → 2 * r ∣ q - 1 → q ∣ Mr)
    (h : killS (Nat.log2 p) r Mr S (phiMod p r (Nat.mul S Mr)) = true) :
    ∃ q, q.Prime ∧ B < q ∧ q ∣ gs p (r - 1) := by
  have hx : phiMod p r (Nat.mul S Mr) = gs p (r - 1) % (S * Mr) := phiMod_eq hp3 hr.pos _
  unfold killS at h
  rw [hx] at h
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  set Φ := gs p (r - 1) with hΦ
  have h1' : Φ % (S * Mr) % S = 0 := h1
  have h2' : Nat.gcd (Φ % (S * Mr) / S) Mr = 1 := by rw [← gcdR_eq]; exact h2
  have h3' : r * S < 2 ^ ((r - 1) * Nat.log2 p) := h3
  have hΦ0 : 0 < Φ := gs_pos (by omega) _
  have hS0 : 0 < S := by
    rcases Nat.eq_zero_or_pos S with h0 | h0
    · rw [h0, zero_mul, Nat.mod_zero, Nat.mod_zero] at h1'; omega
    · exact h0
  have hdecomp := Nat.mod_add_div Φ (S * Mr)
  have hSx : S ∣ Φ % (S * Mr) := Nat.dvd_of_mod_eq_zero h1'
  obtain ⟨a, ha⟩ := hSx
  have e1 : Φ = S * (a + Mr * (Φ / (S * Mr))) := by
    conv_lhs => rw [← hdecomp]
    rw [ha]; ring
  have hSΦ : S ∣ Φ := ⟨_, e1⟩
  have hq : Φ / S = a + Mr * (Φ / (S * Mr)) := by
    conv_lhs => rw [e1]
    rw [Nat.mul_div_cancel_left _ hS0]
  have hcop : Nat.gcd (Φ / S) Mr = 1 := by
    rw [hq, Nat.gcd_add_mul_left_left]
    rw [ha, Nat.mul_div_cancel_left _ hS0] at h2'
    exact h2'
  exact core_kill (by omega) hpo hr hr2 hcomp hSΦ hcop h3'

private theorem killG_sound {B p r Mr : ℕ} (hp3 : 3 ≤ p) (hpo : p % 2 = 1) (hr : r.Prime)
    (hr2 : r ≠ 2) (hcomp : ∀ q, q.Prime → q ≤ B → 2 * r ∣ q - 1 → q ∣ Mr)
    (h : killG p (Nat.log2 p) r Mr = true) : ∃ q, q.Prime ∧ B < q ∧ q ∣ gs p (r - 1) := by
  unfold killG killH at h
  have hS : gcdR (phiMod p r Mr) Mr = Nat.gcd (gs p (r - 1)) Mr := by
    rw [gcdR_eq, phiMod_eq hp3 hr.pos, ← Nat.gcd_rec, Nat.gcd_comm]
  cases hb : Nat.beq (gcdR (phiMod p r Mr) Mr) 1 <;> rw [hb] at h <;> simp only [cond] at h
  · exact killS_sound hp3 hpo hr hr2 hcomp h
  · rw [Nat.beq_eq, hS] at hb
    have hr3 : 3 ≤ r := by have := hr.two_le; omega
    exact core_kill (by omega) hpo hr hr2 hcomp (one_dvd _) (by rw [Nat.div_one]; exact hb)
      (by rw [mul_one]; exact small_size (by omega) hr3)

private theorem stepOK_sound {B p r Mr : ℕ} {X : List ℕ} {EXS : List (ℕ × ℕ)} (hp3 : 3 ≤ p)
    (hpo : p % 2 = 1) (hr : r.Prime) (hr2 : r ≠ 2)
    (hcomp : ∀ q, q.Prime → q ≤ B → 2 * r ∣ q - 1 → q ∣ Mr)
    (h : stepOK p (Nat.log2 p) X EXS (r, Mr) = true) :
    r ∈ X ∨ ∃ q, q.Prime ∧ B < q ∧ q ∣ gs p (r - 1) := by
  unfold stepOK at h
  simp only [Bool.or_eq_true, memB_iff] at h
  rcases h with (h | h) | h
  · exact Or.inr (killG_sound hp3 hpo hr hr2 hcomp h)
  · exact Or.inl h
  · exact Or.inr (killS_sound hp3 hpo hr hr2 hcomp h)

/-! ## Primality by a greatest common divisor -/

private theorem primeG_iff {Q K n : ℕ} (hK2 : 2 ≤ K) (hQ : 2 * (primesUpTo K).prod = Q)
    (hn : n < (K + 1) * (K + 1)) : primeG Q K n = true ↔ n.Prime := by
  unfold primeG
  cases hb : Nat.blt K n <;> simp only [cond]
  · exact isPrimeF_iff
  · rw [Nat.blt_eq] at hb
    rw [Nat.beq_eq, show Nat.gcd (Nat.mod Q n) n = Nat.gcd n Q from (Nat.gcd_rec n Q).symm]
    have hdvdQ : ∀ m, m.Prime → m ≤ K → m ∣ Q := by
      intro m hm hmK
      rw [← hQ]
      by_cases h2 : m = 2
      · rw [h2]; exact dvd_mul_right 2 _
      · exact (List.dvd_prod (mem_primesUpTo.mpr ⟨hmK, h2, hm⟩)).mul_left 2
    constructor
    · intro hg
      by_contra hnp
      have hm := Nat.minFac_prime (show n ≠ 1 by omega)
      have hsq : n.minFac * n.minFac ≤ n := by
        rw [← pow_two]; exact Nat.minFac_sq_le_self (by omega) hnp
      have hmK : n.minFac ≤ K := by
        by_contra hc
        have := Nat.mul_le_mul (show K + 1 ≤ n.minFac by omega) (show K + 1 ≤ n.minFac by omega)
        omega
      have := Nat.dvd_gcd (Nat.minFac_dvd n) (hdvdQ _ hm hmK)
      rw [hg] at this
      exact hm.one_lt.ne' (Nat.dvd_one.mp this)
    · intro hp
      rw [← Nat.Coprime, hp.coprime_iff_not_dvd]
      intro hd
      rw [← hQ] at hd
      rcases (Nat.Prime.dvd_mul hp).mp hd with h2 | h2
      · have := Nat.le_of_dvd (by norm_num) h2; omega
      · obtain ⟨q, hq, hnq⟩ := (Nat.prime_iff.mp hp).exists_mem_multiset_dvd
          (s := ((primesUpTo K : List ℕ) : Multiset ℕ)) (by rwa [Multiset.prod_coe])
        rw [Multiset.mem_coe] at hq
        obtain ⟨hqK, -, hqp⟩ := mem_primesUpTo.mp hq
        have := (Nat.prime_dvd_prime_iff_eq hp hqp).mp hnq
        omega

/-- The odd primes up to `B` by `primeG` (trial division up to `K`, a greatest common divisor
with `Q = 2 ∏ primesUpTo K` above), when `B < (K + 1) ^ 2`. -/
theorem primesUpTo_eq_filterG {B K Q : ℕ} (hK2 : 2 ≤ K) (hK : B < (K + 1) * (K + 1))
    (hQ : 2 * (primesUpTo K).prod = Q) :
    primesUpTo B = (List.range (B + 1)).filter (fun n => !Nat.beq n 2 && primeG Q K n) := by
  unfold primesUpTo
  refine List.filter_congr fun n hn => ?_
  rw [List.mem_range] at hn
  congr 1
  rw [Bool.eq_iff_iff, isPrimeF_iff, primeG_iff hK2 hQ (by omega)]

/-! ## The global list `DR` -/

private theorem cprodP_dvd {Q K r : ℕ} (hK2 : 2 ≤ K) (hQ : 2 * (primesUpTo K).prod = Q)
    {k : ℕ} (hk : 1 ≤ k) (hc : (2 * k * r + 1).Prime) (hcK : 2 * k * r + 1 < (K + 1) * (K + 1)) :
    ∀ {K'}, k ≤ K' → 2 * k * r + 1 ∣ cprodP Q K r K'
  | 0, h => by omega
  | K' + 1, h => by
    show 2 * k * r + 1 ∣ pick Q K (2 * (K' + 1) * r + 1) * cprodP Q K r K'
    rcases Nat.eq_or_lt_of_le h with he | hlt
    · have hp : primeG Q K (2 * k * r + 1) = true := (primeG_iff hK2 hQ hcK).mpr hc
      rw [← he]
      unfold pick
      rw [hp]
      exact dvd_mul_right _ _
    · exact dvd_mul_of_dvd_right (cprodP_dvd hK2 hQ hk hc hcK (by omega)) _

private theorem dvd_cprodP {B Q K r q : ℕ} (hK2 : 2 ≤ K) (hQ : 2 * (primesUpTo K).prod = Q)
    (hK : B < (K + 1) * (K + 1)) (hr : 0 < r) (hq : q.Prime) (hqB : q ≤ B)
    (h2r : 2 * r ∣ q - 1) : q ∣ cprodP Q K r ((B - 1) / (2 * r)) := by
  obtain ⟨k, hk⟩ := h2r
  have hq2 := hq.two_le
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, mul_zero] at hk; omega
    · exact h0
  have hqe : q = 2 * k * r + 1 := by
    have : 2 * k * r = 2 * r * k := by ring
    omega
  have hkK : k ≤ (B - 1) / (2 * r) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have : k * (2 * r) = 2 * k * r := by ring
    omega
  rw [hqe] at hq ⊢
  exact cprodP_dvd hK2 hQ hk1 hq (by omega) hkK

private theorem drOK_sound {B Q K : ℕ} :
    ∀ {l : List ℕ} {DR : List (ℕ × ℕ)}, drOK B Q K l DR = true →
    (∀ x ∈ DR, ∃ r ∈ l, x.1 = r ∧ x.2 = cprodP Q K r ((B - 1) / (2 * r))) ∧
    (∀ r ∈ l, (∃ x ∈ DR, x.1 = r) ∨ cprodP Q K r ((B - 1) / (2 * r)) = 1)
  | [], [], _ => by simp
  | [], _ :: _, h => by simp [drOK] at h
  | r :: l, [], h => by
    unfold drOK at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨-, ih2⟩ := drOK_sound h.2
    refine ⟨by simp, fun r' hr' => ?_⟩
    rcases List.mem_cons.mp hr' with rfl | hl
    · exact Or.inr h.1
    · exact ih2 r' hl
  | r :: l, x :: DR, h => by
    unfold drOK at h
    cases hb : Nat.beq x.1 r <;> rw [hb] at h <;> simp only [cond, Bool.and_eq_true, Nat.beq_eq] at h
    · obtain ⟨ih1, ih2⟩ := drOK_sound h.2
      refine ⟨fun y hy => ?_, fun r' hr' => ?_⟩
      · obtain ⟨r'', hr'', h'⟩ := ih1 y hy
        exact ⟨r'', List.mem_cons_of_mem _ hr'', h'⟩
      · rcases List.mem_cons.mp hr' with rfl | hl
        · exact Or.inr h.1
        · exact ih2 r' hl
    · rw [Nat.beq_eq] at hb
      obtain ⟨ih1, ih2⟩ := drOK_sound h.2
      refine ⟨fun y hy => ?_, fun r' hr' => ?_⟩
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨r, List.mem_cons_self, hb, h.1.symm⟩
        · obtain ⟨r'', hr'', h'⟩ := ih1 y hy
          exact ⟨r'', List.mem_cons_of_mem _ hr'', h'⟩
      · rcases List.mem_cons.mp hr' with rfl | hl
        · exact Or.inl ⟨x, List.mem_cons_self, hb⟩
        · rcases ih2 r' hl with ⟨y, hy, hy'⟩ | h'
          · exact Or.inl ⟨y, List.mem_cons_of_mem _ hy, hy'⟩
          · exact Or.inr h'

/-- What the global check `drOK` gives: every entry `(r, M_r)` of `DR` has `M_r` divisible by
every prime `q ≤ B` with `2 r ∣ q - 1`, and every odd prime `r ≤ B` without an entry has no
such prime `q`. -/
def DRGood (B : ℕ) (DR : List (ℕ × ℕ)) : Prop :=
  (∀ x ∈ DR, ∀ q, q.Prime → q ≤ B → 2 * x.1 ∣ q - 1 → q ∣ x.2) ∧
  ∀ r, r.Prime → r ≠ 2 → r ≤ B → (∃ x ∈ DR, x.1 = r) ∨
    ∀ q, q.Prime → q ≤ B → ¬ 2 * r ∣ q - 1

/-- Soundness of the global check `drOK` over the odd primes up to `B`. -/
theorem drOK_good {B K Q : ℕ} {DR : List (ℕ × ℕ)} (hK2 : 2 ≤ K) (hK : B < (K + 1) * (K + 1))
    (hQ : 2 * (primesUpTo K).prod = Q) (h : drOK B Q K (primesUpTo B) DR = true) :
    DRGood B DR := by
  obtain ⟨h1, h2⟩ := drOK_sound h
  refine ⟨fun x hx q hq hqB h2r => ?_, fun r hr hr2 hrB => ?_⟩
  · obtain ⟨r, hrP, hxr, hx2⟩ := h1 x hx
    rw [hx2]
    rw [hxr] at h2r
    exact dvd_cprodP hK2 hQ hK (mem_primesUpTo.mp hrP).2.2.pos hq hqB h2r
  · rcases h2 r (mem_primesUpTo.mpr ⟨hrB, hr2, hr⟩) with h' | h'
    · exact Or.inl h'
    · refine Or.inr fun q hq hqB h2r => ?_
      have := dvd_cprodP hK2 hQ hK hr.pos hq hqB h2r
      rw [h'] at this
      exact hq.one_lt.ne' (Nat.dvd_one.mp this)

/-! ## Soundness of the row check -/

/-- A row certificate accepted by `rowOK3` gives the meaning `LPF2.RowCover` of its row. -/
theorem rowOK3_sound {B XU : ℕ} {DR : List (ℕ × ℕ)} {L : List ℕ}
    {c : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)} (hB : B ≤ 2 ^ 21)
    (hDR : DRGood B DR) (hL : listOK XU ((B - 3) / 2) L = true)
    (h : rowOK3 (2 * (primesUpTo B).prod) XU DR L c = true) :
    RowCover B c.1 c.2.1 := by
  obtain ⟨p, R, X, EXS, EX⟩ := c
  simp only [rowOK3, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hst, hXU⟩, hEX⟩, hLc⟩ := h
  intro hp hp2 f hf1 hf2 hpar hsm
  have hp2' : 2 ≤ p := hp.two_le
  have hpo : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hp3 : 3 ≤ p := by omega
  have hnz : 0 < f + 1 := by omega
  -- a killed divisor of `f + 1` is impossible
  have hkill : ∀ d, d ∣ f + 1 → ∀ q, q.Prime → B < q → q ∣ gs p (d - 1) → False := by
    intro d hd q hq hBq hqd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hnz
    have := hqd.trans (gs_dvd hp2' hd0 hd hnz)
    rw [Nat.add_sub_cancel] at this
    exact absurd (hsm q hq this) (by omega)
  -- every odd prime factor of `f + 1` lies in `X`
  have hX : ∀ r, r.Prime → r ∣ f + 1 → r = 2 ∨ r ∈ X := by
    intro r hr hrd
    by_cases hr2 : r = 2
    · exact Or.inl hr2
    right
    have hrle : r ≤ f + 1 := Nat.le_of_dvd hnz hrd
    rcases hDR.2 r hr hr2 (by omega) with ⟨x, hx, hxr⟩ | hno
    · obtain ⟨r', Mr⟩ := x
      simp only at hxr
      subst hxr
      rcases stepOK_sound hp3 hpo hr hr2 (hDR.1 _ hx) (hst _ hx) with hx' | ⟨q, hq, hBq, hqd⟩
      · exact hx'
      · exact (hkill r' hrd q hq hBq hqd).elim
    · have hr3 : 3 ≤ r := by have := hr.two_le; omega
      obtain ⟨q, hq, hBq, hqd⟩ := core_kill (Mr := 1) (S := 1) hp2' hpo hr hr2
        (fun q hq hqB h2r => absurd h2r (hno q hq hqB)) (one_dvd _)
        (Nat.gcd_one_right _) (by rw [mul_one]; exact small_size hp2' hr3)
      exact (hkill r hrd q hq hBq hqd).elim
  have hfx : f + 1 ∣ xpow X := dvd_xpow hnz (by omega) hX
  have hfL : f ∈ L := listOK_sound hL f hf1 (by omega)
    (hfx.trans (Nat.dvd_of_mod_eq_zero hXU))
  have hc := hLc f hfL
  simp only [Bool.or_eq_true, Bool.not_eq_true', memB_iff, List.any_eq_true, Nat.beq_eq] at hc
  rcases hc with ((hc | hc) | hc) | ⟨x, hx, hxd⟩
  · rw [hpar] at hc; exact absurd hc (by decide)
  · exact hc
  · rw [Bool.eq_false_iff, Ne, Nat.beq_eq] at hc
    exact absurd (Nat.mod_eq_zero_of_dvd hfx) hc
  · obtain ⟨q, hq, hBq, hqd⟩ := killOK_sound (hEX x hx)
    exact (hkill x.1 (Nat.dvd_of_mod_eq_zero hxd) q hq hBq hqd).elim

/-! ## Splitting the search into separate kernel checks -/

/-- One step of `LPF.search` with no pending divisor: the first undecided prime `q` either
divides `N` or not. -/
theorem search_nil {B : ℕ} {P : List ℕ} {M D : ℕ} {T : List (ℕ × List ℕ)} {fuel : ℕ}
    {ex : List (ℕ × ℕ)} {nd : List ℕ} {q : ℕ}
    (hf : (P.filter (fun q => !memF q ex && !memB q nd)).head? = some q)
    (h1 : search B P M D T fuel ex [q] nd = true)
    (h2 : search B P M D T fuel ex [] (q :: nd) = true) :
    search B P M D T (fuel + 1) ex [] nd = true := by
  unfold search
  cases hfl : P.filter (fun q => !memF q ex && !memB q nd) with
  | nil => rw [hfl] at hf; simp at hf
  | cons a l =>
    rw [hfl] at hf
    simp only [List.head?_cons, Option.some.injEq] at hf
    subst hf
    simp only [h1, h2, Bool.and_self, Bool.or_true]

/-- One step of `LPF.search` at a pending divisor `p` whose exponent is already fixed. -/
theorem search_cons_old {B : ℕ} {P : List ℕ} {M D : ℕ} {T : List (ℕ × List ℕ)} {fuel : ℕ}
    {ex : List (ℕ × ℕ)} {p : ℕ} {rest nd : List ℕ} (hm : memF p ex = true)
    (h : search B P M D T fuel ex rest nd = true) :
    search B P M D T (fuel + 1) ex (p :: rest) nd = true := by
  unfold search
  simp only [hm, if_true, h, Bool.or_true]

/-- One step of `LPF.search` at a new pending divisor `p` whose candidate exponents are `es`:
it suffices that every `e` of `es` is excluded by parity or the search succeeds after it. -/
theorem search_cons_all {B : ℕ} {P : List ℕ} {M D : ℕ} {T : List (ℕ × List ℕ)} {fuel : ℕ}
    {ex : List (ℕ × ℕ)} {p : ℕ} {rest nd es : List ℕ} (hm : memF p ex = false)
    (hc : cands nd p (getRow B M T p) = es)
    (h : ∀ e ∈ es, (Nat.beq (e % 2) 1 && ex.any fun x => Nat.beq (x.2 % 2) 1) = true ∨
      search B P M D T fuel ((p, e) :: ex) (newPrimes P (gs p e) ++ rest) nd = true) :
    search B P M D T (fuel + 1) ex (p :: rest) nd = true := by
  unfold search
  simp only [hm, hc, Bool.false_eq_true, if_false]
  have : es.all (fun e => (Nat.beq (e % 2) 1 && ex.any fun x => Nat.beq (x.2 % 2) 1) ||
      search B P M D T fuel ((p, e) :: ex) (newPrimes P (gs p e) ++ rest) nd) = true :=
    List.all_eq_true.mpr fun e he => by
      rcases h e he with h1 | h1 <;> simp only [h1, Bool.true_or, Bool.or_true]
  rw [this, Bool.or_true]

/-- An accepted search with rows certified by `rowOK3` gives a prime factor above `B`. The list
`P` of odd primes up to `B`, the numbers `M = 2 ∏ P`, `D = ∏ (q - 1)` and
`Q = 2 ∏ primesUpTo K`, the global list `DR`, the certificates `C`, from which the table `T`
is read off, and the list `L` are given explicitly and checked. -/
theorem exists_primeFactor_gt_of_cert3 {B K Q : ℕ} {P : List ℕ} {M D XU : ℕ} {L : List ℕ}
    {DR : List (ℕ × ℕ)} {T : List (ℕ × List ℕ)}
    {C : List (ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ))}
    (hP : primesUpTo B = P) (hM : 2 * P.prod = M) (hD : (P.map (· - 1)).prod = D)
    (hB : B ≤ 2 ^ 21) (hK2 : 2 ≤ K) (hK : B < (K + 1) * (K + 1))
    (hQ : 2 * (primesUpTo K).prod = Q) (hDR : drOK B Q K P DR = true)
    (hTC : C.map (fun c => (c.1, c.2.1)) = T)
    (hL : listOK XU ((B - 3) / 2) L = true) (hC : C.all (rowOK3 M XU DR L) = true)
    (hs : search B P M D T 1000 [] [] [] = true)
    (h : OddPerfect N) : ∃ p ∈ N.primeFactors, B < p := by
  subst hP hM hD hTC
  have hgood := drOK_good hK2 hK hQ hDR
  by_contra hne
  push Not at hne
  refine LPF2.search_sound h hne (fun x hx => ?_) _ _ _ _ hs ⟨by simp, by simp, by simp⟩
    ⟨by simp, by simp, by simp, by simp, by simp⟩
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  exact rowOK3_sound hB hgood hL (List.all_eq_true.mp hC c hc)

end LPF3

end OddPerfect

#print axioms OddPerfect.LPF3.primesUpTo_eq_filterG
#print axioms OddPerfect.LPF3.drOK_good
#print axioms OddPerfect.LPF3.rowOK3_sound
#print axioms OddPerfect.LPF3.search_nil
#print axioms OddPerfect.LPF3.search_cons_old
#print axioms OddPerfect.LPF3.search_cons_all
#print axioms OddPerfect.LPF3.exists_primeFactor_gt_of_cert3
