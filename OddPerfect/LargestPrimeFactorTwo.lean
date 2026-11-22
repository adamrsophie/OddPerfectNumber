import OddPerfect.LargestPrimeFactor

/-!
# Certified rows for the largest prime factor search

`OddPerfect.LargestPrimeFactor` runs the search `LPF.search` with a table `T` of rows, and its
checker `LPF.exists_primeFactor_gt_of_search` asks the kernel to recompute every row with
`LPF.row`, which tests every exponent `e ≤ (B - 3) / 2` with large greatest common divisors.
That test dominates the cost for larger bounds `B`. This module proves a second checker,
`LPF2.exists_primeFactor_gt_of_cert`, for the same search, in which a row only has to contain
the admissible exponents, and this is certified by cheaper facts.

For a row prime `p` with row `R`, a certificate `(p, R, X, SP, EX)` consists of

* a list `X` of odd primes; every other odd prime `r ≤ (B - 3) / 2 + 1` is *killed*: the
  number `σ (p ^ (r - 1))` has a prime factor above `B`. This is shown by dividing it by a
  given divisor `S` (listed in `SP` when `S ≠ 1`) and checking that the quotient `u` is above
  `1` and divisible neither by `r` nor by any `2 k r + 1 ≤ B`: a prime factor of
  `σ (p ^ (r - 1))` other than `r` is `1` modulo `2 r` (`dvd_sub_one_of_dvd_gs`);
* a list `EX` of further killed numbers `d` (any `d`, shown with a divisor `S` and a quotient
  coprime to `M = 2 ∏ P`).

If `e` is an admissible exponent of `p`, then `σ (p ^ (r - 1)) ∣ σ (p ^ e)` for each prime
`r ∣ e + 1`, so no prime factor of `e + 1` other than `2` is killed, and `e + 1` divides
`(2 ∏ X) ^ 20`. A global list `L` contains every `e` with `e + 1 ∣ XU`, where `XU` is a multiple
of all the numbers `(2 ∏ X) ^ 20`, and for each `e ∈ L` the certificate checks that `e` is in
`R`, fails Euler's parity condition, or is excluded by `X` or `EX`.

All checks are run by the kernel (`decide +kernel`) on data found outside Lean.
-/

namespace OddPerfect

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace LPF2

open LPF

/-! ## The certificate checks -/

/-- `S` divides `σ (p ^ (d - 1))` and the quotient is above `1` and coprime to `M`. -/
def killOK (M p d S : ℕ) : Bool :=
  Nat.beq (gs p (d - 1) % S) 0 && Nat.blt 1 (gs p (d - 1) / S) &&
    Nat.beq (Nat.gcd (gs p (d - 1) / S) M) 1

/-- No `2 k r + 1` with `1 ≤ k ≤ K` divides `u`. -/
def candOK (u r : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => !Nat.beq (u % (2 * (k + 1) * r + 1)) 0 && candOK u r k

/-- For a prime `r`: `S` divides `σ (p ^ (r - 1))`, the quotient `u` is above `1`, and neither
`r` nor any `2 k r + 1 ≤ B` divides `u`. -/
def killP (B p r S : ℕ) : Bool :=
  Nat.beq (gs p (r - 1) % S) 0 && Nat.blt 1 (gs p (r - 1) / S) &&
    !Nat.beq (gs p (r - 1) / S % r) 0 && candOK (gs p (r - 1) / S) r ((B - 1) / (2 * r))

/-- Every prime `r` of the list with `r ≤ cut` lies in `X` or is killed; `SP` lists the
divisors `S` different from `1`, in the order of the list. -/
def primeOK (B p cut : ℕ) (X : List ℕ) : List ℕ → List (ℕ × ℕ) → Bool
  | [], _ => true
  | r :: l, SP => cond (Nat.blt cut r || memB r X) (primeOK B p cut X l SP)
      (match SP with
       | a :: SP' => cond (Nat.beq a.1 r) (killP B p r a.2 && primeOK B p cut X l SP')
           (killP B p r 1 && primeOK B p cut X l SP)
       | [] => killP B p r 1 && primeOK B p cut X l [])

/-- `(2 ∏ X) ^ 20`. -/
def xpow (X : List ℕ) : ℕ := (2 * X.prod) ^ 20

/-- Every `e` with `1 ≤ e ≤ f` and `e + 1 ∣ XU` lies in `L`, which is listed in decreasing
order. -/
def listOK (XU : ℕ) : ℕ → List ℕ → Bool
  | 0, _ => true
  | e + 1, L => match L with
    | a :: L' => cond (Nat.beq a (e + 1)) (listOK XU e L')
        (!Nat.beq (XU % (e + 2)) 0 && listOK XU e L)
    | [] => !Nat.beq (XU % (e + 2)) 0 && listOK XU e []

/-- The certificate `(p, R, X, SP, EX)` of the row `R` of `p`. -/
def rowOK (B M XU : ℕ) (P L : List ℕ)
    (c : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)) : Bool :=
  primeOK B c.1 ((B - 3) / 2 + 1) c.2.2.1 P c.2.2.2.1 && Nat.beq (XU % xpow c.2.2.1) 0 &&
    c.2.2.2.2.all (fun x => killOK M c.1 x.1 x.2) &&
    L.all (fun e => !parityOK c.1 e || memB e c.2.1 ||
      !Nat.beq (xpow c.2.2.1 % (e + 1)) 0 || c.2.2.2.2.any (fun x => Nat.beq ((e + 1) % x.1) 0))

/-- The meaning of a row: it contains every exponent `f` of the odd prime `p` that satisfies
the conditions known for an odd perfect number all of whose prime factors are at most `B`. -/
def RowCover (B p : ℕ) (R : List ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ f, 1 ≤ f → 2 * f + 3 ≤ B → parityOK p f = true →
    (∀ q, q.Prime → q ∣ gs p f → q ≤ B) → f ∈ R

/-! ## Basic facts -/

private theorem sigma_eq_gs {p : ℕ} (hp : p.Prime) (e : ℕ) : σ 1 (p ^ e) = gs p e := by
  rw [sigma_one_apply_prime_pow hp, gs, Nat.geomSum_eq hp.two_le]

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

/-- Primality of `n` by trial division by the members of `Q` up to `√n`. -/
def primeBy (Q : List ℕ) (n : ℕ) : Bool :=
  Nat.ble 2 n && Q.all (fun q => Nat.blt n (q * q) || !Nat.beq (n % q) 0)

private theorem primeBy_iff {Q : List ℕ} {K n : ℕ} (hQ : ∀ q ∈ Q, 2 ≤ q)
    (hK : ∀ m, m.Prime → m ≤ K → m ∈ Q) (hn : n < (K + 1) * (K + 1)) :
    primeBy Q n = true ↔ n.Prime := by
  simp only [primeBy, Bool.and_eq_true, Nat.ble_eq, List.all_eq_true, Bool.or_eq_true,
    Nat.blt_eq, nbeq_iff]
  constructor
  · rintro ⟨h2, h⟩
    by_contra hnp
    have hm := Nat.minFac_prime (show n ≠ 1 by omega)
    have hsq : n.minFac * n.minFac ≤ n := by
      rw [← pow_two]; exact Nat.minFac_sq_le_self (by omega) hnp
    have hmK : n.minFac ≤ K := by
      by_contra hc
      have := Nat.mul_le_mul (show K + 1 ≤ n.minFac by omega) (show K + 1 ≤ n.minFac by omega)
      omega
    rcases h _ (hK _ hm hmK) with h1 | h1
    · omega
    · exact h1 (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n))
  · intro hp
    refine ⟨hp.two_le, fun q hq => ?_⟩
    by_cases hqn : q ∣ n
    · rcases hp.eq_one_or_self_of_dvd q hqn with h1 | h1
      · have := hQ q hq; omega
      · left; subst h1; have := hp.two_le; nlinarith
    · right; exact fun h0 => hqn (Nat.dvd_of_mod_eq_zero h0)

/-- The odd primes up to `B` by trial division by `2` and the odd primes up to `K`, when
`B < (K + 1) ^ 2`. -/
theorem primesUpTo_eq_filter {B K : ℕ} (hK : B < (K + 1) * (K + 1)) :
    primesUpTo B = (List.range (B + 1)).filter
      (fun n => !Nat.beq n 2 && primeBy (2 :: primesUpTo K) n) := by
  unfold primesUpTo
  refine List.filter_congr fun n hn => ?_
  rw [List.mem_range] at hn
  congr 1
  rw [Bool.eq_iff_iff, isPrimeF_iff, primeBy_iff (K := K) _ _ (by omega)]
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact le_rfl
    · exact (mem_primesUpTo.mp hq).2.2.two_le
  · intro m hm hmK
    by_cases h2 : m = 2
    · rw [h2]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_primesUpTo.mpr ⟨hmK, h2, hm⟩)

private theorem nodup_primesUpTo (B : ℕ) : (primesUpTo B).Nodup :=
  (List.nodup_range).filter _

private theorem mem_of_look {β : Type} {q : ℕ} {e : β} :
    ∀ {l : List (ℕ × β)}, look q l = some e → (q, e) ∈ l
  | [], h => by simp [look] at h
  | (a, b) :: l, h => by
    unfold look at h
    cases hab : Nat.beq a q <;> rw [hab] at h
    · exact List.mem_cons_of_mem _ (mem_of_look h)
    · rw [Nat.beq_eq] at hab; subst hab; cases h; simp

private theorem memB_iff {q : ℕ} : ∀ {l : List ℕ}, memB q l = true ↔ q ∈ l
  | [] => by simp [memB]
  | a :: l => by
    simp only [memB, Bool.or_eq_true, Nat.beq_eq, memB_iff, List.mem_cons]
    exact ⟨fun h => h.elim (fun h => Or.inl h.symm) Or.inr,
      fun h => h.elim (fun h => Or.inl h.symm) Or.inr⟩

private theorem memF_iff {q : ℕ} : ∀ {l : List (ℕ × ℕ)}, memF q l = true ↔ ∃ x ∈ l, x.1 = q
  | [] => by simp [memF]
  | a :: l => by
    simp only [memF, Bool.or_eq_true, Nat.beq_eq, memF_iff, List.mem_cons, exists_eq_or_imp]

private theorem cofree_dvd (M : ℕ) : ∀ f m, cofree M f m ∣ m
  | 0, m => dvd_rfl
  | f + 1, m => by
    unfold cofree
    cases Nat.beq (Nat.gcd m M) 1
    · exact (cofree_dvd M f _).trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m M))
    · exact dvd_rfl

private theorem bigF_sound {M m : ℕ} (h : bigF M m = true) :
    ∃ q, q.Prime ∧ q ∣ m ∧ ¬ q ∣ M := by
  simp only [bigF, Bool.and_eq_true, Nat.beq_eq, nbeq_iff] at h
  set r := cofree M 100 m
  have hr : r ∣ m := cofree_dvd M 100 m
  refine ⟨r.minFac, Nat.minFac_prime h.1, (Nat.minFac_dvd r).trans hr, fun hq => ?_⟩
  have := Nat.dvd_gcd (Nat.minFac_dvd r) hq
  rw [h.2] at this
  exact (Nat.minFac_prime h.1).one_lt.ne' (Nat.dvd_one.mp this)

/-! ## Divisor sums of prime powers -/

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

/-! ## Soundness of the certificate checks -/

private theorem candOK_sound {u r : ℕ} : ∀ {K : ℕ}, candOK u r K = true →
    ∀ k, 1 ≤ k → k ≤ K → ¬ (2 * k * r + 1) ∣ u
  | 0, _, k, h1, h2 => by omega
  | K + 1, h, k, h1, h2 => by
    simp only [candOK, Bool.and_eq_true, nbeq_iff] at h
    rcases Nat.eq_or_lt_of_le h2 with rfl | hlt
    · exact fun hd => h.1 (Nat.mod_eq_zero_of_dvd hd)
    · exact candOK_sound h.2 k h1 (by omega)

/-- A killed prime `r` gives a prime factor of `σ (p ^ (r - 1))` above `B`. -/
private theorem killP_sound {B p r S : ℕ} (hp : 2 ≤ p) (hpo : p % 2 = 1) (hr : r.Prime)
    (hr2 : r ≠ 2) (h : killP B p r S = true) :
    ∃ q, q.Prime ∧ B < q ∧ q ∣ gs p (r - 1) := by
  simp only [killP, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, nbeq_iff] at h
  obtain ⟨⟨⟨hS, hu⟩, hur⟩, hc⟩ := h
  set u := gs p (r - 1) / S with hu_def
  have hud : u ∣ gs p (r - 1) := Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero hS)
  have hq := Nat.minFac_prime (show u ≠ 1 by omega)
  refine ⟨u.minFac, hq, ?_, (Nat.minFac_dvd u).trans hud⟩
  have hqr : u.minFac ≠ r := by
    intro he
    exact hur (Nat.mod_eq_zero_of_dvd (he ▸ Nat.minFac_dvd u))
  have h2r := two_mul_dvd_sub_one hp hpo hr hr2 hq ((Nat.minFac_dvd u).trans hud) hqr
  by_contra hle
  push Not at hle
  obtain ⟨k, hk⟩ := h2r
  have hq1 := hq.one_lt
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, mul_zero] at hk; omega
    · exact h0
  have hkK : k ≤ (B - 1) / (2 * r) := by
    rw [Nat.le_div_iff_mul_le (by have := hr.pos; omega)]
    have : 2 * r * k = u.minFac - 1 := hk.symm
    rw [mul_comm k]; omega
  apply candOK_sound hc k hk1 hkK
  have : 2 * k * r + 1 = u.minFac := by
    have : 2 * r * k = u.minFac - 1 := hk.symm
    rw [show 2 * k * r = 2 * r * k by ring]; omega
  rw [this]; exact Nat.minFac_dvd u

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

private theorem primeOK_sound {B p cut : ℕ} {X : List ℕ} (hp : 2 ≤ p) (hpo : p % 2 = 1) :
    ∀ {l : List ℕ} {SP : List (ℕ × ℕ)}, primeOK B p cut X l SP = true →
    ∀ r ∈ l, r.Prime → r ≠ 2 → r ≤ cut → r ∈ X ∨ ∃ q, q.Prime ∧ B < q ∧ q ∣ gs p (r - 1)
  | [], _, _, r, hr, _, _, _ => by simp at hr
  | a :: l, SP, h, r, hr, hrp, hr2, hrc => by
    unfold primeOK at h
    cases hc : (Nat.blt cut a || memB a X)
    · rw [hc] at h
      have hrec : ∀ SP', primeOK B p cut X l SP' = true →
          (r ∈ l → r ∈ X ∨ ∃ q, q.Prime ∧ B < q ∧ q ∣ gs p (r - 1)) := fun SP' h' hl =>
        primeOK_sound hp hpo h' r hl hrp hr2 hrc
      rcases List.mem_cons.mp hr with rfl | hl
      · right
        cases SP with
        | nil =>
          simp only [cond_false, Bool.and_eq_true] at h
          exact killP_sound hp hpo hrp hr2 h.1
        | cons b SP' =>
          simp only at h
          cases hb : Nat.beq b.1 r <;> rw [hb] at h <;> simp only [cond, Bool.and_eq_true] at h
          · exact killP_sound hp hpo hrp hr2 h.1
          · exact killP_sound hp hpo hrp hr2 h.1
      · cases SP with
        | nil =>
          simp only [cond_false, Bool.and_eq_true] at h
          exact hrec _ h.2 hl
        | cons b SP' =>
          simp only at h
          cases hb : Nat.beq b.1 a <;> rw [hb] at h <;> simp only [cond, Bool.and_eq_true] at h
          · exact hrec _ h.2 hl
          · exact hrec _ h.2 hl
    · rw [hc] at h
      simp only [cond] at h
      rcases List.mem_cons.mp hr with rfl | hl
      · simp only [Bool.or_eq_true, Nat.blt_eq, memB_iff] at hc
        rcases hc with hc | hc
        · omega
        · exact Or.inl hc
      · exact primeOK_sound hp hpo h r hl hrp hr2 hrc

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

/-- A row certificate accepted by `rowOK` gives the meaning `RowCover` of its row. -/
theorem rowOK_sound {B XU : ℕ} {L : List ℕ}
    {c : ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)} (hB : B ≤ 2 ^ 21)
    (hL : listOK XU ((B - 3) / 2) L = true)
    (h : rowOK B (2 * (primesUpTo B).prod) XU (primesUpTo B) L c = true) :
    RowCover B c.1 c.2.1 := by
  obtain ⟨p, R, X, SP, EX⟩ := c
  simp only [rowOK, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hpr, hXU⟩, hEX⟩, hLc⟩ := h
  intro hp hp2 f hf1 hf2 hpar hsm
  have hp2' : 2 ≤ p := hp.two_le
  have hpo : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
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
    have hrP : r ∈ primesUpTo B := mem_primesUpTo.mpr ⟨by omega, hr2, hr⟩
    rcases primeOK_sound hp2' hpo hpr r hrP hr hr2 (by omega) with hx | ⟨q, hq, hBq, hqd⟩
    · exact hx
    · exact (hkill r hrd q hq hBq hqd).elim
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

/-! ## Soundness of the search with covering rows -/

variable {N B : ℕ}

private theorem mem_P_of_mem (h : OddPerfect N) (hB : ∀ r ∈ N.primeFactors, r ≤ B) {q : ℕ}
    (hq : q ∈ N.primeFactors) : q ∈ primesUpTo B := by
  have hqp := Nat.prime_of_mem_primeFactors hq
  refine mem_primesUpTo.mpr ⟨hB q hq, ?_, hqp⟩
  rintro rfl
  exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hq)

/-- The exponent of a prime factor lies in its row (from the table when listed there). -/
private theorem mem_cands (h : OddPerfect N) (hB : ∀ r ∈ N.primeFactors, r ≤ B) {nd : List ℕ}
    (hnd : ∀ q ∈ nd, q.Prime ∧ q ≠ 2 ∧ ¬ q ∣ N) {T : List (ℕ × List ℕ)}
    (hT : ∀ x ∈ T, RowCover B x.1 x.2) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) :
    N.factorization p ∈ cands nd p (getRow B (2 * (primesUpTo B).prod) T p) := by
  have hpm : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpN, h.ne_zero⟩
  set f := N.factorization p with hf
  have he1 : 1 ≤ f := (hp.dvd_iff_one_le_factorization h.ne_zero).mp hpN
  have hcap := two_mul_factorization_add_three_le h hpm hB
  have hσ : σ 1 (p ^ f) ∣ 2 * N := OPNStarter.component_sigma_dvd h.perfect hp hf.symm
  rw [sigma_eq_gs hp] at hσ
  have hpar : parityOK p f = true := by
    obtain ⟨q, -, -, hq4, hqe, hev⟩ := exists_special_prime h
    simp only [parityOK, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq]
    by_cases hpq : p = q
    · subst hpq; exact Or.inr ⟨hq4, hqe⟩
    · exact Or.inl (Nat.even_iff.mp (hev p hp hpq))
  have hp2 : p ≠ 2 := by
    rintro rfl; exact h.not_two_dvd hpN
  -- every prime factor of `σ (p ^ f)` is at most `B`
  have hsm : ∀ q, q.Prime → q ∣ gs p f → q ≤ B := by
    intro q hq hqd
    rcases (Nat.Prime.dvd_mul hq).mp (hqd.trans hσ) with h2 | hN
    · have := Nat.le_of_dvd two_pos h2; omega
    · exact hB q (Nat.mem_primeFactors.mpr ⟨hq, hN, h.ne_zero⟩)
  have hrow : f ∈ getRow B (2 * (primesUpTo B).prod) T p := by
    unfold getRow
    cases hl : look p T with
    | some r => exact hT _ (mem_of_look hl) hp hp2 f he1 (by omega) hpar hsm
    | none =>
      simp only [row, List.mem_filter, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
        Nat.ble_eq]
      refine ⟨by omega, ⟨he1, hpar⟩, ?_⟩
      by_contra hb
      obtain ⟨q, hq, hqd, hqM⟩ := bigF_sound (by simpa using hb)
      apply hqM
      rcases (Nat.Prime.dvd_mul hq).mp (hqd.trans hσ) with h2 | hN
      · exact h2.mul_right _
      · exact (List.dvd_prod (mem_P_of_mem h hB
          (Nat.mem_primeFactors.mpr ⟨hq, hN, h.ne_zero⟩))).mul_left 2
  simp only [cands, List.mem_filter, List.all_eq_true, Bool.not_eq_true']
  refine ⟨hrow, ?_⟩
  intro q hq
  rw [Bool.eq_false_iff, Ne, Nat.beq_eq]
  intro h0
  obtain ⟨hqp, hq2, hqN⟩ := hnd q hq
  rw [← sigma_eq_gs hp] at h0
  exact hqN (OPNStarter.force_prime h.perfect hp hf.symm hqp hq2 (Nat.dvd_of_mod_eq_zero h0))

private theorem prod_P_eq_two (h : OddPerfect N) (hB : ∀ r ∈ N.primeFactors, r ≤ B) :
    ∏ q ∈ (primesUpTo B).toFinset, abundancy (q ^ N.factorization q) = 2 := by
  have hab := (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
  rw [abundancy_eq_prod_primeFactors h.ne_zero] at hab
  rw [← hab]
  symm
  refine Finset.prod_subset (fun q hq => List.mem_toFinset.mpr (mem_P_of_mem h hB hq)) ?_
  intro q hq hqN
  have hqp := (mem_primesUpTo.mp (List.mem_toFinset.mp hq)).2.2
  have : ¬ q ∣ N := fun hd => hqN (Nat.mem_primeFactors.mpr ⟨hqp, hd, h.ne_zero⟩)
  rw [Nat.factorization_eq_zero_of_not_dvd this]
  simp [abundancy]

private theorem one_le_abundancy_pow {q : ℕ} (hq : q.Prime) (k : ℕ) : 1 ≤ abundancy (q ^ k) := by
  have := abundancy_le_of_dvd (pow_ne_zero k hq.ne_zero) (one_dvd (q ^ k))
  simpa [abundancy] using this

private theorem cast_prod_ex {ex : List (ℕ × ℕ)} (hex : ∀ x ∈ ex, N.factorization x.1 = x.2)
    (hk : (ex.map Prod.fst).Nodup) (G : ℕ → ℕ → ℕ) :
    (((ex.map fun x => G x.1 x.2).prod : ℕ) : ℚ) =
      ∏ q ∈ (ex.map Prod.fst).toFinset, (G q (N.factorization q) : ℚ) := by
  rw [List.prod_toFinset _ hk, Nat.cast_list_prod, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x hx
  simp [hex x hx]

private theorem cast_prod_map {l : List ℕ} (hl : l.Nodup) (G : ℕ → ℕ) :
    (((l.map G).prod : ℕ) : ℚ) = ∏ q ∈ l.toFinset, (G q : ℚ) := by
  rw [List.prod_toFinset _ hl, Nat.cast_list_prod, List.map_map]
  rfl

private theorem cast_prod {l : List ℕ} (hl : l.Nodup) :
    ((l.prod : ℕ) : ℚ) = ∏ q ∈ l.toFinset, (q : ℚ) := by
  rw [List.prod_toFinset _ hl, Nat.cast_list_prod]

private theorem lowerOK_sound (h : OddPerfect N) (hB : ∀ r ∈ N.primeFactors, r ≤ B)
    {ex : List (ℕ × ℕ)} {dv nd : List ℕ} (hex : ∀ x ∈ ex, N.factorization x.1 = x.2)
    (hI : Inv (primesUpTo B) ex dv nd) (hl : lowerOK ex = true) : False := by
  obtain ⟨hk, -, hexP, -, -⟩ := hI
  set K := (ex.map Prod.fst).toFinset with hK
  have hKP : K ⊆ (primesUpTo B).toFinset := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    exact List.mem_toFinset.mpr (hexP x hx).1
  have hKp : ∀ q ∈ K, q.Prime := fun q hq =>
    (mem_primesUpTo.mp (List.mem_toFinset.mp (hKP hq))).2.2
  have hl' : 2 * (ex.map fun x => x.1 ^ x.2).prod < (ex.map fun x => gs x.1 x.2).prod := by
    unfold lowerOK at hl; rwa [Nat.blt_eq] at hl
  have hl'' : (((2 * (ex.map fun x => x.1 ^ x.2).prod : ℕ)) : ℚ) <
      (((ex.map fun x => gs x.1 x.2).prod : ℕ) : ℚ) := Nat.cast_lt.mpr hl'
  rw [Nat.cast_mul, Nat.cast_ofNat, cast_prod_ex hex hk (fun q e => q ^ e),
    cast_prod_ex hex hk gs] at hl''
  have hpos : (0 : ℚ) < ∏ q ∈ K, ((q ^ N.factorization q : ℕ) : ℚ) :=
    Finset.prod_pos fun q hq => by have := (hKp q hq).pos; positivity
  have hA : ∏ q ∈ K, abundancy (q ^ N.factorization q) =
      (∏ q ∈ K, (gs q (N.factorization q) : ℚ)) /
        ∏ q ∈ K, ((q ^ N.factorization q : ℕ) : ℚ) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun q hq => ?_
    rw [abundancy, sigma_eq_gs (hKp q hq)]
  have h2 : 2 < ∏ q ∈ K, abundancy (q ^ N.factorization q) := by
    rw [hA, lt_div_iff₀ hpos]; exact hl''
  have h3 : ∏ q ∈ K, abundancy (q ^ N.factorization q) ≤
      ∏ q ∈ (primesUpTo B).toFinset, abundancy (q ^ N.factorization q) :=
    Finset.prod_le_prod_of_subset_of_one_le hKP
      (fun q _ => by unfold abundancy; positivity)
      (fun q hq _ => one_le_abundancy_pow
        (mem_primesUpTo.mp (List.mem_toFinset.mp hq)).2.2 _)
  rw [prod_P_eq_two h hB] at h3
  linarith

private theorem upperOK_sound (h : OddPerfect N) (hB : ∀ r ∈ N.primeFactors, r ≤ B)
    {ex : List (ℕ × ℕ)} {dv nd : List ℕ} (hs : Holds N ex dv nd)
    (hI : Inv (primesUpTo B) ex dv nd)
    (hu : upperOK (2 * (primesUpTo B).prod) ((primesUpTo B).map (· - 1)).prod ex nd = true) :
    False := by
  obtain ⟨hex, -, hnd⟩ := hs
  obtain ⟨hk, hn, hexP, hndP, -⟩ := hI
  have hPn := nodup_primesUpTo B
  set P := primesUpTo B with hP
  set Pf := P.toFinset with hPf
  set K := (ex.map Prod.fst).toFinset with hK
  set Nd := nd.toFinset with hNd
  have hKP : K ⊆ Pf := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    exact List.mem_toFinset.mpr (hexP x hx).1
  have hNP : Nd ⊆ Pf := fun q hq => List.mem_toFinset.mpr (hndP q (List.mem_toFinset.mp hq))
  have hdisj : Disjoint K Nd := by
    rw [Finset.disjoint_left]
    intro q hqK hqN
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hqK)
    exact (hexP x hx).2 (List.mem_toFinset.mp hqN)
  have hPp : ∀ q ∈ Pf, q.Prime := fun q hq =>
    (mem_primesUpTo.mp (List.mem_toFinset.mp hq)).2.2
  set R := Pf \ (K ∪ Nd) with hR
  have hsplit : ∀ f : ℕ → ℚ,
      ∏ q ∈ Pf, f q = (∏ q ∈ R, f q) * ((∏ q ∈ K, f q) * ∏ q ∈ Nd, f q) := by
    intro f
    rw [← Finset.prod_union hdisj, Finset.prod_sdiff (Finset.union_subset hKP hNP)]
  have hu1 : 2 * P.prod * (ex.map fun x => gs x.1 x.2 * (x.1 - 1)).prod *
      (nd.map (· - 1)).prod < 4 * (P.map (· - 1)).prod *
      (ex.map fun x => x.1 ^ x.2 * x.1).prod * nd.prod := by
    unfold upperOK at hu; rwa [Nat.blt_eq] at hu
  have hu2 : ((2 * P.prod * (ex.map fun x => gs x.1 x.2 * (x.1 - 1)).prod *
      (nd.map (· - 1)).prod : ℕ) : ℚ) < ((4 * (P.map (· - 1)).prod *
      (ex.map fun x => x.1 ^ x.2 * x.1).prod * nd.prod : ℕ) : ℚ) := Nat.cast_lt.mpr hu1
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hu2
  rw [cast_prod hPn, cast_prod_map hPn, cast_prod hn, cast_prod_map hn,
    cast_prod_ex hex hk (fun q e => gs q e * (q - 1)),
    cast_prod_ex hex hk (fun q e => q ^ e * q)] at hu2
  simp only [Nat.cast_mul, Finset.prod_mul_distrib] at hu2
  rw [hsplit (fun q => (q : ℚ)), hsplit (fun q => ((q - 1 : ℕ) : ℚ))] at hu2
  have hc : ∀ q ∈ Pf, (0 : ℚ) < ((q - 1 : ℕ) : ℚ) := fun q hq => by
    have := (hPp q hq).two_le
    exact_mod_cast (by omega : 0 < q - 1)
  have hq0 : ∀ q ∈ Pf, (0 : ℚ) < (q : ℚ) := fun q hq => by
    exact_mod_cast (hPp q hq).pos
  have hw : ∀ q ∈ Pf, abundancy (q ^ N.factorization q) * ((q - 1 : ℕ) : ℚ) ≤ q := by
    intro q hq
    have hlt := abundancy_prime_pow_lt (hPp q hq) (N.factorization q)
    have h1 : ((q - 1 : ℕ) : ℚ) = (q : ℚ) - 1 := by
      rw [Nat.cast_sub (hPp q hq).one_lt.le]; simp
    have hc' := hc q hq
    rw [h1] at hc' ⊢
    rw [lt_div_iff₀ hc'] at hlt
    exact hlt.le
  have hAll := prod_P_eq_two h hB
  rw [hsplit] at hAll
  have hAn : ∏ q ∈ Nd, abundancy (q ^ N.factorization q) = 1 := by
    refine Finset.prod_eq_one fun q hq => ?_
    rw [Nat.factorization_eq_zero_of_not_dvd (hnd q (List.mem_toFinset.mp hq)).2.2]
    simp [abundancy]
  rw [hAn, mul_one] at hAll
  have hRw : (∏ q ∈ R, abundancy (q ^ N.factorization q)) * ∏ q ∈ R, ((q - 1 : ℕ) : ℚ) ≤
      ∏ q ∈ R, (q : ℚ) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun q hq => ?_) (fun q hq => hw q (Finset.sdiff_subset hq))
    have := hc q (Finset.sdiff_subset hq)
    have : 0 ≤ abundancy (q ^ N.factorization q) := by unfold abundancy; positivity
    positivity
  have hKe : (∏ q ∈ K, abundancy (q ^ N.factorization q)) *
      ∏ q ∈ K, ((q ^ N.factorization q : ℕ) : ℚ) = ∏ q ∈ K, (gs q (N.factorization q) : ℚ) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q hq => ?_
    have hqp := hPp q (hKP hq)
    have : ((q ^ N.factorization q : ℕ) : ℚ) ≠ 0 := by
      have := pow_pos hqp.pos (N.factorization q); positivity
    rw [abundancy, sigma_eq_gs hqp, div_mul_cancel₀ _ this]
  set Ar := ∏ q ∈ R, abundancy (q ^ N.factorization q)
  set Ak := ∏ q ∈ K, abundancy (q ^ N.factorization q)
  set Cr := ∏ q ∈ R, ((q - 1 : ℕ) : ℚ)
  set Ck := ∏ q ∈ K, ((q - 1 : ℕ) : ℚ)
  set Cn := ∏ q ∈ Nd, ((q - 1 : ℕ) : ℚ)
  set Qr := ∏ q ∈ R, (q : ℚ)
  set Qk := ∏ q ∈ K, (q : ℚ)
  set Qn := ∏ q ∈ Nd, (q : ℚ)
  set Ek := ∏ q ∈ K, ((q ^ N.factorization q : ℕ) : ℚ)
  set Gk := ∏ q ∈ K, (gs q (N.factorization q) : ℚ)
  have hX : 0 < Ck * Cn * Qk * Qn := by
    have := Finset.prod_pos fun q hq => hc q (hKP hq)
    have := Finset.prod_pos fun q hq => hc q (hNP hq)
    have := Finset.prod_pos fun q hq => hq0 q (hKP hq)
    have := Finset.prod_pos fun q hq => hq0 q (hNP hq)
    positivity
  have hGk : 0 ≤ Gk := Finset.prod_nonneg fun q _ => by positivity
  have key : Ar * Cr * (Ak * Ek) ≤ Qr * Gk := by
    rw [hKe]; exact mul_le_mul_of_nonneg_right hRw hGk
  have m := mul_le_mul_of_nonneg_right key hX.le
  have e1 : 4 * (Cr * (Ck * Cn)) * (Ek * Qk) * Qn =
      2 * (Ar * Cr * (Ak * Ek) * (Ck * Cn * Qk * Qn)) := by
    linear_combination (-2 * Cr * Ek * (Ck * Cn * Qk * Qn)) * hAll
  have e2 : 2 * (Qr * (Qk * Qn)) * (Gk * Ck) * Cn = 2 * (Qr * Gk * (Ck * Cn * Qk * Qn)) := by ring
  rw [e1, e2] at hu2
  linarith

private theorem two_odd_false (h : OddPerfect N) {ex : List (ℕ × ℕ)}
    (hex : ∀ x ∈ ex, N.factorization x.1 = x.2) {p : ℕ}
    (hpe : ¬ memF p ex = true) (hp : p.Prime)
    (hodd : (Nat.beq (N.factorization p % 2) 1 && ex.any fun x => Nat.beq (x.2 % 2) 1) = true) :
    False := by
  simp only [Bool.and_eq_true, List.any_eq_true, Nat.beq_eq] at hodd
  rw [memF_iff] at hpe
  obtain ⟨hpo, x, hx, hxo⟩ := hodd
  have hxp : x.1 ≠ p := fun he => hpe ⟨x, hx, he⟩
  have hfx := hex x hx
  have hxprime : x.1.Prime := by
    by_contra hnp
    rw [Nat.factorization_eq_zero_of_not_prime N hnp] at hfx
    omega
  obtain ⟨q, -, -, -, -, hev⟩ := exists_special_prime h
  by_cases hpq : p = q
  · subst hpq
    have := Nat.even_iff.mp (hev x.1 hxprime hxp)
    omega
  · have := Nat.even_iff.mp (hev p hp hpq)
    omega

/-- Soundness of the search when the rows of the table cover the admissible exponents. -/
theorem search_sound (h : OddPerfect N) (hB : ∀ r ∈ N.primeFactors, r ≤ B)
    {T : List (ℕ × List ℕ)} (hT : ∀ x ∈ T, RowCover B x.1 x.2) :
    ∀ fuel ex dv nd, search B (primesUpTo B) (2 * (primesUpTo B).prod)
      ((primesUpTo B).map (· - 1)).prod T fuel ex dv nd = true →
      Holds N ex dv nd → Inv (primesUpTo B) ex dv nd → False := by
  intro fuel
  induction fuel with
  | zero => intro ex dv nd hs; simp [search] at hs
  | succ fuel ih =>
    intro ex dv nd hs hH hI
    obtain ⟨hex, hdv, hnd⟩ := hH
    obtain ⟨hk, hn, hexP, hndP, hdvP⟩ := hI
    have hI' : Inv (primesUpTo B) ex dv nd := ⟨hk, hn, hexP, hndP, hdvP⟩
    cases dv with
    | cons p rest =>
      simp only [search, Bool.or_eq_true] at hs
      rcases hs with (hl | hu) | hs
      · exact lowerOK_sound h hB hex hI' hl
      · exact upperOK_sound h hB ⟨hex, hdv, hnd⟩ hI' hu
      split_ifs at hs with hpe
      · exact ih _ _ _ hs ⟨hex, fun q hq => hdv q (List.mem_cons_of_mem _ hq), hnd⟩
          ⟨hk, hn, hexP, hndP, fun q hq => hdvP q (List.mem_cons_of_mem _ hq)⟩
      · obtain ⟨hp, hpN⟩ := hdv p (by simp)
        have hm := mem_cands h hB hnd hT hp hpN
        have hc := List.all_eq_true.mp hs _ hm
        simp only [Bool.or_eq_true] at hc
        rcases hc with hodd | hc
        · exact two_odd_false h hex hpe hp hodd
        refine ih _ _ _ hc ⟨?_, ?_, hnd⟩ ⟨?_, hn, ?_, hndP, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · rfl
          · exact hex x hx
        · intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · obtain ⟨hqP, hq0⟩ := List.mem_filter.mp hq
            obtain ⟨-, hq2, hqp⟩ := mem_primesUpTo.mp hqP
            refine ⟨hqp, OPNStarter.force_prime h.perfect hp rfl hqp hq2 ?_⟩
            rw [sigma_eq_gs hp]
            exact Nat.dvd_of_mod_eq_zero (by simpa using hq0)
          · exact hdv q (List.mem_cons_of_mem _ hq)
        · rw [List.map_cons, List.nodup_cons]
          refine ⟨fun hmem => hpe ?_, hk⟩
          obtain ⟨x, hx, hxp⟩ := List.mem_map.mp hmem
          exact memF_iff.mpr ⟨x, hx, hxp⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨hdvP _ (by simp), fun hmem => (hnd _ hmem).2.2 hpN⟩
          · exact hexP x hx
        · intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · exact (List.mem_filter.mp hq).1
          · exact hdvP q (List.mem_cons_of_mem _ hq)
    | nil =>
      simp only [search, Bool.or_eq_true] at hs
      rcases hs with (hl | hu) | hs
      · exact lowerOK_sound h hB hex hI' hl
      · exact upperOK_sound h hB ⟨hex, hdv, hnd⟩ hI' hu
      split at hs
      · simp at hs
      · rename_i q l hfl
        have hqmem : q ∈ (primesUpTo B).filter
            (fun q => !memF q ex && !memB q nd) := by
          rw [hfl]; simp
        obtain ⟨hqP, hqf⟩ := List.mem_filter.mp hqmem
        simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, Ne, memF_iff,
          memB_iff] at hqf
        obtain ⟨-, hq2, hqp⟩ := mem_primesUpTo.mp hqP
        simp only [Bool.and_eq_true] at hs
        by_cases hqN : q ∣ N
        · exact ih _ _ _ hs.1 ⟨hex, by simpa using ⟨hqp, hqN⟩, hnd⟩
            ⟨hk, hn, hexP, hndP, by simpa using hqP⟩
        · refine ih _ _ _ hs.2 ⟨hex, by simp, fun r hr => ?_⟩
            ⟨hk, List.nodup_cons.mpr ⟨hqf.2, hn⟩, fun x hx => ⟨(hexP x hx).1, ?_⟩, ?_, by simp⟩
          · rcases List.mem_cons.mp hr with rfl | hr
            · exact ⟨hqp, hq2, hqN⟩
            · exact hnd r hr
          · rw [List.mem_cons, not_or]
            exact ⟨fun he => hqf.1 ⟨x, hx, he⟩, (hexP x hx).2⟩
          · intro r hr
            rcases List.mem_cons.mp hr with rfl | hr
            · exact hqP
            · exact hndP r hr

/-- An accepted search with certified rows gives a prime factor above `B`. The list `P` of odd
primes up to `B`, the numbers `M = 2 ∏ P` and `D = ∏ (q - 1)`, the certificates `C`, from
which the table `T` is read off, and the list `L` are given explicitly and checked. -/
theorem exists_primeFactor_gt_of_cert {B : ℕ} {P : List ℕ} {M D XU : ℕ} {L : List ℕ}
    {T : List (ℕ × List ℕ)} {C : List (ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ))}
    (hP : primesUpTo B = P) (hM : 2 * P.prod = M) (hD : (P.map (· - 1)).prod = D)
    (hB : B ≤ 2 ^ 21) (hTC : C.map (fun c => (c.1, c.2.1)) = T)
    (hL : listOK XU ((B - 3) / 2) L = true) (hC : C.all (rowOK B M XU P L) = true)
    (hs : search B P M D T 1000 [] [] [] = true)
    (h : OddPerfect N) : ∃ p ∈ N.primeFactors, B < p := by
  subst hP hM hD hTC
  by_contra hne
  push Not at hne
  refine search_sound h hne (fun x hx => ?_) _ _ _ _ hs ⟨by simp, by simp, by simp⟩
    ⟨by simp, by simp, by simp, by simp, by simp⟩
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  exact rowOK_sound hB hL (List.all_eq_true.mp hC c hc)

end LPF2

end OddPerfect

#print axioms OddPerfect.LPF2.primesUpTo_eq_filter
#print axioms OddPerfect.LPF2.rowOK_sound
#print axioms OddPerfect.LPF2.search_sound
#print axioms OddPerfect.LPF2.exists_primeFactor_gt_of_cert
