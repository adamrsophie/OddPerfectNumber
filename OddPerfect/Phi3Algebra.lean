import OddPerfect.Phi3
import Mathlib.Tactic.NormNum.Prime

/-!
# Algebra of `x ^ 2 + x + 1`

Reusable lemmas on `phi3 x = x ^ 2 + x + 1` (and on `phi5 x = x ^ 4 + x ^ 3 + x ^ 2 + x + 1`)
from the literature on inequalities between `Ω` and `ω` for odd perfect numbers.
-/

namespace OddPerfect

/-- The identity `F(b ^ 2) = F(b) · (b ^ 2 - b + 1)`, where `F = phi3`. Natural subtraction
is harmless here since `b ≤ b ^ 2`. -/
theorem phi3_sq_eq (b : ℕ) : phi3 (b ^ 2) = phi3 b * (b ^ 2 - b + 1) := by
  have hb : b ≤ b ^ 2 := by nlinarith
  zify [hb]
  unfold phi3
  push_cast
  ring

/-- Master lemma behind Clayton and Hansen's "ZelProof1" (arXiv 2303.11974) and
Hansen and Nielsen's Theorem 3.1 (arXiv 2204.08971): if `F(b)` is prime and
`F(x) = m · F(b)` with `1 < m ≤ F(b)`, then `x = b ^ 2` and `m = b ^ 2 - b + 1`. -/
theorem phi3_eq_mul_phi3_prime {x b m : ℕ} (hp : (phi3 b).Prime)
    (h : phi3 x = m * phi3 b) (hm1 : 1 < m) (hmp : m ≤ phi3 b) :
    x = b ^ 2 ∧ m = b ^ 2 - b + 1 := by
  set p := phi3 b with hpdef
  have hxp : x < p := by
    have h1 : x ^ 2 < p ^ 2 := by
      calc x ^ 2 < phi3 x := sq_lt_phi3 x
        _ = m * p := h
        _ ≤ p * p := Nat.mul_le_mul_right _ hmp
        _ = p ^ 2 := by ring
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) h1
  have hbp : b < p := by rw [hpdef]; unfold phi3; nlinarith
  have hdx : p ∣ phi3 x := ⟨m, by rw [h]; ring⟩
  have hdb : p ∣ phi3 b := dvd_refl _
  have hpos : 0 < p := hp.pos
  have hxb : x ≠ b := by
    rintro rfl
    have : 1 * p = m * p := by rw [one_mul, ← h, hpdef]
    have := Nat.eq_of_mul_eq_mul_right hpos this
    omega
  have hsum : x + b + 1 = p := by
    rcases lt_or_gt_of_ne hxb with hlt | hlt
    · exact phi3_roots_sum hp hdx hdb hlt hbp
    · have := phi3_roots_sum hp hdb hdx hlt hxp
      omega
  have hx : x = b ^ 2 := by
    have : x + b + 1 = b ^ 2 + b + 1 := by rw [hsum, hpdef]; rfl
    omega
  refine ⟨hx, ?_⟩
  have h2 : (b ^ 2 - b + 1) * p = m * p := by
    rw [← h, hx, phi3_sq_eq, mul_comm]
  exact (Nat.eq_of_mul_eq_mul_right hpos h2).symm

/-- Reduction of `phi3` modulo any `m`. -/
theorem phi3_mod (z m : ℕ) : phi3 z % m = phi3 (z % m) % m := by
  have h0 : z % m ≡ z [MOD m] := Nat.mod_modEq z m
  have := ((h0.pow 2).add h0).add_right 1
  unfold phi3
  exact this.symm

/-- Two inputs with a common prime divisor of `phi3` are congruent modulo it, or their sum
plus one is divisible by it (the natural number form of `phi3_two_roots`). -/
theorem phi3_common_prime_cases {p x y : ℕ} (hp : p.Prime) (hx : p ∣ phi3 x)
    (hy : p ∣ phi3 y) : x ≡ y [MOD p] ∨ p ∣ x + y + 1 := by
  rcases phi3_two_roots hp hx hy with h | h
  · exact Or.inl ((ZMod.natCast_eq_natCast_iff _ _ _).1 h)
  · exact Or.inr ((ZMod.natCast_eq_zero_iff _ _).1 (by push_cast; exact h))

private theorem mul_mod_six_of_one {p k : ℕ} (hp : p % 6 = 1) : (p * k) % 6 = k % 6 := by
  rw [Nat.mul_mod, hp, one_mul, Nat.mod_mod]

/-- Clayton and Hansen, Lemma "Factorization1" (arXiv 2303.11974): if `c` is prime,
`a ^ 2 + a + 1 = c d`, `b ^ 2 + b + 1 = c e` and `c > d > e`, then `c = a + b + 1` and
`a - b = d - e` (stated additively as `a + e = b + d`). The paper's positivity hypotheses
are not needed. Compared with `phi3_roots_sum`, the size condition `a, b < c` is derived
from `c > d > e`, and the cofactor relation is added. -/
theorem ch_factorization1 {a b c d e : ℕ} (hc : c.Prime) (ha : phi3 a = c * d)
    (hb : phi3 b = c * e) (hcd : d < c) (hde : e < d) :
    c = a + b + 1 ∧ a + e = b + d := by
  have hc0 : 0 < c := hc.pos
  have hac : a < c := by
    have : a ^ 2 < c ^ 2 := by
      calc a ^ 2 < phi3 a := sq_lt_phi3 a
        _ = c * d := ha
        _ < c * c := Nat.mul_lt_mul_of_pos_left hcd hc0
        _ = c ^ 2 := by ring
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  have hba : b < a := by
    apply phi3_strictMono.lt_iff_lt.1
    rw [ha, hb]
    exact Nat.mul_lt_mul_of_pos_left hde hc0
  have hsum := phi3_roots_sum hc ⟨e, hb⟩ ⟨d, ha⟩ hba hac
  refine ⟨by omega, ?_⟩
  have h1 : (c : ℤ) * (a + e) = c * (b + d) := by
    have ha' : ((phi3 a : ℕ) : ℤ) = c * d := by exact_mod_cast ha
    have hb' : ((phi3 b : ℕ) : ℤ) = c * e := by exact_mod_cast hb
    have hs : (c : ℤ) = a + b + 1 := by exact_mod_cast (by omega : c = a + b + 1)
    unfold phi3 at ha' hb'
    push_cast at ha' hb'
    have : (c : ℤ) * (a - b) = c * (d - e) := by
      rw [show (c : ℤ) * (a - b) = (a - b) * (a + b + 1) by rw [hs]; ring]
      linear_combination ha' - hb'
    linear_combination this
  have := mul_left_cancel₀ (by exact_mod_cast hc.ne_zero : (c : ℤ) ≠ 0) h1
  exact_mod_cast this

/-- Clayton and Hansen, Lemma "ZelProof1" (arXiv 2303.11974; compare Ochem and Rao,
Lemma 3): if `c` is prime, `a ^ 2 + a + 1 = c d`, `b ^ 2 + b + 1 = c` and `c > d > 1`, then
`a = b ^ 2`. -/
theorem ch_zelProof1 {a b c d : ℕ} (hc : c.Prime) (ha : phi3 a = c * d) (hb : phi3 b = c)
    (hcd : d < c) (hd : 1 < d) : a = b ^ 2 := by
  subst hb
  exact (phi3_eq_mul_phi3_prime hc (by rw [ha, mul_comm]) hd hcd.le).1

/-- The "in particular" part of Clayton and Hansen's "ZelProof1" (arXiv 2303.11974): under
the same hypotheses `a` is not prime. -/
theorem ch_zelProof1_not_prime {a b c d : ℕ} (hc : c.Prime) (ha : phi3 a = c * d)
    (hb : phi3 b = c) (hcd : d < c) (hd : 1 < d) : ¬ a.Prime := by
  rw [ch_zelProof1 hc ha hb hcd hd]
  exact Nat.Prime.not_prime_pow le_rfl

/-- Clayton and Hansen, Lemma "ZelProof2" (arXiv 2303.11974): for primes
`a, b, c, d, f > 3` with `c > d > f`, it is impossible that `a ^ 2 + a + 1 = c d` and
`b ^ 2 + b + 1 = c f`. So two primes of `S_{2,2}` never share their largest contributed
prime. -/
theorem ch_zelProof2 {a b c d f : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hd : d.Prime) (hf : f.Prime) (ha3 : 3 < a) (hb3 : 3 < b) (hc3 : 3 < c) (hd3 : 3 < d)
    (hf3 : 3 < f) (hcd : d < c) (hdf : f < d) :
    ¬ (phi3 a = c * d ∧ phi3 b = c * f) := by
  rintro ⟨h1, h2⟩
  have hnot : ∀ {x y z : ℕ}, x.Prime → y.Prime → 3 < x → 3 < y → phi3 z = x * y →
      z.Prime → 3 < z → z % 3 = 2 := by
    intro x y z hx hy hx3 hy3 hz hzp hz3
    have h0 : z % 3 ≠ 0 := by
      intro h0
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hzp).1 (Nat.dvd_of_mod_eq_zero h0)
      omega
    have h1 : z % 3 ≠ 1 := by
      intro h1
      have h3 := (three_dvd_phi3_iff z).2 h1
      rw [hz] at h3
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h
      · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hx).1 h; omega
      · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hy).1 h; omega
    omega
  have ha2 := hnot hc hd hc3 hd3 h1 ha ha3
  have hb2 := hnot hc hf hc3 hf3 h2 hb hb3
  obtain ⟨hsum, -⟩ := ch_factorization1 hc h1 h2 hcd hdf
  have hc1 := prime_dvd_phi3_mod_three hc (by omega) ⟨d, h1⟩
  omega

/-- `phi3 a ≥ 3` once `a ≥ 1`. -/
private theorem three_le_phi3 {a : ℕ} (ha : 1 ≤ a) : 3 ≤ phi3 a := by
  unfold phi3; nlinarith

/-- `phi3` is injective. -/
private theorem phi3_injective : Function.Injective phi3 := phi3_strictMono.injective

/-- The family identity behind Hansen and Nielsen, Theorem 3.1 (arXiv 2204.08971):
`F((a + 1) ^ 2) = F(a) F(a + 1)` for every `a`. -/
theorem phi3_succ_sq (a : ℕ) : phi3 ((a + 1) ^ 2) = phi3 a * phi3 (a + 1) := by
  unfold phi3; ring

/-- Hansen and Nielsen, Theorem 3.1 (arXiv 2204.08971), in a sharper elementary form: for
`1 ≤ a ≤ b` with `b ^ 2 + b + 1` prime, `x ^ 2 + x + 1 = (a ^ 2 + a + 1)(b ^ 2 + b + 1)`
holds exactly when `b = a + 1` and `x = (a + 1) ^ 2`. Only the larger factor needs to be
prime (the paper assumes both are), and the proof uses no arithmetic of `ℤ[ζ₆]`. -/
theorem hansen_nielsen_two {x a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hp : (phi3 b).Prime) :
    phi3 x = phi3 a * phi3 b ↔ b = a + 1 ∧ x = (a + 1) ^ 2 := by
  constructor
  · intro h
    obtain ⟨hx, hm⟩ := phi3_eq_mul_phi3_prime hp h
      (by have := three_le_phi3 ha; omega) (phi3_strictMono.monotone hab)
    have hb1 : 1 ≤ b := le_trans ha hab
    have hba : phi3 a = phi3 (b - 1) := by
      rw [hm]; unfold phi3
      obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring_nf; omega
    have := phi3_injective hba
    refine ⟨by omega, ?_⟩
    rw [hx]; congr 1; omega
  · rintro ⟨rfl, rfl⟩
    exact phi3_succ_sq a

/-- No "double threat" (Hansen and Nielsen, arXiv 2204.08971, consequence of Theorem 3.1;
Zelinsky, arXiv 1810.13063, Lemma "Only partial overlap with s1 and s22"): if `x` is prime
then `x ^ 2 + x + 1` is not the product of two primes of the form `a ^ 2 + a + 1`. -/
theorem no_double_threat {x a b : ℕ} (hx : x.Prime) (ha : (phi3 a).Prime)
    (hb : (phi3 b).Prime) : phi3 x ≠ phi3 a * phi3 b := by
  intro h
  have pos : ∀ {y : ℕ}, (phi3 y).Prime → 1 ≤ y := by
    intro y hy
    by_contra h0
    have : y = 0 := by omega
    subst this
    exact Nat.not_prime_one hy
  have key : ∀ {a b : ℕ}, 1 ≤ a → a ≤ b → (phi3 b).Prime → phi3 x = phi3 a * phi3 b →
      False := by
    intro a b ha hab hb h
    obtain ⟨-, hx2⟩ := (hansen_nielsen_two ha hab hb).1 h
    rw [hx2] at hx
    exact Nat.Prime.not_prime_pow le_rfl hx
  rcases le_total a b with hab | hab
  · exact key (pos ha) hab hb h
  · exact key (pos hb) hab ha (by rw [h, mul_comm])

/-- If `b ^ 2 + b + 1` is prime and `x ^ 2 + x + 1 = 3 (b ^ 2 + b + 1)`, then `b = 2` and
`x = 4`. This is Ochem and Rao's Lemma 3 (quoted in Zelinsky, arXiv 1706.07009 and
1810.13063) in the case where the middle value `r = b ^ 2 + b + 1` is prime. -/
theorem phi3_eq_three_mul_phi3_prime {x b : ℕ} (hp : (phi3 b).Prime)
    (h : phi3 x = 3 * phi3 b) : b = 2 ∧ x = 4 := by
  have hb1 : 1 ≤ b := by
    by_contra h0
    have : b = 0 := by omega
    subst this
    exact Nat.not_prime_one hp
  obtain ⟨hx, hm⟩ := phi3_eq_mul_phi3_prime hp h (by norm_num) (three_le_phi3 hb1)
  have hb2 : b = 2 := by
    have h1 : b ^ 2 ≤ b + 2 := by omega
    have hb : b ≤ 2 := by nlinarith
    interval_cases b <;> simp_all
  subst hb2
  exact ⟨rfl, by simpa using hx⟩

/-- Zelinsky, arXiv 1810.13063, Lemma "Get no overlap between s1 and s21": there is no prime
`x` with `x ^ 2 + x + 1 = 3 (a ^ 2 + a + 1)` and `a ^ 2 + a + 1` prime (the hypotheses that
`a` is prime and the primes are odd are not needed). -/
theorem no_phi3_eq_three_mul_phi3 {x a : ℕ} (hx : x.Prime) (ha : (phi3 a).Prime) :
    phi3 x ≠ 3 * phi3 a := by
  intro h
  obtain ⟨-, rfl⟩ := phi3_eq_three_mul_phi3_prime ha h
  exact (by norm_num : ¬ Nat.Prime 4) hx

/-- Yamada, arXiv 2103.16936 (counting form of "a prime `p > 3` divides at most two
`σ(q ^ 2)`"), from `not_three_roots`: for a prime `c`, at most two natural numbers below `c`
have `c ∣ x ^ 2 + x + 1`. -/
theorem card_le_two_of_dvd_phi3 {c : ℕ} (hc : c.Prime) (S : Finset ℕ)
    (hS : ∀ x ∈ S, x < c ∧ c ∣ phi3 x) : S.card ≤ 2 := by
  by_contra h
  push Not at h
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.1 h
  exact not_three_roots hc (hS x hx).2 (hS y hy).2 (hS z hz).2 (hS x hx).1 (hS y hy).1
    (hS z hz).1 hxy hxz hyz

/-- The set of `x < c` with `c ∣ x ^ 2 + x + 1` has at most two elements, for a prime `c`
(Yamada, arXiv 2103.16936). -/
theorem card_filter_range_dvd_phi3_le_two {c : ℕ} (hc : c.Prime) :
    ((Finset.range c).filter (fun x => c ∣ phi3 x)).card ≤ 2 :=
  card_le_two_of_dvd_phi3 hc _ (fun x hx => by
    simp only [Finset.mem_filter, Finset.mem_range] at hx; exact hx)

/-- Without a size restriction: the inputs `x` with `c ∣ x ^ 2 + x + 1`, for a prime `c`, fall
into at most two residue classes modulo `c` (Yamada, arXiv 2103.16936). -/
theorem card_image_zmod_le_two_of_dvd_phi3 {c : ℕ} (hc : c.Prime) (S : Finset ℕ)
    (hS : ∀ x ∈ S, c ∣ phi3 x) : (S.image (fun x : ℕ => (x : ZMod c))).card ≤ 2 := by
  have himg : S.image (fun x : ℕ => (x : ZMod c)) =
      (S.image (· % c)).image (fun x : ℕ => (x : ZMod c)) := by
    rw [Finset.image_image]
    refine Finset.image_congr fun x _ => ?_
    simp [ZMod.natCast_mod]
  rw [himg]
  refine le_trans Finset.card_image_le (card_le_two_of_dvd_phi3 hc _ fun y hy => ?_)
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
  refine ⟨Nat.mod_lt _ hc.pos, ?_⟩
  have := hS x hx
  rw [Nat.dvd_iff_mod_eq_zero] at this ⊢
  rwa [phi3_mod x c] at this

/-- Zelinsky, shared prime lemma (arXiv 1706.07009, Lemma 2; arXiv 1810.13063, Lemma
"smallsharedprimes"), case `a ≡ b ≡ 2 (mod 3)`: if `a ≠ b` are odd, `a ≡ b ≡ 2 (mod 3)`,
and a prime `p` divides both `a ^ 2 + a + 1` and `b ^ 2 + b + 1`, then `5 p ≤ a + b + 1`.
(The paper assumes `a, b` prime; only oddness is used.) -/
theorem zelinsky_shared_prime_two {a b p : ℕ} (hab : a ≠ b) (ha2 : a % 2 = 1)
    (hb2 : b % 2 = 1) (ha3 : a % 3 = 2) (hb3 : b % 3 = 2) (hp : p.Prime)
    (hpa : p ∣ phi3 a) (hpb : p ∣ phi3 b) : 5 * p ≤ a + b + 1 := by
  have hp3 : p ≠ 3 := by
    rintro rfl
    have := (three_dvd_phi3_iff a).1 hpa
    omega
  have hp6 := prime_dvd_phi3_mod_six hp hp3 hpa
  rcases phi3_common_prime_cases hp hpa hpb with h | h
  · rcases lt_or_gt_of_ne hab with hlt | hlt
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hlt.le).1 h
      have hk6 := mul_mod_six_of_one (k := k) hp6
      have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hk; omega)
      have : 6 ≤ k := by omega
      have := Nat.mul_le_mul_left p this
      omega
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hlt.le).1 h.symm
      have hk6 := mul_mod_six_of_one (k := k) hp6
      have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hk; omega)
      have : 6 ≤ k := by omega
      have := Nat.mul_le_mul_left p this
      omega
  · obtain ⟨k, hk⟩ := h
    have hk6 := mul_mod_six_of_one (k := k) hp6
    have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hk; omega)
    have : 5 ≤ k := by omega
    have := Nat.mul_le_mul_left p this
    omega

/-- Zelinsky, shared prime lemma (arXiv 1706.07009, Lemma 2; arXiv 1810.13063), case
`a ≡ b ≡ 1 (mod 3)`: if `a ≠ b` are odd, `a ≡ b ≡ 1 (mod 3)`, and a prime `p` divides both
`a ^ 2 + a + 1` and `b ^ 2 + b + 1`, then `3 p ≤ a + b + 1`. -/
theorem zelinsky_shared_prime_one {a b p : ℕ} (hab : a ≠ b) (ha2 : a % 2 = 1)
    (hb2 : b % 2 = 1) (ha3 : a % 3 = 1) (hb3 : b % 3 = 1) (hp : p.Prime)
    (hpa : p ∣ phi3 a) (hpb : p ∣ phi3 b) : 3 * p ≤ a + b + 1 := by
  by_cases hp3 : p = 3
  · subst hp3; omega
  have hp6 := prime_dvd_phi3_mod_six hp hp3 hpa
  rcases phi3_common_prime_cases hp hpa hpb with h | h
  · rcases lt_or_gt_of_ne hab with hlt | hlt
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hlt.le).1 h
      have hk6 := mul_mod_six_of_one (k := k) hp6
      have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hk; omega)
      have : 6 ≤ k := by omega
      have := Nat.mul_le_mul_left p this
      omega
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hlt.le).1 h.symm
      have hk6 := mul_mod_six_of_one (k := k) hp6
      have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hk; omega)
      have : 6 ≤ k := by omega
      have := Nat.mul_le_mul_left p this
      omega
  · obtain ⟨k, hk⟩ := h
    have hk6 := mul_mod_six_of_one (k := k) hp6
    have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hk; omega)
    have : 3 ≤ k := by omega
    have := Nat.mul_le_mul_left p this
    omega

/-- Zelinsky, arXiv 1810.13063, "Precursor Lemma", first part: if `a ≠ c` are odd, `c` is
prime, `a ^ 2 + a + 1` is prime and divides `c ^ 2 + c + 1`, then
`2 (a ^ 2 + a + 1) < c`. (The paper assumes `a` prime; only oddness is used.) -/
theorem zelinsky_precursor {a c : ℕ} (ha : a % 2 = 1) (hc : c.Prime) (hc2 : c % 2 = 1)
    (hp : (phi3 a).Prime) (hac : a ≠ c) (hd : phi3 a ∣ phi3 c) : 2 * phi3 a < c := by
  set p := phi3 a with hpdef
  have hsq : a ^ 2 % 2 = 1 := by
    rw [Nat.pow_mod, ha]
  have hpa : p = a ^ 2 + a + 1 := rfl
  have hap : a < p := by omega
  rcases phi3_common_prime_cases hp (dvd_refl p) hd with h | h
  · rcases lt_or_gt_of_ne hac with hlt | hlt
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hlt.le).1 h
      rcases k with _ | _ | k
      · omega
      · omega
      · have : p * (k + 1 + 1) = p * k + 2 * p := by ring
        omega
    · have h1 : a % p = a := Nat.mod_eq_of_lt hap
      have h2 : c % p = c := Nat.mod_eq_of_lt (by omega)
      have : a % p = c % p := h
      omega
  · obtain ⟨k, hk⟩ := h
    rcases k with _ | _ | _ | k
    · omega
    · have hc' : c = a ^ 2 := by omega
      rw [hc'] at hc
      exact absurd hc (Nat.Prime.not_prime_pow le_rfl)
    · omega
    · have : p * (k + 1 + 1 + 1) = p * k + 3 * p := by ring
      omega

/-- Zelinsky, arXiv 1810.13063, "Precursor Lemma", second part, with the correction
`a ≠ 3`: if `a ≠ c` are odd primes (`a, c ≠ 2`), `a ≠ 3`, `a ^ 2 + a + 1` is prime and divides
`c ^ 2 + c + 1`, and `3 ∤ c ^ 2 + c + 1`, then `9 (a ^ 2 + a + 1) < 2 c`. The paper omits
`a ≠ 3`, and then the statement is false: `a = 3`, `c = 29`, `29 ^ 2 + 29 + 1 = 13 · 67`. -/
theorem zelinsky_precursor_of_not_three_dvd {a c : ℕ} (ha : a.Prime) (ha2' : a ≠ 2)
    (ha3 : a ≠ 3) (hc : c.Prime) (hc2' : c ≠ 2) (hp : (phi3 a).Prime) (hac : a ≠ c)
    (hd : phi3 a ∣ phi3 c) (h3 : ¬ 3 ∣ phi3 c) : 9 * phi3 a < 2 * c := by
  set p := phi3 a with hpdef
  have hpa : p = a ^ 2 + a + 1 := rfl
  have ha2 : 2 ≤ a := ha.two_le
  have hc31 : c % 3 ≠ 1 := fun h => h3 ((three_dvd_phi3_iff c).2 h)
  have ha31 : a % 3 ≠ 1 := fun h => h3 (((three_dvd_phi3_iff a).2 h).trans hd)
  have ha30 : a % 3 ≠ 0 := by
    intro h0
    exact ha3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three ha).1
      (Nat.dvd_of_mod_eq_zero h0)).symm
  have hc30 : c % 3 ≠ 0 := by
    intro h0
    have hc3 : c = 3 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hc).1 (Nat.dvd_of_mod_eq_zero h0)).symm
    subst hc3
    have h13 : p = 13 :=
      (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (by simpa [phi3] using hd)
    have : a ≤ 3 := by nlinarith
    interval_cases a <;> simp_all [phi3]
  have ha22 : a % 2 = 1 := (ha.eq_two_or_odd).resolve_left ha2'
  have hc22 : c % 2 = 1 := (hc.eq_two_or_odd).resolve_left hc2'
  have hp3 : p ≠ 3 := by
    intro h; rw [hpa] at h; nlinarith
  have hp6 := prime_dvd_phi3_mod_six hp hp3 (dvd_refl p)
  have hbig : 2 * a + 2 < p := by nlinarith
  have hap : a < p := by omega
  rcases phi3_common_prime_cases hp (dvd_refl p) hd with h | h
  · rcases lt_or_gt_of_ne hac with hlt | hlt
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hlt.le).1 h
      have hk6 := mul_mod_six_of_one (k := k) hp6
      have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hk; omega)
      have : 6 ≤ k := by omega
      have := Nat.mul_le_mul_left p this
      omega
    · have h1 : a % p = a := Nat.mod_eq_of_lt hap
      have h2 : c % p = c := Nat.mod_eq_of_lt (by omega)
      have : a % p = c % p := h
      omega
  · obtain ⟨k, hk⟩ := h
    have hk6 := mul_mod_six_of_one (k := k) hp6
    have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hk; omega)
    have : 5 ≤ k := by omega
    have := Nat.mul_le_mul_left p this
    omega

/-- Zelinsky, arXiv 1810.13063, Lemma "Other new lemma for repairing 3 divides N case":
there are no odd primes `a, b, c` with `a ^ 2 + a + 1`, `b ^ 2 + b + 1` prime and
`c ^ 2 + c + 1 = 3 (a ^ 2 + a + 1)(b ^ 2 + b + 1)`. (Only oddness of `a, b` is used.) -/
theorem no_phi3_eq_three_mul_phi3_mul_phi3 {a b c : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1)
    (hc : c.Prime) (hc2 : c % 2 = 1) (hpa : (phi3 a).Prime) (hpb : (phi3 b).Prime) :
    phi3 c ≠ 3 * phi3 a * phi3 b := by
  intro h
  have hA := hpa.two_le
  have hB := hpb.two_le
  have hne : ∀ {y z : ℕ}, 2 ≤ phi3 z → phi3 c = phi3 y * (3 * phi3 z) → y ≠ c := by
    rintro y z hz hyz rfl
    have : phi3 y * 1 < phi3 y * (3 * phi3 z) :=
      Nat.mul_lt_mul_of_pos_left (by omega) (by unfold phi3; omega)
    omega
  have h1 := zelinsky_precursor ha hc hc2 hpa (hne hB (by rw [h]; ring))
    ⟨3 * phi3 b, by rw [h]; ring⟩
  have h2 := zelinsky_precursor hb hc hc2 hpb (hne hA (by rw [h]; ring))
    ⟨3 * phi3 a, by rw [h]; ring⟩
  have h3 := sq_lt_phi3 c
  have : 4 * (phi3 a * phi3 b) < c * c := by nlinarith
  nlinarith

/-- Zelinsky, arXiv 1810.13063, Lemma "x2+x+1 not a cube of a prime": if `x` is prime then
`x ^ 2 + x + 1` is not a perfect cube. (Primality matters: `18 ^ 2 + 18 + 1 = 7 ^ 3`.) An earlier
source for the statement is A. Brauer, Bull. Amer. Math. Soc. 49 (1943), 712 to 718, Lemma 1,
which treats every exponent above 1 and relies on a theorem of Nagell. -/
theorem phi3_ne_cube_of_prime {x : ℕ} (hx : x.Prime) (k : ℕ) : phi3 x ≠ k ^ 3 := by
  intro h
  have hx2 := hx.two_le
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; unfold phi3 at h; simp at h
    · exact h0
  have hfac : x * (x + 1) = (k - 1) * phi3 k := by
    have e1 : x * (x + 1) + 1 = k ^ 3 := by rw [← h]; unfold phi3; ring
    have e2 : (k - 1) * phi3 k + 1 = k ^ 3 := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; unfold phi3; ring
    omega
  have hdvd : x ∣ (k - 1) * phi3 k := ⟨x + 1, hfac.symm⟩
  rcases (Nat.Prime.dvd_mul hx).1 hdvd with h1 | h1
  · have hk0 : k - 1 ≠ 0 := by
      intro h0
      have : k = 1 := by omega
      subst this; unfold phi3 at h; nlinarith
    have hle : x ≤ k - 1 := Nat.le_of_dvd (by omega) h1
    have : x + 1 ≤ k := by omega
    have : (x + 1) ^ 3 ≤ k ^ 3 := Nat.pow_le_pow_left this 3
    unfold phi3 at h
    nlinarith
  · by_cases hx3 : x = 3
    · subst hx3
      have hk : k ≤ 2 := by
        by_contra hk
        have : 3 ^ 3 ≤ k ^ 3 := Nat.pow_le_pow_left (by omega) 3
        unfold phi3 at h; omega
      interval_cases k <;> simp [phi3] at h
    · have hmod := prime_dvd_phi3_mod_three hx hx3 h1
      have h3 : 3 ∣ k ^ 3 := h ▸ (three_dvd_phi3_iff x).2 hmod
      have h3k : 3 ∣ k := Nat.prime_three.dvd_of_dvd_pow h3
      have h27 : 9 ∣ k ^ 3 := by
        obtain ⟨j, rfl⟩ := h3k
        exact ⟨3 * j ^ 3, by ring⟩
      exact not_nine_dvd_phi3 x (h ▸ h27)

/-- Zelinsky, arXiv 1810.13063, Lemma "No triple threat arising from T": there are no
integers `a, b, c, d`, all `≡ 1 (mod 5)`, with
`a ^ 2 + a + 1 = (b ^ 2 + b + 1)(c ^ 2 + c + 1)(d ^ 2 + d + 1)` (the left side is `3` and the
right side `27 ≡ 2` modulo `5`). -/
theorem no_phi3_eq_triple_mod_five {a b c d : ℕ} (ha : a % 5 = 1) (hb : b % 5 = 1)
    (hc : c % 5 = 1) (hd : d % 5 = 1) : phi3 a ≠ phi3 b * phi3 c * phi3 d := by
  intro h
  have e : ∀ z : ℕ, z % 5 = 1 → phi3 z % 5 = 3 := by
    intro z hz; rw [phi3_mod, hz]; rfl
  have := congrArg (· % 5) h
  rw [e a ha, Nat.mul_mod, Nat.mul_mod (phi3 b), e b hb, e c hc, e d hd] at this
  norm_num at this

/-- The family of three factor solutions in Hansen and Nielsen, Theorem 4.1
(arXiv 2204.08971): if `c (a + b + 1) = a b` and `x = c (a b + a + b) + a + b`, then
`x ^ 2 + x + 1 = (a ^ 2 + a + 1)(b ^ 2 + b + 1)(c ^ 2 + c + 1)`. -/
theorem hansen_nielsen_three_family {a b c x : ℕ} (hc : c * (a + b + 1) = a * b)
    (hx : x = c * (a * b + a + b) + a + b) : phi3 x = phi3 a * phi3 b * phi3 c := by
  subst hx
  unfold phi3
  have h : (c : ℤ) * (a + b + 1) = a * b := by exact_mod_cast hc
  have key : ∀ t s xp : ℤ, s = t + 1 → xp = c * (c * s + t) + t →
      xp ^ 2 + xp + 1 = (c ^ 2 * s ^ 2 + c * s * t - c * s + t ^ 2 + t + 1) *
        (c ^ 2 + c + 1) := by
    intro t s xp hs hxp; subst hs hxp; ring
  have k := key (a + b) (a + b + 1) (c * (c * (a + b + 1) + (a + b)) + (a + b)) rfl rfl
  zify
  linear_combination k + (-(c * ((c * (a * b + a + b) + a + b : ℤ) +
    (c * (c * (a + b + 1) + (a + b)) + (a + b)) + 1)) +
    (a * b + c * (a + b + 1) + (a + b) - 1) * (c ^ 2 + c + 1)) * h

/-- Sporadic three factor solutions in Hansen and Nielsen, Theorem 4.1 (arXiv 2204.08971):
`F(18) = F(2) ^ 3`, `F(25) = F(1) F(2) F(5)`, `F(22) = F(1) F(3) ^ 2`. -/
theorem hansen_nielsen_three_sporadic :
    phi3 18 = phi3 2 * phi3 2 * phi3 2 ∧ phi3 25 = phi3 1 * phi3 2 * phi3 5 ∧
      phi3 22 = phi3 1 * phi3 3 * phi3 3 := by
  norm_num [phi3]

/-- The quadruple threat of Hansen and Nielsen (arXiv 2204.08971, Section 5):
`191 ^ 2 + 191 + 1 = F(2) F(3) F(3) F(5) = 7 · 13 · 13 · 31`, with `191` and the four factors
prime. -/
theorem quadruple_threat_191 :
    phi3 191 = phi3 2 * phi3 3 * phi3 3 * phi3 5 ∧ Nat.Prime 191 ∧ (phi3 2).Prime ∧
      (phi3 3).Prime ∧ (phi3 5).Prime := by
  refine ⟨by norm_num [phi3], by norm_num, by norm_num [phi3], by norm_num [phi3],
    by norm_num [phi3]⟩

/-- The value `x ^ 4 + x ^ 3 + x ^ 2 + x + 1 = σ(x ^ 4)` for prime `x`. -/
def phi5 (x : ℕ) : ℕ := x ^ 4 + x ^ 3 + x ^ 2 + x + 1

/-- Reduction of `phi5` modulo any `m`. -/
theorem phi5_mod (z m : ℕ) : phi5 z % m = phi5 (z % m) % m := by
  have h0 : z % m ≡ z [MOD m] := Nat.mod_modEq z m
  have := ((((h0.pow 4).add (h0.pow 3)).add (h0.pow 2)).add h0).add_right 1
  unfold phi5
  exact this.symm

/-- Block identity for `Φ₃` (Zelinsky, arXiv 1810.13063): `F(z) - 3 = (z - 1)(z + 2)`,
over `ℤ`. -/
theorem phi3_sub_three (z : ℕ) : (phi3 z : ℤ) - 3 = ((z : ℤ) - 1) * (z + 2) := by
  unfold phi3; push_cast; ring

/-- Block identity for `Φ₅` (Zelinsky, arXiv 1810.13063):
`Φ₅(z) - 5 = (z - 1)(z ^ 3 + 2 z ^ 2 + 3 z + 4)`, over `ℤ`. -/
theorem phi5_sub_five (z : ℕ) :
    (phi5 z : ℤ) - 5 = ((z : ℤ) - 1) * (z ^ 3 + 2 * z ^ 2 + 3 * z + 4) := by
  unfold phi5; push_cast; ring

/-- `5 ∣ Φ₅(z)` exactly when `z ≡ 1 (mod 5)`, for every natural `z`. -/
theorem five_dvd_phi5_iff (z : ℕ) : 5 ∣ phi5 z ↔ z % 5 = 1 := by
  rw [Nat.dvd_iff_mod_eq_zero, phi5_mod]
  have h := Nat.mod_lt z (show 5 > 0 by norm_num)
  interval_cases z % 5 <;> simp [phi5]

/-- For `z ≡ 1 (mod 5)`, `Φ₅(z) ≡ 5 (mod 25)` (from the block identity: `5 ∣ z - 1` and
`5 ∣ z ^ 3 + 2 z ^ 2 + 3 z + 4`). -/
theorem phi5_mod_twentyfive {z : ℕ} (hz : z % 5 = 1) : phi5 z % 25 = 5 := by
  rw [phi5_mod]
  have h := Nat.mod_lt z (show 25 > 0 by norm_num)
  have h5 : z % 25 % 5 = 1 := by rw [Nat.mod_mod_of_dvd _ (by norm_num)]; exact hz
  interval_cases hr : z % 25 <;> simp_all [phi5]

/-- `25` never divides `Φ₅(z)`. -/
theorem not_twentyfive_dvd_phi5 (z : ℕ) : ¬ 25 ∣ phi5 z := by
  rw [Nat.dvd_iff_mod_eq_zero, phi5_mod]
  have h := Nat.mod_lt z (show 25 > 0 by norm_num)
  interval_cases z % 25 <;> simp [phi5]

/-- The exact power of `5` in `Φ₅(z)` for every natural `z`: it is `1` if `z ≡ 1 (mod 5)`
and `0` otherwise. -/
theorem padicValNat_five_phi5 (z : ℕ) :
    padicValNat 5 (phi5 z) = if z % 5 = 1 then 1 else 0 := by
  have hpos : phi5 z ≠ 0 := by unfold phi5; omega
  have := Fact.mk (show Nat.Prime 5 by norm_num)
  split_ifs with h
  · have h5 : 5 ∣ phi5 z := (five_dvd_phi5_iff z).2 h
    have hle : padicValNat 5 (phi5 z) ≤ 1 := by
      by_contra hc
      have : 5 ^ 2 ∣ phi5 z :=
        (pow_dvd_pow 5 (show 2 ≤ padicValNat 5 (phi5 z) by omega)).trans
          (by rw [Nat.padicValNat_def]; exact pow_multiplicity_dvd _ _)
      exact not_twentyfive_dvd_phi5 z (by simpa using this)
    have : 1 ≤ padicValNat 5 (phi5 z) := by
      rw [Nat.padicValNat_def]; exact one_le_padicValNat_of_dvd hpos h5
    omega
  · rw [Nat.padicValNat_def]
    exact padicValNat.eq_zero_of_not_dvd (fun h5 => h ((five_dvd_phi5_iff z).1 h5))

/-- Zelinsky's "miraculous factorization" (arXiv 1810.13063):
`Φ₃(Φ₅(x)) = (x ^ 2 - x + 1)(x ^ 6 + 3 x ^ 5 + 5 x ^ 4 + 6 x ^ 3 + 7 x ^ 2 + 6 x + 3)`.
Natural subtraction is harmless since `x ≤ x ^ 2`. -/
theorem phi3_phi5 (x : ℕ) :
    phi3 (phi5 x) =
      (x ^ 2 - x + 1) * (x ^ 6 + 3 * x ^ 5 + 5 * x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + 6 * x + 3) := by
  have hx : x ≤ x ^ 2 := by nlinarith
  zify [hx]
  unfold phi3 phi5
  push_cast
  ring

/-- Zelinsky, arXiv 1810.13063, Lemma "Relative primeness of two parts of T to S1": the gcd
of the two factors in `phi3_phi5` divides `31`, via the explicit combination
`(5x⁵ + 21x⁴ + 44x³ + 58x² + 55x + 34) A - (5x + 1) B = 31`. -/
theorem gcd_phi3_phi5_factors_dvd (x : ℕ) :
    Nat.gcd (x ^ 2 - x + 1) (x ^ 6 + 3 * x ^ 5 + 5 * x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + 6 * x + 3)
      ∣ 31 := by
  have hx : x ≤ x ^ 2 := by nlinarith
  set g := Nat.gcd (x ^ 2 - x + 1)
    (x ^ 6 + 3 * x ^ 5 + 5 * x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + 6 * x + 3)
  have hA : (g : ℤ) ∣ ((x ^ 2 - x + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _)
  have hB : (g : ℤ) ∣ ((x ^ 6 + 3 * x ^ 5 + 5 * x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + 6 * x + 3 : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _)
  push_cast [Nat.cast_sub hx] at hA hB
  have h31 : (g : ℤ) ∣ 31 := by
    have := Dvd.dvd.sub (dvd_mul_of_dvd_right hA
      ((5 * x ^ 5 + 21 * x ^ 4 + 44 * x ^ 3 + 58 * x ^ 2 + 55 * x + 34 : ℤ)))
      (dvd_mul_of_dvd_right hB ((5 * x + 1 : ℤ)))
    have e : ((5 * x ^ 5 + 21 * x ^ 4 + 44 * x ^ 3 + 58 * x ^ 2 + 55 * x + 34 : ℤ)) *
        ((x : ℤ) ^ 2 - x + 1) - (5 * x + 1) *
        ((x : ℤ) ^ 6 + 3 * x ^ 5 + 5 * x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + 6 * x + 3) = 31 := by
      ring
    rw [← e]
    exact Dvd.dvd.sub (dvd_mul_of_dvd_right hA _) (dvd_mul_of_dvd_right hB _)
  exact_mod_cast h31

/-- The only possible common prime divisor of the two factors in `phi3_phi5` is `31`
(Zelinsky, arXiv 1810.13063). -/
theorem prime_dvd_phi3_phi5_factors {x q : ℕ} (hq : q.Prime) (hA : q ∣ x ^ 2 - x + 1)
    (hB : q ∣ x ^ 6 + 3 * x ^ 5 + 5 * x ^ 4 + 6 * x ^ 3 + 7 * x ^ 2 + 6 * x + 3) : q = 31 :=
  (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1
    ((Nat.dvd_gcd hA hB).trans (gcd_phi3_phi5_factors_dvd x))

/-- Clayton and Hansen, Lemma "Factorization3" (arXiv 2303.11974): if `d` is prime,
`a ^ 2 + a + 1 = 3 d e`, `b ^ 2 + b + 1 = 3 d f` and `d ≥ e > f`, then `3 d = a + b + 1` and
`a - b = e - f` (stated as `a + f = b + e`). The paper also assumes `a, b` prime; this is
not needed. -/
theorem ch_factorization3 {a b d e f : ℕ} (hd : d.Prime) (hA : phi3 a = 3 * d * e)
    (hB : phi3 b = 3 * d * f) (hde : e ≤ d) (hef : f < e) :
    3 * d = a + b + 1 ∧ a + f = b + e := by
  have hd0 : 0 < d := hd.pos
  have hd3 : d ≠ 3 := by
    rintro rfl
    exact not_nine_dvd_phi3 a ⟨e, by rw [hA]⟩
  have ha3 : a % 3 = 1 := (three_dvd_phi3_iff a).1 ⟨d * e, by rw [hA]; ring⟩
  have hb3 : b % 3 = 1 := (three_dvd_phi3_iff b).1 ⟨d * f, by rw [hB]; ring⟩
  have hba : b < a := by
    apply phi3_strictMono.lt_iff_lt.1
    rw [hA, hB]
    exact Nat.mul_lt_mul_of_pos_left hef (by omega)
  have h3d : a < 3 * d := by
    have : a ^ 2 < (3 * d) ^ 2 := by
      have := sq_lt_phi3 a
      have : 3 * d * e ≤ 3 * d * d := Nat.mul_le_mul_left _ hde
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  have three_dvd : ∀ {k : ℕ}, 3 ∣ d * k → 3 ∣ k := by
    intro k h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hd).1 h).symm hd3
    · exact h
  have hsum : 3 * d = a + b + 1 := by
    rcases phi3_common_prime_cases hd ⟨3 * e, by rw [hA]; ring⟩
        ⟨3 * f, by rw [hB]; ring⟩ with h | h
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hba.le).1 h.symm
      have h3k : 3 ∣ k := three_dvd ⟨(a - b) / 3, by rw [← hk]; omega⟩
      have : 3 ≤ k := by
        obtain ⟨j, rfl⟩ := h3k
        rcases j with _ | j
        · omega
        · omega
      have := Nat.mul_le_mul_left d this
      omega
    · obtain ⟨k, hk⟩ := h
      have h3k : 3 ∣ k := three_dvd ⟨(a + b + 1) / 3, by rw [← hk]; omega⟩
      obtain ⟨j, rfl⟩ := h3k
      rcases j with _ | _ | j
      · omega
      · rw [hk]; ring
      · have : d * (3 * (j + 1 + 1)) = d * 6 + d * (3 * j) := by ring
        omega
  refine ⟨hsum, ?_⟩
  have hA' : ((phi3 a : ℕ) : ℤ) = 3 * d * e := by exact_mod_cast hA
  have hB' : ((phi3 b : ℕ) : ℤ) = 3 * d * f := by exact_mod_cast hB
  have hs : (3 * d : ℤ) = a + b + 1 := by exact_mod_cast hsum
  unfold phi3 at hA' hB'
  push_cast at hA' hB'
  have h1 : (3 * d : ℤ) * (a + f) = 3 * d * (b + e) := by
    have : (3 * d : ℤ) * (a - b) = (a - b) * (a + b + 1) := by rw [hs]; ring
    linear_combination this + hA' - hB'
  have := mul_left_cancel₀ (by positivity : (3 * d : ℤ) ≠ 0) h1
  exact_mod_cast this

/-- Clayton and Hansen, Lemma "Factorization2" (arXiv 2303.11974): if `a, b, d` are prime,
`a ^ 2 + a + 1 = 3 d e`, `b ^ 2 + b + 1 = d f` and `d ≥ e > f`, then `d = a + b + 1` and
`a - b = 3 e - f` (stated as `a + f = b + 3 e`). The paper assumes `d > e`; `d ≥ e`
suffices. The paper's mod `3` step tacitly assumes `b ≡ 2 (mod 3)`; the cases `b = 3` and
`b ≡ 1 (mod 3)` are handled here separately (the latter by a size argument). -/
theorem ch_factorization2 {a b d e f : ℕ} (ha : a.Prime) (hb : b.Prime) (hd : d.Prime)
    (hA : phi3 a = 3 * d * e) (hB : phi3 b = d * f) (hde : e ≤ d) (hef : f < e) :
    d = a + b + 1 ∧ a + f = b + 3 * e := by
  have hd0 : 0 < d := hd.pos
  have hb2 := hb.two_le
  have ha3 : a % 3 = 1 := (three_dvd_phi3_iff a).1 ⟨d * e, by rw [hA]; ring⟩
  have ha2 : a % 2 = 1 := by
    rcases ha.eq_two_or_odd with h | h
    · subst h; omega
    · exact h
  have hFb : 7 ≤ phi3 b := by unfold phi3; nlinarith
  have hd3 : d ≠ 3 := by
    rintro rfl
    have : f ≤ 2 := by omega
    have : 3 * f ≤ 6 := by omega
    omega
  have hba : b < a := by
    apply phi3_strictMono.lt_iff_lt.1
    rw [hA, hB]
    have := Nat.mul_lt_mul_of_pos_left (show f < 3 * e by omega) hd0
    linarith
  have h2d : a < 2 * d := by
    have : a ^ 2 < (2 * d) ^ 2 := by
      have := sq_lt_phi3 a
      have : 3 * d * e ≤ 3 * d * d := Nat.mul_le_mul_left _ hde
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  have hdA : d ∣ phi3 a := ⟨3 * e, by rw [hA]; ring⟩
  have hd1 := prime_dvd_phi3_mod_three hd hd3 hdA
  have hsum : d = a + b + 1 := by
    rcases phi3_common_prime_cases hd hdA ⟨f, hB⟩ with h | h
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hba.le).1 h.symm
      rcases k with _ | _ | k
      · omega
      · have hb3 : b % 3 = 0 := by omega
        have hb3' : b = 3 :=
          ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hb).1 (Nat.dvd_of_mod_eq_zero hb3)).symm
        subst hb3'
        have : d = 13 := ((Nat.prime_dvd_prime_iff_eq hd (by norm_num)).1
          ⟨f, by simpa [phi3] using hB⟩)
        omega
      · have : d * (k + 1 + 1) = d * k + 2 * d := by ring
        omega
    · obtain ⟨k, hk⟩ := h
      rcases k with _ | _ | _ | _ | k
      · omega
      · omega
      · rcases hb.eq_two_or_odd with h2 | h2
        · subst h2
          have : d = 7 := ((Nat.prime_dvd_prime_iff_eq hd (by norm_num)).1
            ⟨f, by simpa [phi3] using hB⟩)
          omega
        · omega
      · exfalso
        have hs : 3 * d = a + b + 1 := by rw [hk]; ring
        have h1 : d * f + d ≤ d * e := by
          have := Nat.mul_le_mul_left d (show f + 1 ≤ e by omega)
          linarith
        have h2 : 3 * d * e ≤ 3 * d * d := Nat.mul_le_mul_left _ hde
        unfold phi3 at hA hB
        nlinarith
      · have : d * (k + 1 + 1 + 1 + 1) = d * k + 4 * d := by ring
        omega
  refine ⟨hsum, ?_⟩
  have hA' : ((phi3 a : ℕ) : ℤ) = 3 * d * e := by exact_mod_cast hA
  have hB' : ((phi3 b : ℕ) : ℤ) = d * f := by exact_mod_cast hB
  have hs : (d : ℤ) = a + b + 1 := by exact_mod_cast hsum
  unfold phi3 at hA' hB'
  push_cast at hA' hB'
  have h1 : (d : ℤ) * (a + f) = d * (b + 3 * e) := by
    have : (d : ℤ) * (a - b) = (a - b) * (a + b + 1) := by rw [hs]; ring
    linear_combination this + hA' - hB'
  have := mul_left_cancel₀ (by exact_mod_cast hd.ne_zero : (d : ℤ) ≠ 0) h1
  exact_mod_cast this

/-- Clayton and Hansen, Lemma "Unique between S1 and S31" (arXiv 2303.11974): there are no
primes `a, b, d` and `e > 1` with `a ^ 2 + a + 1 = 3 d e`, `b ^ 2 + b + 1 = d` and
`d ≥ e`. -/
theorem ch_unique_S1_S31 {a b d e : ℕ} (ha : a.Prime) (hb : b.Prime) (hd : d.Prime)
    (he : 1 < e) (hA : phi3 a = 3 * d * e) (hB : phi3 b = d) (hde : e ≤ d) : False := by
  obtain ⟨hs, -⟩ := ch_factorization2 ha hb hd hA (by rw [hB, mul_one]) hde he
  have : a = b ^ 2 := by
    have := hB.trans hs
    unfold phi3 at this
    omega
  rw [this] at ha
  exact Nat.Prime.not_prime_pow le_rfl ha

/-- Clayton and Hansen, Lemma "Unique between S21 and S31" (arXiv 2303.11974): there are no
primes `a, d` and `e > 1`, and no `b`, with `a ^ 2 + a + 1 = 3 d e`, `b ^ 2 + b + 1 = 3 d` and
`d ≥ e`. (The paper writes `d = a + b + 1` where `3 d = a + b + 1` is meant.) -/
theorem ch_unique_S21_S31 {a b d e : ℕ} (ha : a.Prime) (hd : d.Prime) (he : 1 < e)
    (hA : phi3 a = 3 * d * e) (hB : phi3 b = 3 * d) (hde : e ≤ d) : False := by
  obtain ⟨hs, hd'⟩ := ch_factorization3 hd hA (by rw [hB, mul_one]) hde he
  have hab : a = b ^ 2 := by
    have h1 : ((a : ℤ) + 1) = b + e := by exact_mod_cast hd'
    have h2 : (3 * d : ℤ) = a + b + 1 := by exact_mod_cast hs
    have hA' : ((phi3 a : ℕ) : ℤ) = 3 * d * e := by exact_mod_cast hA
    unfold phi3 at hA'
    push_cast at hA'
    have : (a : ℤ) = b ^ 2 := by
      have he' : (e : ℤ) = a + 1 - b := by linarith
      rw [he', h2] at hA'
      linarith [hA']
    exact_mod_cast this
  rw [hab] at ha
  exact Nat.Prime.not_prime_pow le_rfl ha

/-- Clayton and Hansen, Lemma "Semi-linked in S31" (arXiv 2303.11974): for a prime `d`
there are no `a, b, c` and `d ≥ e > f > g` with `a ^ 2 + a + 1 = 3 d e`,
`b ^ 2 + b + 1 = 3 d f` and `c ^ 2 + c + 1 = 3 d g`. (The paper's other primality and
distinctness hypotheses are not needed.) -/
theorem ch_semilinked_S31 {a b c d e f g : ℕ} (hd : d.Prime) (hA : phi3 a = 3 * d * e)
    (hB : phi3 b = 3 * d * f) (hC : phi3 c = 3 * d * g) (hde : e ≤ d) (hef : f < e)
    (hfg : g < f) : False := by
  obtain ⟨h1, -⟩ := ch_factorization3 hd hA hB hde hef
  obtain ⟨h2, -⟩ := ch_factorization3 hd hA hC hde (hfg.trans hef)
  have hbc : b = c := by omega
  subst hbc
  have : 3 * d * f = 3 * d * g := hB.symm.trans hC
  have := Nat.eq_of_mul_eq_mul_left (by have := hd.pos; omega) this
  omega

/-- Yamada's first gap principle (arXiv 1706.09341, Lemma 4.1), prime modulus case, for any
odd `l`: let `q` be prime, let `x₁, x₂` satisfy `x₁ ^ l ≡ x₂ ^ l ≡ 1 (mod q)`, let `x₁` and
`x₂` be multiplicatively independent (`x₁ ^ i = x₂ ^ j` only for `i = j = 0`), and let
`x₁ ^ ((l - 1) / 2) < q`. Then `x₂ > x₁ ^ ⌊(l + 1) / 6⌋`. In the paper `q` is the common
large prime of `Φ_l(x₁) = p ^ {m₁} q` and `Φ_l(x₂) = p ^ {m₂} q` with `p ^ {m₁} < q`, which
gives the size hypothesis. For `l = 3` the conclusion is only `x₂ > 1`; for `l = 5` it is
`x₂ > x₁`. The proof counts the `l + 1` or more distinct residues `x₁ ^ i x₂ ^ j < q` that are
`l`-th roots of unity modulo `q`. -/
theorem yamada_gap {l q x₁ x₂ : ℕ} (hl : Odd l) (hq : q.Prime)
    (h1 : (x₁ : ZMod q) ^ l = 1) (h2 : (x₂ : ZMod q) ^ l = 1)
    (hq1 : x₁ ^ ((l - 1) / 2) < q)
    (hind : ∀ i j : ℕ, x₁ ^ i = x₂ ^ j → i = 0 ∧ j = 0) :
    x₁ ^ ((l + 1) / 6) < x₂ := by
  have := Fact.mk hq
  have hl0 : 0 < l := hl.pos
  obtain ⟨t, rfl⟩ := hl
  set E := (2 * t + 1 - 1) / 2 with hE
  set k := (2 * t + 1 + 1) / 6 with hk
  have hkE : 2 * k ≤ E := by omega
  by_contra hcon
  push Not at hcon
  have hx1 : 2 ≤ x₁ := by
    rcases x₁ with _ | _ | x
    · simp [zero_pow hl0.ne'] at h1
    · exact absurd (hind 1 0 (by simp)).1 one_ne_zero
    · omega
  have hx2 : 2 ≤ x₂ := by
    rcases x₂ with _ | _ | x
    · simp [zero_pow hl0.ne'] at h2
    · exact absurd (hind 0 1 (by simp)).2 one_ne_zero
    · omega
  have hp1 : ∀ i, 0 < x₁ ^ i := fun i => pow_pos (by omega) i
  have hp2 : ∀ j, 0 < x₂ ^ j := fun j => pow_pos (by omega) j
  have key : ∀ i i' m, x₁ ^ i = x₁ ^ i' * x₂ ^ m → m = 0 := by
    intro i i' m h
    by_cases hii : i < i'
    · exfalso
      have : x₁ ^ i < x₁ ^ i' := Nat.pow_lt_pow_right hx1 hii
      have : x₁ ^ i' ≤ x₁ ^ i' * x₂ ^ m := Nat.le_mul_of_pos_right _ (hp2 m)
      omega
    · push Not at hii
      have e : x₁ ^ i = x₁ ^ i' * x₁ ^ (i - i') := by
        rw [← pow_add]; congr 1; omega
      rw [e] at h
      exact (hind _ _ (Nat.eq_of_mul_eq_mul_left (hp1 i') h)).2
  let f : ℕ → ℕ → ℕ := fun j i => x₁ ^ i * x₂ ^ j
  have hjj : ∀ {j j' i i'}, j ≤ j' → f j i = f j' i' → j = j' := by
    intro j j' i i' hj h
    have e : x₁ ^ i * x₂ ^ j = (x₁ ^ i' * x₂ ^ (j' - j)) * x₂ ^ j := by
      rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hj]; exact h
    have := key _ _ _ (Nat.eq_of_mul_eq_mul_right (hp2 j) e)
    omega
  have finj : ∀ j j' i i', f j i = f j' i' → j = j' := by
    intro j j' i i' h
    rcases le_total j j' with hj | hj
    · exact hjj hj h
    · exact (hjj hj h.symm).symm
  have finj2 : ∀ j, Function.Injective (f j) := by
    intro j i i' h
    exact Nat.pow_right_injective hx1 (Nat.eq_of_mul_eq_mul_right (hp2 j) h)
  let A : ℕ → Finset ℕ := fun j => (Finset.range (E - j * k + 1)).image (f j)
  have hcardA : ∀ j, (A j).card = E - j * k + 1 := fun j => by
    simp only [A]; rw [Finset.card_image_of_injective _ (finj2 j), Finset.card_range]
  have hdisj : ∀ j j', j ≠ j' → Disjoint (A j) (A j') := by
    intro j j' hne
    rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨i', -, h⟩ := Finset.mem_image.1 hy'
    exact hne (finj _ _ _ _ h.symm)
  let T := A 0 ∪ A 1 ∪ A 2
  have hcardT : T.card = (E + 1) + (E - k + 1) + (E - 2 * k + 1) := by
    simp only [T]
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2
        ⟨hdisj 0 2 (by norm_num), hdisj 1 2 (by norm_num)⟩),
      Finset.card_union_of_disjoint (hdisj 0 1 (by norm_num)), hcardA, hcardA, hcardA]
    simp only [zero_mul, Nat.sub_zero, one_mul]
  have hlt : ∀ y ∈ T, y < q := by
    intro y hy
    have : ∃ j ≤ 2, ∃ i, i + j * k ≤ E ∧ y = f j i := by
      simp only [T, Finset.mem_union] at hy
      rcases hy with (hy | hy) | hy <;> obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hy <;>
        rw [Finset.mem_range] at hi
      · exact ⟨0, by norm_num, i, by omega, rfl⟩
      · exact ⟨1, by norm_num, i, by omega, rfl⟩
      · exact ⟨2, le_rfl, i, by omega, rfl⟩
    obtain ⟨j, -, i, hij, rfl⟩ := this
    calc x₁ ^ i * x₂ ^ j ≤ x₁ ^ i * (x₁ ^ k) ^ j :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hcon j)
      _ = x₁ ^ (i + j * k) := by rw [← pow_mul, ← pow_add, mul_comm k j]
      _ ≤ x₁ ^ E := Nat.pow_le_pow_right (by omega) hij
      _ < q := hq1
  have hinj : Set.InjOn (fun y : ℕ => (y : ZMod q)) T := by
    intro y hy y' hy' h
    have := (ZMod.natCast_eq_natCast_iff' y y' q).1 h
    rwa [Nat.mod_eq_of_lt (hlt y hy), Nat.mod_eq_of_lt (hlt y' hy')] at this
  have hsub : T.image (fun y : ℕ => (y : ZMod q)) ⊆
      Polynomial.nthRootsFinset (2 * t + 1) (1 : ZMod q) := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    rw [Polynomial.mem_nthRootsFinset hl0]
    have : ∃ j i, y = f j i := by
      simp only [T, Finset.mem_union] at hy
      rcases hy with (hy | hy) | hy <;> obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy <;>
        exact ⟨_, i, rfl⟩
    obtain ⟨j, i, rfl⟩ := this
    simp only [f]
    push_cast
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j, pow_mul, pow_mul, h1, h2,
      one_pow, one_pow, one_mul]
  have hroots : (Polynomial.nthRootsFinset (2 * t + 1) (1 : ZMod q)).card ≤ 2 * t + 1 := by
    rw [Polynomial.nthRootsFinset_def]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
  have hcard := (Finset.card_le_card hsub).trans hroots
  rw [Finset.card_image_of_injOn hinj, hcardT] at hcard
  omega

/-- Clayton and Hansen, Lemma "Unique between S1 and S2" (arXiv 2303.11974): let
`a, b, c, d` be odd primes with `c > d`, `d ≠ 3`, `a ^ 2 + a + 1 = c d` and
`b ^ 2 + b + 1 = 3 c`. Then there is no odd prime `g` with `g ^ 2 + g + 1 = d h`, `d > h`,
where `h = 1` or `h` is an odd prime. -/
theorem ch_unique_S1_S2 {a b c d g h : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hd : d.Prime) (hb2 : b ≠ 2) (hd2 : d ≠ 2) (hd3 : d ≠ 3) (hcd : d < c)
    (hA : phi3 a = c * d) (hB : phi3 b = 3 * c) (hg : g.Prime) (hg2 : g ≠ 2)
    (hG : phi3 g = d * h) (hdh : h < d) (hh : h = 1 ∨ (h.Prime ∧ h ≠ 2)) : False := by
  have odd_of : ∀ {x : ℕ}, x.Prime → x ≠ 2 → x % 2 = 1 := by
    intro x hx hx2
    rcases hx.eq_two_or_odd with h | h
    · exact absurd h hx2
    · exact h
  have hb1 := odd_of hb hb2
  have hd1 := odd_of hd hd2
  have hg1 := odd_of hg hg2
  have hd5 : 5 ≤ d := by have := hd.two_le; omega
  obtain ⟨hcs, hrel⟩ := ch_factorization1 hc hA (by rw [hB, mul_comm]) hcd (by omega)
  have hbsq : b ^ 2 = 3 * a + 2 * b + 2 := by
    have := hB; rw [hcs] at this; unfold phi3 at this; omega
  have hcd30 : 30 ≤ c * d := by
    have : 6 ≤ c := by omega
    nlinarith
  have hb3 : 3 ≤ b := by have := hb.two_le; omega
  by_cases hg3 : g = 3
  · subst hg3
    have h13 : d = 13 := (Nat.prime_dvd_prime_iff_eq hd (by norm_num)).1
      ⟨h, by simpa [phi3] using hG⟩
    subst h13
    have hb' : b ^ 2 = 5 * b + 32 := by omega
    have : b ≤ 8 := by nlinarith
    interval_cases b <;> omega
  have hg30 : g % 3 ≠ 0 := by
    intro h0
    exact hg3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hg).1
      (Nat.dvd_of_mod_eq_zero h0)).symm
  by_cases hg31 : g % 3 = 1
  · have h3 : 3 ∣ d * h := hG ▸ (three_dvd_phi3_iff g).2 hg31
    have h3h : 3 ∣ h := by
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h' | h'
      · exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hd).1 h').symm hd3
      · exact h'
    have hh3 : h = 3 := by
      rcases hh with rfl | ⟨hhp, -⟩
      · omega
      · exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hhp).1 h3h).symm
    subst hh3
    obtain ⟨m, rfl⟩ : ∃ m, b = m + 3 := ⟨b - 3, by omega⟩
    have : phi3 g = phi3 m := by
      rw [hG]; unfold phi3
      have e1 : (m + 3) ^ 2 = m ^ 2 + 6 * m + 9 := by ring
      omega
    have := phi3_strictMono.injective this
    omega
  · have hg32 : g % 3 = 2 := by omega
    have hcd3 : ¬ 3 ∣ c * d := by
      intro h3
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h' | h'
      · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hc).1 h'; omega
      · exact hd3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hd).1 h').symm
    have ha31 : a % 3 ≠ 1 := fun h' => hcd3 (hA ▸ (three_dvd_phi3_iff a).2 h')
    have ha30 : a % 3 ≠ 0 := by
      intro h0
      have : a = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three ha).1
        (Nat.dvd_of_mod_eq_zero h0)).symm
      subst this
      have : phi3 3 = 13 := rfl
      omega
    have ha1 : a % 2 = 1 := by
      rcases ha.eq_two_or_odd with h' | h'
      · subst h'
        have : phi3 2 = 7 := rfl
        omega
      · exact h'
    have h2d : a < 2 * d := by
      have e : (3 : ℤ) * (2 * d - a) = ((b : ℤ) - 4) ^ 2 := by
        have h1 : (b : ℤ) ^ 2 = 3 * a + 2 * b + 2 := by exact_mod_cast hbsq
        have h2 : (a : ℤ) + 3 = b + d := by exact_mod_cast hrel
        linear_combination -6 * h2 - h1
      have hpos : (0 : ℤ) < ((b : ℤ) - 4) ^ 2 := by
        have : (b : ℤ) - 4 ≠ 0 := by omega
        positivity
      have : (a : ℤ) < 2 * d := by linarith
      exact_mod_cast this
    have hga : g < a := by
      apply phi3_strictMono.lt_iff_lt.1
      rw [hG, hA]
      calc d * h < d * d := Nat.mul_lt_mul_of_pos_left hdh (by omega)
        _ < c * d := Nat.mul_lt_mul_of_pos_right hcd (by omega)
    have hdA : d ∣ phi3 a := ⟨c, by rw [hA, mul_comm]⟩
    have hd6 := prime_dvd_phi3_mod_six hd hd3 hdA
    rcases phi3_common_prime_cases hd hdA ⟨h, hG⟩ with h' | h'
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hga.le).1 h'.symm
      rcases k with _ | _ | k
      · omega
      · omega
      · have : d * (k + 1 + 1) = d * k + 2 * d := by ring
        omega
    · obtain ⟨k, hk⟩ := h'
      have hk6 := mul_mod_six_of_one (k := k) hd6
      have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hk; omega)
      have : 5 ≤ k := by omega
      have := Nat.mul_le_mul_left d this
      omega

end OddPerfect

#print axioms OddPerfect.phi3_sq_eq
#print axioms OddPerfect.phi3_eq_mul_phi3_prime
#print axioms OddPerfect.phi3_mod
#print axioms OddPerfect.phi3_common_prime_cases
#print axioms OddPerfect.ch_factorization1
#print axioms OddPerfect.ch_zelProof1
#print axioms OddPerfect.ch_zelProof1_not_prime
#print axioms OddPerfect.ch_zelProof2
#print axioms OddPerfect.phi3_succ_sq
#print axioms OddPerfect.hansen_nielsen_two
#print axioms OddPerfect.no_double_threat
#print axioms OddPerfect.phi3_eq_three_mul_phi3_prime
#print axioms OddPerfect.no_phi3_eq_three_mul_phi3
#print axioms OddPerfect.card_le_two_of_dvd_phi3
#print axioms OddPerfect.card_filter_range_dvd_phi3_le_two
#print axioms OddPerfect.card_image_zmod_le_two_of_dvd_phi3
#print axioms OddPerfect.zelinsky_shared_prime_two
#print axioms OddPerfect.zelinsky_shared_prime_one
#print axioms OddPerfect.zelinsky_precursor
#print axioms OddPerfect.zelinsky_precursor_of_not_three_dvd
#print axioms OddPerfect.no_phi3_eq_three_mul_phi3_mul_phi3
#print axioms OddPerfect.phi3_ne_cube_of_prime
#print axioms OddPerfect.no_phi3_eq_triple_mod_five
#print axioms OddPerfect.hansen_nielsen_three_family
#print axioms OddPerfect.hansen_nielsen_three_sporadic
#print axioms OddPerfect.quadruple_threat_191
#print axioms OddPerfect.phi5_mod
#print axioms OddPerfect.phi3_sub_three
#print axioms OddPerfect.phi5_sub_five
#print axioms OddPerfect.five_dvd_phi5_iff
#print axioms OddPerfect.phi5_mod_twentyfive
#print axioms OddPerfect.not_twentyfive_dvd_phi5
#print axioms OddPerfect.padicValNat_five_phi5
#print axioms OddPerfect.phi3_phi5
#print axioms OddPerfect.gcd_phi3_phi5_factors_dvd
#print axioms OddPerfect.prime_dvd_phi3_phi5_factors
#print axioms OddPerfect.ch_factorization3
#print axioms OddPerfect.ch_factorization2
#print axioms OddPerfect.ch_unique_S1_S31
#print axioms OddPerfect.ch_unique_S21_S31
#print axioms OddPerfect.ch_semilinked_S31
#print axioms OddPerfect.yamada_gap
#print axioms OddPerfect.ch_unique_S1_S2
