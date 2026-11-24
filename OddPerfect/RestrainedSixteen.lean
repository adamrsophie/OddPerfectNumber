import OddPerfect.RestrainedEleven

/-!
# Restrained odd perfect numbers: tail packing for the sieve bound

Setting of `restrained_omega_ge_sieve` (`OddPerfect.RestrainedEleven`): `N` is an odd perfect
number with special prime `q`, every prime factor other than `q` and `3` has exponent 2, and
`R`, the prime factors other than `3` and `q`, consists of `Good` primes at least
`B = 132257`. With `X = 10 ^ 6` and `y = (X + 1) / X`:

* A counted certificate `CertC` records a bound `d` on the size of the leftover set `T`. The
  checker `runL` is sound for it with `d` the number of zero digits of the limb list
  (`runL_soundC`), and the counts add (`certC_trans`). The landed sieve data then gives `T`
  with at most 9063 members (`certC_all`); no witness is checked again.
* The members of `R` up to `X` lie in `T`, so at least `#R - 9063` members exceed `X`. Instead
  of bounding their factors `fac X t ≤ 1` by 1, a set `S` of `m` distinct odd numbers at least
  `x₀` has `(∏_S t/(t - 1)) ^ 2 ≤ 1 + 4 m/(2 x₀ - 3)` (`prod_sq_le`), from
  `(x/(x - 1)) ^ 2 (2 x + 4 m + 1)/(2 x + 1) ≤ (2 x + 4 m + 1)/(2 x - 3)`.
* One kernel comparison (`final_ineqC`) gives `#R ≥ 360547`, hence `ω(N) ≥ 360549`
  (`restrained_omega_ge_tail`), `v_3(N) ≥ 180274` since `ω(N) ≤ 2 v_3(N) + 3` and the
  exponent of 3 is even (`restrained_tail_le_three`), and `Ω(N) ≥ 901369`
  (`restrained_Omega_ge_tail`).

Relation to the literature. Ochem and Zelinsky (arXiv 2607.19746) state a far larger lower
bound for the exponent of 3 in this family, obtained by a long computation; that bound is not
proved here. The theorems of this file are conditional family results checked by the kernel;
no novelty is claimed. The odd perfect number conjecture is open and nothing here decides it.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.omega ArithmeticFunction.Omega

namespace OddPerfect

namespace RestrainedSixteen

open RestrainedSeven RestrainedEight RestrainedElevenCheck RestrainedEleven

/-! ## Counted certificates -/

/-- The number of zero digits among the `c` lowest digits of `W` in base `2 ^ 18`. -/
def zl : ℕ → ℕ → ℕ
  | 0, _ => 0
  | c + 1, W => (if W % 262144 = 0 then 1 else 0) + zl c (W / 262144)

/-- The number of zero digits of a limb list, sixteen digits per limb. -/
def zeros : List ℕ → ℕ
  | [] => 0
  | W :: L => zl 16 W + zeros L

/-- `Cert` with a bound `d` on the size of the leftover set. -/
def CertC (X lo hi a b d : ℕ) : Prop :=
  lo ≤ hi ∧ ∃ T : Finset ℕ, (∀ m ∈ T, lo ≤ m ∧ m < hi) ∧
    (∀ m, lo ≤ m → m < hi → m.Prime → Good m → m ∈ T) ∧ T.card ≤ d ∧
    (a : ℚ) * ∏ m ∈ T, fac X m ≤ b

/-- Counted certificates of adjacent ranges combine; the counts add. -/
theorem certC_trans {X lo mid hi a b c d e : ℕ} (h₁ : CertC X lo mid a b d)
    (h₂ : CertC X mid hi b c e) : CertC X lo hi a c (d + e) := by
  classical
  obtain ⟨hl₁, T₁, hT₁, hc₁, hd₁, hp₁⟩ := h₁
  obtain ⟨hl₂, T₂, hT₂, hc₂, hd₂, hp₂⟩ := h₂
  have hdis : Disjoint T₁ T₂ := Finset.disjoint_left.mpr fun m h1 h2 => by
    have := hT₁ m h1
    have := hT₂ m h2
    omega
  refine ⟨by omega, T₁ ∪ T₂, fun m hm => ?_, fun m hlo hhi hp hg => ?_, ?_, ?_⟩
  · rcases Finset.mem_union.mp hm with h | h
    · have := hT₁ m h
      omega
    · have := hT₂ m h
      omega
  · rcases Nat.lt_or_ge m mid with h' | h'
    · exact Finset.mem_union_left _ (hc₁ m hlo h' hp hg)
    · exact Finset.mem_union_right _ (hc₂ m h' hhi hp hg)
  · rw [Finset.card_union_of_disjoint hdis]
    omega
  · rw [Finset.prod_union hdis, ← mul_assoc]
    have h0 : 0 ≤ ∏ m ∈ T₂, fac X m := Finset.prod_nonneg fun m _ => fac_nonneg X m
    calc (a : ℚ) * (∏ m ∈ T₁, fac X m) * ∏ m ∈ T₂, fac X m
        ≤ (b : ℚ) * ∏ m ∈ T₂, fac X m := mul_le_mul_of_nonneg_right hp₁ h0
      _ ≤ c := hp₂

/-- A larger count is weaker. -/
theorem certC_mono {X lo hi a b d d' : ℕ} (hd : d ≤ d') (h : CertC X lo hi a b d) :
    CertC X lo hi a b d' := by
  obtain ⟨hl, T, hT, hc, hcard, hp⟩ := h
  exact ⟨hl, T, hT, hc, hcard.trans hd, hp⟩

/-- Soundness of one limb, with the count of its zero digits. -/
theorem runLimb_soundC {X : ℕ} : ∀ (c n W acc a : ℕ), runLimb X c n W acc = some a →
    n % 2 = 1 → 3 ≤ n → CertC X n (n + 2 * c) acc a (zl c W)
  | 0, n, W, acc, a, h, _, _ => by
    simp only [runLimb, beq_iff_eq] at h
    split_ifs at h
    cases h
    exact ⟨by omega, ∅, by simp, fun m h1 h2 => by omega, by simp, by simp⟩
  | c + 1, n, W, acc, a, h, hodd, h3 => by
    have hnext : ∀ m, n ≤ m → m < n + 2 * (c + 1) → m ≠ n → m.Prime → n + 2 ≤ m := by
      intro m h1 h2 hmn hp
      rcases (by omega : m = n + 1 ∨ n + 2 ≤ m) with rfl | h'
      · exact absurd ((Nat.Prime.even_iff hp).mp (by
          rw [Nat.even_add_one, Nat.not_even_iff_odd]; exact Nat.odd_iff.mpr hodd)) (by omega)
      · exact h'
    have hz : zl (c + 1) W = (if W % 262144 = 0 then 1 else 0) + zl c (W / 262144) := rfl
    simp only [runLimb] at h
    split_ifs at h with hw hwit
    · have hw' : W % 262144 = 0 := by simpa using hw
      rw [hz, if_pos hw']
      obtain ⟨-, T, hT, hc, hcard, hp⟩ :=
        runLimb_soundC c (n + 2) _ _ a h (by omega) (by omega)
      have hnT : n ∉ T := fun hm => by have := hT n hm; omega
      refine ⟨by omega, insert n T, fun m hm => ?_, fun m h1 h2 hpm hg => ?_, ?_, ?_⟩
      · rcases Finset.mem_insert.mp hm with rfl | hm
        · omega
        · have := hT m hm; omega
      · by_cases hmn : m = n
        · exact hmn ▸ Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hc m (hnext m h1 h2 hmn hpm) (by omega) hpm hg)
      · rw [Finset.card_insert_of_notMem hnT]
        omega
      · rw [Finset.prod_insert hnT, ← mul_assoc]
        have h0 : 0 ≤ ∏ m ∈ T, fac X m := Finset.prod_nonneg fun m _ => fac_nonneg X m
        exact le_trans (mul_le_mul_of_nonneg_right (fac_step h3) h0) hp
    · have hw' : W % 262144 ≠ 0 := by simpa using hw
      rw [hz, if_neg hw', zero_add]
      obtain ⟨-, T, hT, hc, hcard, hp⟩ :=
        runLimb_soundC c (n + 2) _ _ a h (by omega) (by omega)
      refine ⟨by omega, T, fun m hm => ?_, fun m h1 h2 hpm hg => ?_, hcard, hp⟩
      · have := hT m hm; omega
      · by_cases hmn : m = n
        · subst hmn
          exact (wit_sound hwit hpm hg).elim
        · exact hc m (hnext m h1 h2 hmn hpm) (by omega) hpm hg

/-- **Soundness of the checker with counts.** The leftover set has at most `zeros L`
members. -/
theorem runL_soundC {X : ℕ} : ∀ {L : List ℕ} {n acc hi b : ℕ}, runL X L n acc hi b = true →
    CertC X n hi acc b (zeros L)
  | [], n, acc, hi, b, h => by
    simp only [runL, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨rfl, hb⟩ := h
    refine ⟨le_rfl, ∅, by simp, fun m h1 h2 => by omega, by simp, ?_⟩
    simpa using (Nat.cast_le (α := ℚ)).mpr hb
  | W :: L, n, acc, hi, b, h => by
    simp only [runL, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨hodd, h3⟩, h⟩ := h
    split at h
    · rename_i a ha
      exact certC_trans (runLimb_soundC 16 n W acc a ha hodd h3) (runL_soundC h)
    · exact absurd h (by simp)

/-- A checked block with a known zero count. -/
theorem blockC {X n acc hi b k : ℕ} {L : List ℕ} (hz : zeros L = k)
    (h : runL X L n acc hi b = true) : CertC X n hi acc b k :=
  hz ▸ runL_soundC h

/-- Zero digits of the block at `132257`. -/
theorem zb132257 : zeros wb132257 = 192 := by decide +kernel

/-- Zero digits of the block at `148641`. -/
theorem zb148641 : zeros wb148641 = 187 := by decide +kernel

/-- Zero digits of the block at `165025`. -/
theorem zb165025 : zeros wb165025 = 173 := by decide +kernel

/-- Zero digits of the block at `181409`. -/
theorem zb181409 : zeros wb181409 = 184 := by decide +kernel

/-- Zero digits of the block at `197793`. -/
theorem zb197793 : zeros wb197793 = 186 := by decide +kernel

/-- Zero digits of the block at `214177`. -/
theorem zb214177 : zeros wb214177 = 165 := by decide +kernel

/-- Zero digits of the block at `230561`. -/
theorem zb230561 : zeros wb230561 = 169 := by decide +kernel

/-- Zero digits of the block at `246945`. -/
theorem zb246945 : zeros wb246945 = 195 := by decide +kernel

/-- Zero digits of the block at `263329`. -/
theorem zb263329 : zeros wb263329 = 169 := by decide +kernel

/-- Zero digits of the block at `279713`. -/
theorem zb279713 : zeros wb279713 = 182 := by decide +kernel

/-- Zero digits of the block at `296097`. -/
theorem zb296097 : zeros wb296097 = 162 := by decide +kernel

/-- Zero digits of the block at `312481`. -/
theorem zb312481 : zeros wb312481 = 169 := by decide +kernel

/-- Zero digits of the block at `328865`. -/
theorem zb328865 : zeros wb328865 = 179 := by decide +kernel

/-- Zero digits of the block at `345249`. -/
theorem zb345249 : zeros wb345249 = 186 := by decide +kernel

/-- Zero digits of the block at `361633`. -/
theorem zb361633 : zeros wb361633 = 161 := by decide +kernel

/-- Zero digits of the block at `378017`. -/
theorem zb378017 : zeros wb378017 = 178 := by decide +kernel

/-- Zero digits of the block at `394401`. -/
theorem zb394401 : zeros wb394401 = 153 := by decide +kernel

/-- Zero digits of the block at `410785`. -/
theorem zb410785 : zeros wb410785 = 190 := by decide +kernel

/-- Zero digits of the block at `427169`. -/
theorem zb427169 : zeros wb427169 = 164 := by decide +kernel

/-- Zero digits of the block at `443553`. -/
theorem zb443553 : zeros wb443553 = 156 := by decide +kernel

/-- Zero digits of the block at `459937`. -/
theorem zb459937 : zeros wb459937 = 188 := by decide +kernel

/-- Zero digits of the block at `476321`. -/
theorem zb476321 : zeros wb476321 = 168 := by decide +kernel

/-- Zero digits of the block at `492705`. -/
theorem zb492705 : zeros wb492705 = 183 := by decide +kernel

/-- Zero digits of the block at `509089`. -/
theorem zb509089 : zeros wb509089 = 165 := by decide +kernel

/-- Zero digits of the block at `525473`. -/
theorem zb525473 : zeros wb525473 = 169 := by decide +kernel

/-- Zero digits of the block at `541857`. -/
theorem zb541857 : zeros wb541857 = 155 := by decide +kernel

/-- Zero digits of the block at `558241`. -/
theorem zb558241 : zeros wb558241 = 163 := by decide +kernel

/-- Zero digits of the block at `574625`. -/
theorem zb574625 : zeros wb574625 = 157 := by decide +kernel

/-- Zero digits of the block at `591009`. -/
theorem zb591009 : zeros wb591009 = 178 := by decide +kernel

/-- Zero digits of the block at `607393`. -/
theorem zb607393 : zeros wb607393 = 156 := by decide +kernel

/-- Zero digits of the block at `623777`. -/
theorem zb623777 : zeros wb623777 = 168 := by decide +kernel

/-- Zero digits of the block at `640161`. -/
theorem zb640161 : zeros wb640161 = 171 := by decide +kernel

/-- Zero digits of the block at `656545`. -/
theorem zb656545 : zeros wb656545 = 188 := by decide +kernel

/-- Zero digits of the block at `672929`. -/
theorem zb672929 : zeros wb672929 = 172 := by decide +kernel

/-- Zero digits of the block at `689313`. -/
theorem zb689313 : zeros wb689313 = 150 := by decide +kernel

/-- Zero digits of the block at `705697`. -/
theorem zb705697 : zeros wb705697 = 177 := by decide +kernel

/-- Zero digits of the block at `722081`. -/
theorem zb722081 : zeros wb722081 = 164 := by decide +kernel

/-- Zero digits of the block at `738465`. -/
theorem zb738465 : zeros wb738465 = 162 := by decide +kernel

/-- Zero digits of the block at `754849`. -/
theorem zb754849 : zeros wb754849 = 158 := by decide +kernel

/-- Zero digits of the block at `771233`. -/
theorem zb771233 : zeros wb771233 = 179 := by decide +kernel

/-- Zero digits of the block at `787617`. -/
theorem zb787617 : zeros wb787617 = 144 := by decide +kernel

/-- Zero digits of the block at `804001`. -/
theorem zb804001 : zeros wb804001 = 183 := by decide +kernel

/-- Zero digits of the block at `820385`. -/
theorem zb820385 : zeros wb820385 = 152 := by decide +kernel

/-- Zero digits of the block at `836769`. -/
theorem zb836769 : zeros wb836769 = 152 := by decide +kernel

/-- Zero digits of the block at `853153`. -/
theorem zb853153 : zeros wb853153 = 183 := by decide +kernel

/-- Zero digits of the block at `869537`. -/
theorem zb869537 : zeros wb869537 = 188 := by decide +kernel

/-- Zero digits of the block at `885921`. -/
theorem zb885921 : zeros wb885921 = 171 := by decide +kernel

/-- Zero digits of the block at `902305`. -/
theorem zb902305 : zeros wb902305 = 170 := by decide +kernel

/-- Zero digits of the block at `918689`. -/
theorem zb918689 : zeros wb918689 = 167 := by decide +kernel

/-- Zero digits of the block at `935073`. -/
theorem zb935073 : zeros wb935073 = 174 := by decide +kernel

/-- Zero digits of the block at `951457`. -/
theorem zb951457 : zeros wb951457 = 171 := by decide +kernel

/-- Zero digits of the block at `967841`. -/
theorem zb967841 : zeros wb967841 = 179 := by decide +kernel

/-- Zero digits of the block at `984225`. -/
theorem zb984225 : zeros wb984225 = 158 := by decide +kernel

/-- The counted certificate of the whole range `132257 ≤ n ≤ 10 ^ 6`: the leftover set has at
most 9063 members (the zero digits of the landed limb lists). -/
theorem certC_all :
    CertC 1000000 132257 1000001 18446744073709551616 18677387639328032348 9063 := by
  have h := (blockC zb132257 ok_b132257)
  have h := certC_trans h (blockC zb148641 ok_b148641)
  have h := certC_trans h (blockC zb165025 ok_b165025)
  have h := certC_trans h (blockC zb181409 ok_b181409)
  have h := certC_trans h (blockC zb197793 ok_b197793)
  have h := certC_trans h (blockC zb214177 ok_b214177)
  have h := certC_trans h (blockC zb230561 ok_b230561)
  have h := certC_trans h (blockC zb246945 ok_b246945)
  have h := certC_trans h (blockC zb263329 ok_b263329)
  have h := certC_trans h (blockC zb279713 ok_b279713)
  have h := certC_trans h (blockC zb296097 ok_b296097)
  have h := certC_trans h (blockC zb312481 ok_b312481)
  have h := certC_trans h (blockC zb328865 ok_b328865)
  have h := certC_trans h (blockC zb345249 ok_b345249)
  have h := certC_trans h (blockC zb361633 ok_b361633)
  have h := certC_trans h (blockC zb378017 ok_b378017)
  have h := certC_trans h (blockC zb394401 ok_b394401)
  have h := certC_trans h (blockC zb410785 ok_b410785)
  have h := certC_trans h (blockC zb427169 ok_b427169)
  have h := certC_trans h (blockC zb443553 ok_b443553)
  have h := certC_trans h (blockC zb459937 ok_b459937)
  have h := certC_trans h (blockC zb476321 ok_b476321)
  have h := certC_trans h (blockC zb492705 ok_b492705)
  have h := certC_trans h (blockC zb509089 ok_b509089)
  have h := certC_trans h (blockC zb525473 ok_b525473)
  have h := certC_trans h (blockC zb541857 ok_b541857)
  have h := certC_trans h (blockC zb558241 ok_b558241)
  have h := certC_trans h (blockC zb574625 ok_b574625)
  have h := certC_trans h (blockC zb591009 ok_b591009)
  have h := certC_trans h (blockC zb607393 ok_b607393)
  have h := certC_trans h (blockC zb623777 ok_b623777)
  have h := certC_trans h (blockC zb640161 ok_b640161)
  have h := certC_trans h (blockC zb656545 ok_b656545)
  have h := certC_trans h (blockC zb672929 ok_b672929)
  have h := certC_trans h (blockC zb689313 ok_b689313)
  have h := certC_trans h (blockC zb705697 ok_b705697)
  have h := certC_trans h (blockC zb722081 ok_b722081)
  have h := certC_trans h (blockC zb738465 ok_b738465)
  have h := certC_trans h (blockC zb754849 ok_b754849)
  have h := certC_trans h (blockC zb771233 ok_b771233)
  have h := certC_trans h (blockC zb787617 ok_b787617)
  have h := certC_trans h (blockC zb804001 ok_b804001)
  have h := certC_trans h (blockC zb820385 ok_b820385)
  have h := certC_trans h (blockC zb836769 ok_b836769)
  have h := certC_trans h (blockC zb853153 ok_b853153)
  have h := certC_trans h (blockC zb869537 ok_b869537)
  have h := certC_trans h (blockC zb885921 ok_b885921)
  have h := certC_trans h (blockC zb902305 ok_b902305)
  have h := certC_trans h (blockC zb918689 ok_b918689)
  have h := certC_trans h (blockC zb935073 ok_b935073)
  have h := certC_trans h (blockC zb951457 ok_b951457)
  have h := certC_trans h (blockC zb967841 ok_b967841)
  have h := certC_trans h (blockC zb984225 ok_b984225)
  exact certC_mono (by norm_num) h

/-! ## Distinct odd numbers above a bound -/

/-- The step of `prod_sq_le`: `(x/(x - 1)) ^ 2 (1 + 4 m/(2 (x + 2) - 3)) ≤ 1 + 4 (m + 1)/(2 x - 3)`
for `x ≥ 3`. -/
theorem step_le {x m : ℚ} (hx : 3 ≤ x) (hm : 0 ≤ m) :
    (x / (x - 1)) ^ 2 * (1 + 4 * m / (2 * (x + 2) - 3)) ≤ 1 + 4 * (m + 1) / (2 * x - 3) := by
  have h1 : x - 1 ≠ 0 := by intro h; linarith
  have h2 : 2 * (x + 2) - 3 ≠ 0 := by intro h; linarith
  have h3 : 2 * x - 3 ≠ 0 := by intro h; linarith
  have e1 : (x / (x - 1)) ^ 2 * (1 + 4 * m / (2 * (x + 2) - 3)) =
      x ^ 2 * (2 * x + 1 + 4 * m) / ((x - 1) ^ 2 * (2 * x + 1)) := by
    field_simp
    ring
  have e2 : 1 + 4 * (m + 1) / (2 * x - 3) = (2 * x + 1 + 4 * m) / (2 * x - 3) := by
    field_simp
    ring
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by linarith)]
  have key : (2 * x + 1 + 4 * m) * ((x - 1) ^ 2 * (2 * x + 1)) -
      x ^ 2 * (2 * x + 1 + 4 * m) * (2 * x - 3) = 2 * x + 1 + 4 * m := by ring
  linarith

/-- **Packing of distinct odd numbers.** A set `S` of odd numbers, each at least `x₀ ≥ 3`, has
`(∏_S t/(t - 1)) ^ 2 ≤ 1 + 4 #S/(2 x₀ - 3)`. -/
theorem prod_sq_le (S : Finset ℕ) : ∀ x₀ : ℕ, 3 ≤ x₀ → (∀ t ∈ S, x₀ ≤ t ∧ t % 2 = 1) →
    (∏ t ∈ S, (t : ℚ) / (t - 1)) ^ 2 ≤ 1 + 4 * (S.card : ℚ) / (2 * x₀ - 3) := by
  induction S using Finset.induction_on_min with
  | empty => intro _ _ _; simp
  | insert a s ha ih =>
    intro x₀ hx₀ hS
    have haS : a ∉ s := fun h => lt_irrefl _ (ha a h)
    obtain ⟨hxa, hao⟩ := hS a (Finset.mem_insert_self _ _)
    have ih' := ih (a + 2) (by omega) fun t ht => by
      have h1 := ha t ht
      have h2 := hS t (Finset.mem_insert_of_mem ht)
      exact ⟨by omega, h2.2⟩
    rw [Finset.prod_insert haS, Finset.card_insert_of_notMem haS, mul_pow]
    have ha3 : (3 : ℚ) ≤ a := by exact_mod_cast (show 3 ≤ a by omega)
    have hx3 : (3 : ℚ) ≤ x₀ := by exact_mod_cast hx₀
    have hxa' : (x₀ : ℚ) ≤ a := by exact_mod_cast hxa
    push_cast at ih' ⊢
    have hsq : 0 ≤ ((a : ℚ) / (a - 1)) ^ 2 := sq_nonneg _
    calc ((a : ℚ) / (a - 1)) ^ 2 * (∏ t ∈ s, (t : ℚ) / (t - 1)) ^ 2
        ≤ ((a : ℚ) / (a - 1)) ^ 2 * (1 + 4 * (s.card : ℚ) / (2 * ((a : ℚ) + 2) - 3)) :=
          mul_le_mul_of_nonneg_left ih' hsq
      _ ≤ 1 + 4 * ((s.card : ℚ) + 1) / (2 * (a : ℚ) - 3) := step_le ha3 (by positivity)
      _ ≤ 1 + 4 * ((s.card : ℚ) + 1) / (2 * (x₀ : ℚ) - 3) := by
          gcongr
          all_goals first | positivity | linarith

/-! ## The counting step -/

/-- **The counting step with the tail.** Setting of `card_gt_of_cert`, with a counted
certificate `CertC X B X₁ a b d` and the comparison
`9 B ^ 2 b ^ 2 (X₁ ^ d) ^ 2 (X₂ + 4 M) ≤ 16 c ^ 2 a ^ 2 (X ^ d) ^ 2 X₂`, where `B = c + 1`,
`X₁ = X + 1` and `X₂ = 2 X - 1`. Then `M + d < #R`. -/
theorem card_gt_of_certC {N q X X₁ X₂ B c a b d M : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N)
    (hqN : q ∈ N.primeFactors) (hq3 : q ≠ 3) (hBc : B = c + 1) (hc : 1 ≤ c) (hqB : B ≤ q)
    (hR : ∀ r ∈ (N.primeFactors.erase 3).erase q, Good r ∧ B ≤ r) (hX : 2 ≤ X)
    (hX₁ : X₁ = X + 1) (hX₂ : X₂ + 1 = 2 * X) (hcert : CertC X B X₁ a b d) (ha : 0 < a)
    (hineq : 9 * B ^ 2 * b ^ 2 * (X₁ ^ d) ^ 2 * (X₂ + 4 * M) ≤
      16 * c ^ 2 * a ^ 2 * (X ^ d) ^ 2 * X₂) :
    M + d < ((N.primeFactors.erase 3).erase q).card := by
  classical
  subst hBc hX₁
  set R := (N.primeFactors.erase 3).erase q with hRdef
  obtain ⟨-, T, hT, hcov, hcard, hprod⟩ := hcert
  have hgt := prod_erase_three_gt h h3
  have hqm : q ∈ N.primeFactors.erase 3 := Finset.mem_erase.mpr ⟨hq3, hqN⟩
  rw [← Finset.mul_prod_erase _ _ hqm] at hgt
  have hrp : ∀ r ∈ R, r.Prime := fun r hr =>
    Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr))
  have hX1 : 1 ≤ X := by omega
  set y : ℚ := ((X + 1 : ℚ) / X) with hy
  have hX' : (0 : ℚ) < X := by exact_mod_cast hX1
  have hy1 : 1 ≤ y := by
    rw [hy, le_div_iff₀ hX']
    linarith
  have hy0 : 0 ≤ y := by linarith
  have hF0 : ∀ n, 0 ≤ fac X n := fac_nonneg X
  -- the component of `q`
  have hAq : abundancy (q ^ N.factorization q) ≤ ((c + 1 : ℕ) : ℚ) / c :=
    (abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors hqN) _).le.trans
      (div_pred_le hc hqB)
  have hAq0 : 0 ≤ abundancy (q ^ N.factorization q) :=
    (abundancy_pos (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hqN).ne_zero)).le
  -- the components of `R`
  have hP0 : 0 ≤ ∏ r ∈ R, abundancy (r ^ N.factorization r) :=
    Finset.prod_nonneg fun r hr => (abundancy_pos (pow_ne_zero _ (hrp r hr).ne_zero)).le
  have hP1 : ∏ r ∈ R, abundancy (r ^ N.factorization r) ≤ ∏ r ∈ R, y * fac X r := by
    refine Finset.prod_le_prod (fun r hr => (abundancy_pos (pow_ne_zero _
      (hrp r hr).ne_zero)).le) fun r hr => ?_
    rw [hy, ← div_pred_eq hX1 (hrp r hr).two_le]
    exact (abundancy_prime_pow_lt (hrp r hr) _).le
  rw [Finset.prod_mul_distrib, Finset.prod_const] at hP1
  -- the split at `X`
  set Rhi := R.filter (fun r => X + 1 ≤ r) with hRhi
  set Rlo := R.filter (fun r => ¬ X + 1 ≤ r) with hRlo
  have hlo_sub : Rlo ⊆ T := fun r hr => by
    obtain ⟨hrR, hrX⟩ := Finset.mem_filter.mp hr
    exact hcov r (hR r hrR).2 (by omega) (hrp r hrR) (hR r hrR).1
  have hlo_card : Rlo.card ≤ d := (Finset.card_le_card hlo_sub).trans hcard
  have hsplit : Rhi.card + Rlo.card = R.card := Finset.card_filter_add_card_filter_not _
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (s := Rhi) (n := R.card - d)
    (by omega)
  have hS : ∀ t ∈ S, X + 1 ≤ t ∧ t.Prime := fun t ht => by
    obtain ⟨htR, htX⟩ := Finset.mem_filter.mp (hSsub ht)
    exact ⟨htX, hrp t htR⟩
  have hfR : ∏ r ∈ R, fac X r = (∏ r ∈ Rhi, fac X r) * ∏ r ∈ Rlo, fac X r :=
    (Finset.prod_filter_mul_prod_filter_not R _ _).symm
  have hlo : ∏ r ∈ Rlo, fac X r ≤ ∏ n ∈ T, fac X n := by
    refine Finset.prod_le_prod_of_subset_of_one_le hlo_sub (fun r _ => hF0 r) fun n hn _ => ?_
    have := hT n hn
    exact one_le_fac (by omega) (by omega)
  have hhi : ∏ r ∈ Rhi, fac X r ≤ ∏ r ∈ S, fac X r := by
    refine Finset.prod_le_prod_of_subset_of_le_one hSsub (fun r _ => hF0 r) fun r hr _ => ?_
    exact fac_le_one hX1 (Finset.mem_filter.mp hr).2
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hTb : ∏ n ∈ T, fac X n ≤ (b : ℚ) / a := by
    rw [le_div_iff₀ ha', mul_comm]
    exact hprod
  -- the tail
  set P := ∏ t ∈ S, (t : ℚ) / (t - 1) with hP
  have hPeq : P = y ^ S.card * ∏ t ∈ S, fac X t := by
    rw [hP, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t ht => ?_
    rw [hy, ← div_pred_eq hX1 (hS t ht).2.two_le]
  have hP0' : 0 ≤ P := by
    rw [hPeq]
    exact mul_nonneg (pow_nonneg hy0 _) (Finset.prod_nonneg fun t _ => hF0 t)
  have hPsq : P ^ 2 ≤ 1 + 4 * (S.card : ℚ) / (2 * ((X + 1 : ℕ) : ℚ) - 3) :=
    prod_sq_le S (X + 1) (by omega) fun t ht => by
      obtain ⟨h1, h2⟩ := hS t ht
      refine ⟨h1, ?_⟩
      rcases h2.eq_two_or_odd with h2' | h2'
      · omega
      · exact h2'
  -- assembling
  by_contra hK
  have hSM : S.card ≤ M := by omega
  have hyR : y ^ R.card ≤ y ^ d * y ^ S.card := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hy1 (by omega)
  have hmain : ∏ r ∈ R, abundancy (r ^ N.factorization r) ≤ y ^ d * ((b : ℚ) / a) * P := by
    have hT0 : 0 ≤ ∏ n ∈ T, fac X n := Finset.prod_nonneg fun n _ => hF0 n
    have hS0 : 0 ≤ ∏ r ∈ S, fac X r := Finset.prod_nonneg fun r _ => hF0 r
    have hlo0 : 0 ≤ ∏ r ∈ Rlo, fac X r := Finset.prod_nonneg fun r _ => hF0 r
    have hfac : ∏ r ∈ R, fac X r ≤ (∏ r ∈ S, fac X r) * ∏ n ∈ T, fac X n := by
      rw [hfR]
      exact mul_le_mul hhi hlo hlo0 hS0
    calc ∏ r ∈ R, abundancy (r ^ N.factorization r) ≤ y ^ R.card * ∏ r ∈ R, fac X r := hP1
      _ ≤ (y ^ d * y ^ S.card) * ((∏ r ∈ S, fac X r) * ((b : ℚ) / a)) :=
          mul_le_mul hyR (hfac.trans (mul_le_mul_of_nonneg_left hTb hS0))
            (Finset.prod_nonneg fun r _ => hF0 r) (by positivity)
      _ = y ^ d * ((b : ℚ) / a) * P := by rw [hPeq]; ring
  set Z : ℚ := ((c + 1 : ℕ) : ℚ) / c * (y ^ d * ((b : ℚ) / a)) with hZ
  have hZ0 : 0 ≤ Z := by
    have : (0 : ℚ) ≤ (b : ℚ) / a := by positivity
    exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg hy0 _) this)
  have hlt : (4 : ℚ) / 3 < Z * P := by
    refine lt_of_lt_of_le hgt ?_
    calc abundancy (q ^ N.factorization q) * ∏ r ∈ R, abundancy (r ^ N.factorization r)
        ≤ ((c + 1 : ℕ) : ℚ) / c * (y ^ d * ((b : ℚ) / a) * P) :=
          mul_le_mul hAq hmain hP0 (by positivity)
      _ = Z * P := by rw [hZ]; ring
  have hX₂' : (X₂ : ℚ) = 2 * X - 1 := by
    have : ((X₂ + 1 : ℕ) : ℚ) = ((2 * X : ℕ) : ℚ) := by rw [hX₂]
    push_cast at this
    linarith
  have hX₂0 : (0 : ℚ) < X₂ := by
    have : (2 : ℚ) ≤ X := by exact_mod_cast hX
    linarith
  have hPM : P ^ 2 ≤ 1 + 4 * (M : ℚ) / X₂ := by
    refine hPsq.trans ?_
    have hSM' : (S.card : ℚ) ≤ M := by exact_mod_cast hSM
    push_cast
    rw [show 2 * ((X : ℚ) + 1) - 3 = X₂ by rw [hX₂']; ring]
    gcongr
  have hsq : (16 : ℚ) / 9 < Z ^ 2 * (1 + 4 * (M : ℚ) / X₂) := by
    have h1 : ((4 : ℚ) / 3) ^ 2 < (Z * P) ^ 2 := by
      have : (0 : ℚ) ≤ 4 / 3 := by norm_num
      exact pow_lt_pow_left₀ hlt this (by norm_num)
    calc (16 : ℚ) / 9 = ((4 : ℚ) / 3) ^ 2 := by norm_num
      _ < (Z * P) ^ 2 := h1
      _ = Z ^ 2 * P ^ 2 := by ring
      _ ≤ Z ^ 2 * (1 + 4 * (M : ℚ) / X₂) := mul_le_mul_of_nonneg_left hPM (sq_nonneg Z)
  have hq : ((9 * (c + 1) ^ 2 * b ^ 2 * ((X + 1) ^ d) ^ 2 * (X₂ + 4 * M) : ℕ) : ℚ) ≤
      ((16 * c ^ 2 * a ^ 2 * (X ^ d) ^ 2 * X₂ : ℕ) : ℚ) := by
    exact_mod_cast hineq
  push_cast at hq
  have hc' : (0 : ℚ) < c := by exact_mod_cast hc
  have hXd : (0 : ℚ) < (X : ℚ) ^ d := pow_pos hX' d
  rw [hZ, hy, div_pow] at hsq
  have hkey : (((c + 1 : ℕ) : ℚ) / c * (((X : ℚ) + 1) ^ d / (X : ℚ) ^ d * ((b : ℚ) / a))) ^ 2 *
      (1 + 4 * (M : ℚ) / X₂) =
      (((c : ℚ) + 1) ^ 2 * b ^ 2 * (((X : ℚ) + 1) ^ d) ^ 2 * (X₂ + 4 * M)) /
        (c ^ 2 * a ^ 2 * ((X : ℚ) ^ d) ^ 2 * X₂) := by
    push_cast
    field_simp
  rw [hkey, lt_div_iff₀ (by positivity)] at hsq
  linarith

/-- The one large comparison, on numbers of about 110,000 digits. -/
theorem final_ineqC : 9 * 132257 ^ 2 * 18677387639328032348 ^ 2 * (1000001 ^ 9063) ^ 2 *
    (1999999 + 4 * 351483) ≤
    16 * 132256 ^ 2 * 18446744073709551616 ^ 2 * (1000000 ^ 9063) ^ 2 * 1999999 := by
  decide +kernel

end RestrainedSixteen

open RestrainedSeven RestrainedEight RestrainedEleven RestrainedSixteen

/-- **Restrained family: `ω(N) ≥ 360549`.** With the hypotheses of `restrained_not_dvd_of_lt`,
the landed sieve certificate counted (at most 9063 leftovers up to `10 ^ 6`) and the packing of
the prime factors above `10 ^ 6` force at least 360547 prime factors other than 3 and `q`.
Conditional family result checked by the kernel; no novelty is claimed. -/
theorem restrained_omega_ge_tail {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    360549 ≤ ω N := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have h3 := restrained_three_dvd h hq hodd hr hrq hsq
  have hq3 : q ≠ 3 := by have := F.mod12; omega
  have hqN : q ∈ N.primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hq, ?_, h.ne_zero⟩
    obtain ⟨k, hk⟩ := hodd
    exact Nat.dvd_of_factorization_pos (by omega)
  have hlt := card_gt_of_certC (B := 132257) (c := 132256) (X := 1000000) (X₁ := 1000001)
    (X₂ := 1999999) (d := 9063) (M := 351483) h h3
    hqN hq3 rfl (by norm_num) (restrained_le_of_ne_three h hq hodd hr hrq hsq hqN hq3)
    (fun t ht => by
      obtain ⟨htq, ht'⟩ := Finset.mem_erase.mp ht
      obtain ⟨ht3, htN⟩ := Finset.mem_erase.mp ht'
      exact ⟨good_of_mem h hq hodd hr hrq hsq htN htq ht3,
        restrained_le_of_ne_three h hq hodd hr hrq hsq htN ht3⟩)
    (by norm_num) rfl (by norm_num) certC_all (by norm_num) final_ineqC
  have h3m : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, h.ne_zero⟩
  have hqm : q ∈ N.primeFactors.erase 3 := Finset.mem_erase.mpr ⟨hq3, hqN⟩
  rw [Finset.card_erase_of_mem hqm, Finset.card_erase_of_mem h3m] at hlt
  rw [cardDistinctFactors_eq_card_primeFactors]
  omega

/-- **Restrained family: `v_3(N) ≥ 180274`.** From `ω(N) ≥ 360549`, `ω(N) ≤ 2 v_3(N) + 3`
(`restrained_omega_le`) and the evenness of `v_3(N)` (`restrained_exception_eq_three`).
Ochem and Zelinsky (arXiv 2607.19746) state a far larger bound for this exponent, obtained by a
long computation; it is not proved here.
Conditional family result checked by the kernel; no novelty is claimed. -/
theorem restrained_tail_le_three {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    180274 ≤ N.factorization 3 := by
  have h1 := restrained_omega_ge_tail h hq hodd hr hrq hsq
  have h2 := restrained_omega_le h hq hodd hr hrq hsq
  obtain ⟨-, -, ⟨k, hk⟩, -⟩ := restrained_exception_eq_three h hq hodd hr hrq hsq
  omega

/-- **Restrained family: `Ω(N) ≥ 901369`.** From `ω(N) ≥ 360549`, `v_3(N) ≥ 180274` and
`2 ω(N) + v_3(N) ≤ Ω(N) + 3`.
Conditional family result checked by the kernel; no novelty is claimed. -/
theorem restrained_Omega_ge_tail {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    901369 ≤ Ω N := by
  have h1 := restrained_omega_ge_tail h hq hodd hr hrq hsq
  have h2 := restrained_tail_le_three h hq hodd hr hrq hsq
  have h3 := two_mul_card_add_factorization_three_le h
  omega

end OddPerfect

#print axioms OddPerfect.RestrainedSixteen.certC_trans
#print axioms OddPerfect.RestrainedSixteen.certC_mono
#print axioms OddPerfect.RestrainedSixteen.runLimb_soundC
#print axioms OddPerfect.RestrainedSixteen.runL_soundC
#print axioms OddPerfect.RestrainedSixteen.blockC
#print axioms OddPerfect.RestrainedSixteen.zb132257
#print axioms OddPerfect.RestrainedSixteen.zb148641
#print axioms OddPerfect.RestrainedSixteen.zb165025
#print axioms OddPerfect.RestrainedSixteen.zb181409
#print axioms OddPerfect.RestrainedSixteen.zb197793
#print axioms OddPerfect.RestrainedSixteen.zb214177
#print axioms OddPerfect.RestrainedSixteen.zb230561
#print axioms OddPerfect.RestrainedSixteen.zb246945
#print axioms OddPerfect.RestrainedSixteen.zb263329
#print axioms OddPerfect.RestrainedSixteen.zb279713
#print axioms OddPerfect.RestrainedSixteen.zb296097
#print axioms OddPerfect.RestrainedSixteen.zb312481
#print axioms OddPerfect.RestrainedSixteen.zb328865
#print axioms OddPerfect.RestrainedSixteen.zb345249
#print axioms OddPerfect.RestrainedSixteen.zb361633
#print axioms OddPerfect.RestrainedSixteen.zb378017
#print axioms OddPerfect.RestrainedSixteen.zb394401
#print axioms OddPerfect.RestrainedSixteen.zb410785
#print axioms OddPerfect.RestrainedSixteen.zb427169
#print axioms OddPerfect.RestrainedSixteen.zb443553
#print axioms OddPerfect.RestrainedSixteen.zb459937
#print axioms OddPerfect.RestrainedSixteen.zb476321
#print axioms OddPerfect.RestrainedSixteen.zb492705
#print axioms OddPerfect.RestrainedSixteen.zb509089
#print axioms OddPerfect.RestrainedSixteen.zb525473
#print axioms OddPerfect.RestrainedSixteen.zb541857
#print axioms OddPerfect.RestrainedSixteen.zb558241
#print axioms OddPerfect.RestrainedSixteen.zb574625
#print axioms OddPerfect.RestrainedSixteen.zb591009
#print axioms OddPerfect.RestrainedSixteen.zb607393
#print axioms OddPerfect.RestrainedSixteen.zb623777
#print axioms OddPerfect.RestrainedSixteen.zb640161
#print axioms OddPerfect.RestrainedSixteen.zb656545
#print axioms OddPerfect.RestrainedSixteen.zb672929
#print axioms OddPerfect.RestrainedSixteen.zb689313
#print axioms OddPerfect.RestrainedSixteen.zb705697
#print axioms OddPerfect.RestrainedSixteen.zb722081
#print axioms OddPerfect.RestrainedSixteen.zb738465
#print axioms OddPerfect.RestrainedSixteen.zb754849
#print axioms OddPerfect.RestrainedSixteen.zb771233
#print axioms OddPerfect.RestrainedSixteen.zb787617
#print axioms OddPerfect.RestrainedSixteen.zb804001
#print axioms OddPerfect.RestrainedSixteen.zb820385
#print axioms OddPerfect.RestrainedSixteen.zb836769
#print axioms OddPerfect.RestrainedSixteen.zb853153
#print axioms OddPerfect.RestrainedSixteen.zb869537
#print axioms OddPerfect.RestrainedSixteen.zb885921
#print axioms OddPerfect.RestrainedSixteen.zb902305
#print axioms OddPerfect.RestrainedSixteen.zb918689
#print axioms OddPerfect.RestrainedSixteen.zb935073
#print axioms OddPerfect.RestrainedSixteen.zb951457
#print axioms OddPerfect.RestrainedSixteen.zb967841
#print axioms OddPerfect.RestrainedSixteen.zb984225
#print axioms OddPerfect.RestrainedSixteen.certC_all
#print axioms OddPerfect.RestrainedSixteen.step_le
#print axioms OddPerfect.RestrainedSixteen.prod_sq_le
#print axioms OddPerfect.RestrainedSixteen.card_gt_of_certC
#print axioms OddPerfect.RestrainedSixteen.final_ineqC
#print axioms OddPerfect.restrained_omega_ge_tail
#print axioms OddPerfect.restrained_tail_le_three
#print axioms OddPerfect.restrained_Omega_ge_tail
