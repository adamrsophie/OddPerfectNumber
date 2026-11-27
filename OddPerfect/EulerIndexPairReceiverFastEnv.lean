import OddPerfect.EulerIndexPairReceiverCore

/-!
# Two prime Euler index, branch `v = 1`: fast forms of the receiver certificate tests

Restricted result; no published source was checked; novelty not verified. The odd perfect
number conjecture remains open.

The certificate test `ReceiverSieve.packRow` evaluates `decide (Nat.Prime c)` for every number
`c` below the envelope maximum, which is slow in the kernel. This module gives tests with the
same value that reduce fast in the kernel:

* `primeFast`: primality by trial division by `d = 2, 3, ...` while `d * d ≤ n`, with fuel;
  `primeFast_iff : primeFast n = true ↔ n.Prime`.
* `envFast`: the envelope test with `primeFast`, where membership is tested against the
  given list `A` only (the primes added on the way are below the lower end); `envOK_of_envFast`.
* `pureFast`: the pure row test with `R_u(x) + u ≡ 0` replaced, for `x ≠ 1`, by the condition
  `x ^ u + u x ≡ 1 + u (mod p)`, which it implies; `pureOK_of_pureFast`.
* `absentFast`: the absent prime tests with `pureFast`; `absentOK_of_absentFast`.
* `keptFast`, `tailFast`: the kept row lengths and the tail test with `primeFast`;
  `tailOK_of_tailFast`.
-/

namespace OddPerfect
namespace ReceiverSieve

/-- Trial division of `n` by `d, d + 1, ...` while `d * d ≤ n`, with fuel `k`. -/
def primeFastAux : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | k + 1, n, d => decide (n < d * d) || (n % d != 0 && primeFastAux k n (d + 1))

/-- Bool primality by trial division (structural recursion, kernel friendly). -/
def primeFast (n : ℕ) : Bool := decide (2 ≤ n) && primeFastAux n n 2

theorem primeFastAux_sound {n : ℕ} :
    ∀ (k d : ℕ), primeFastAux k n d = true → ∀ m, d ≤ m → m * m ≤ n → ¬ m ∣ n := by
  intro k
  induction k with
  | zero => intro d h; simp [primeFastAux] at h
  | succ k ih =>
    intro d h m hdm hmm hmn
    simp only [primeFastAux, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
      bne_iff_ne, ne_eq] at h
    rcases h with h | ⟨hd, hk⟩
    · have : d * d ≤ m * m := Nat.mul_le_mul hdm hdm
      omega
    · rcases Nat.eq_or_lt_of_le hdm with rfl | hlt
      · exact hd (Nat.mod_eq_zero_of_dvd hmn)
      · exact ih (d + 1) hk m hlt hmm hmn

theorem primeFastAux_complete {n : ℕ} (hn : n.Prime) :
    ∀ (k d : ℕ), 2 ≤ d → d ≤ n + 1 → n + 2 ≤ k + d → primeFastAux k n d = true := by
  intro k
  induction k with
  | zero => intro d _ h1 h2; omega
  | succ k ih =>
    intro d hd2 hd1 hk
    simp only [primeFastAux, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
      bne_iff_ne, ne_eq]
    by_cases hlt : n < d * d
    · exact Or.inl hlt
    · right
      push Not at hlt
      have hdn : d < n := by nlinarith
      refine ⟨fun h0 => ?_, ih (d + 1) (by omega) (by omega) (by omega)⟩
      have := hn.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero h0)
      omega

theorem primeFast_iff (n : ℕ) : primeFast n = true ↔ n.Prime := by
  constructor
  · intro h
    simp only [primeFast, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h2, h⟩ := h
    by_contra hp
    have hn1 : n ≠ 1 := by omega
    have hsq := Nat.minFac_sq_le_self (by omega) hp
    have hmp := Nat.minFac_prime hn1
    have hsq' : Nat.minFac n * Nat.minFac n ≤ n := by rw [← pow_two]; exact hsq
    exact primeFastAux_sound n 2 h (Nat.minFac n) hmp.two_le hsq' (Nat.minFac_dvd n)
  · intro hn
    simp only [primeFast, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hn.two_le, primeFastAux_complete hn n 2 le_rfl (by have := hn.two_le; omega) le_rfl⟩

theorem primeFast_eq (n : ℕ) : primeFast n = decide n.Prime := by
  by_cases h : n.Prime
  · rw [decide_eq_true h]; exact (primeFast_iff n).mpr h
  · rw [decide_eq_false h]; exact Bool.eq_false_iff.mpr fun h' => h ((primeFast_iff n).mp h')

/-- The envelope test with `primeFast` in place of `decide (Nat.Prime _)`. Membership is
tested against the fixed list `A`; the primes of the envelope already passed lie below `lo`. -/
def envFast (A : List ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | lo, b :: L => primeFast b && decide (lo ≤ b) && decide (5 ≤ b) && !A.contains b &&
      (List.range' lo (b - lo)).all (fun c => !(primeFast c) || A.contains c) &&
      envFast A (b + 1) L

theorem envOK_of_envFast_aux (A : List ℕ) : ∀ (L B : List ℕ) (lo : ℕ), (∀ c ∈ B, c < lo) →
    envFast A lo L = true → envOK (B ++ A) lo L = true := by
  intro L
  induction L with
  | nil => intro B lo _ _; rfl
  | cons b L ih =>
    intro B lo hB h
    simp only [envFast, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨hp, hlo⟩, h5⟩, hA⟩, hgap⟩, hrest⟩ := h
    have hlo' : lo ≤ b := of_decide_eq_true hlo
    have hA2 : A.contains b = false := by
      revert hA; cases A.contains b <;> simp
    have e1 : decide (Nat.Prime b) = true := decide_eq_true ((primeFast_iff b).mp hp)
    have e4 : (B ++ A).contains b = false := by
      rw [Bool.eq_false_iff]
      intro hc
      rw [List.contains_iff_mem, List.mem_append] at hc
      rcases hc with hc | hc
      · have := hB b hc; omega
      · have h' := List.contains_iff_mem.mpr hc
        rw [hA2] at h'
        exact Bool.false_ne_true h'
    have e5 : (List.range' lo (b - lo)).all
        (fun c => !(decide (Nat.Prime c)) || (B ++ A).contains c) = true := by
      rw [List.all_eq_true] at hgap ⊢
      intro c hc
      have hc' := hgap c hc
      rw [primeFast_eq] at hc'
      cases hd : decide (Nat.Prime c)
      · rfl
      · rw [hd] at hc'
        simp only [Bool.not_true, Bool.false_or] at hc' ⊢
        rw [List.contains_iff_mem] at hc' ⊢
        exact List.mem_append_right B hc'
    have e6 : envOK (b :: (B ++ A)) (b + 1) L = true := by
      have := ih (b :: B) (b + 1) (fun c hc => by
        rcases List.mem_cons.mp hc with rfl | hc
        · omega
        · have := hB c hc; omega) hrest
      exact this
    simp only [envOK, e1, e4, e5, e6, hlo, h5, Bool.not_false, Bool.and_true]

theorem envOK_of_envFast {A : List ℕ} {lo : ℕ} {L : List ℕ} (h : envFast A lo L = true) :
    envOK A lo L = true :=
  envOK_of_envFast_aux A L [] lo (fun _ hc => absurd hc List.not_mem_nil) h

theorem gsum_succ' (n x : ℕ) : gsum (n + 1) x = gsum n x * x + 1 := by
  induction n with
  | zero => show 0 + x ^ 0 = 0 * x + 1; simp
  | succ n ih =>
    have e2 : gsum (n + 1) x = gsum n x + x ^ n := rfl
    have ih' : gsum n x + x ^ n = gsum n x * x + 1 := e2.symm.trans ih
    calc gsum (n + 1 + 1) x = (gsum n x + x ^ n) + x ^ (n + 1) := rfl
      _ = (gsum n x * x + 1) + x ^ (n + 1) := by rw [ih']
      _ = (gsum n x + x ^ n) * x + 1 := by ring
      _ = gsum (n + 1) x * x + 1 := rfl

/-- For `R_u(x) + u ≡ 0 (mod p)`: `x ^ u + u x ≡ 1 + u (mod p)`. -/
theorem pure_cond_of {u p x : ℕ} (h : (gsum u x + u) % p = 0) :
    (x ^ u + u * x) % p = (1 + u) % p := by
  have hid : gsum u x * x + 1 = gsum u x + x ^ u := by rw [← gsum_succ']; rfl
  have hg : ((gsum u x + u : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero h)
  have hid' := congrArg (Nat.cast : ℕ → ZMod p) hid
  push_cast at hg hid'
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
  push_cast
  linear_combination (-1 : ZMod p) * hid' + ((x : ZMod p) - 1) * hg

/-- The pure row test with `R_u(x) + u ≡ 0` replaced, for `x ≠ 1`, by
`x ^ u + u x ≡ 1 + u (mod p)`. -/
def pureFast (u p : ℕ) : Bool :=
  (List.range p).all fun x => !(x ^ oddPart (p - 1) % p == 1 &&
    ((x == 1 && (gsum u x + u) % p == 0) || (x != 1 && (x ^ u + u * x) % p == (1 + u) % p)))

theorem pureOK_of_pureFast {u p : ℕ} (h : pureFast u p = true) : pureOK u p = true := by
  unfold pureFast at h
  unfold pureOK
  rw [List.all_eq_true] at h ⊢
  intro x hx
  have hx' := h x hx
  by_cases ha : x ^ oddPart (p - 1) % p = 1
  · by_cases hb : (gsum u x + u) % p = 0
    · exfalso
      have hc : ((x == 1 && (gsum u x + u) % p == 0) ||
          (x != 1 && (x ^ u + u * x) % p == (1 + u) % p)) = true := by
        by_cases h1 : x = 1
        · subst h1; simp [hb]
        · simp [h1, pure_cond_of hb]
      rw [hc] at hx'
      simp [ha] at hx'
    · simp [hb]
  · simp [ha]

/-- The absent prime tests with `pureFast` in place of `pureOK`. -/
def absentFast (u : ℕ) (A : List (ℕ × List ℕ)) : Bool :=
  A.all fun pr => mixedOK u pr.1 pr.2 && pureFast u pr.1 && pr.1 != u && pr.1 % u != 1

theorem absentOK_of_absentFast {u : ℕ} {A : List (ℕ × List ℕ)} (h : absentFast u A = true) :
    absentOK u A = true := by
  unfold absentFast at h
  unfold absentOK
  rw [List.all_eq_true] at h ⊢
  intro pr hpr
  have h' := h pr hpr
  simp only [Bool.and_eq_true] at h' ⊢
  exact ⟨⟨⟨h'.1.1.1, pureOK_of_pureFast h'.1.1.2⟩, h'.1.2⟩, h'.2⟩

/-- The kept pure row lengths, with `primeFast` in place of `decide (Nat.Prime _)`. -/
def keptFast (u : ℕ) : List ℕ :=
  (List.range u).filter fun d => decide (3 ≤ d) && primeFast d && u % d == 1 &&
    !(d == 3 && (List.range u).all fun p => p % 2 == 0 || p * p + p + 1 != u) &&
    !(u % 4 == 3 && d % 4 == 1)

theorem keptFast_eq (u : ℕ) : keptFast u = keptLengths u := by
  simp only [keptFast, keptLengths, primeFast_eq]

/-- The tail test with `keptFast` in place of `keptLengths`. -/
def tailFast (u : ℕ) (L : List ℕ) : Bool :=
  L.length == u + 1 + (keptFast u).length &&
    decide (L.prod * ((keptFast u).map fun d => 5 ^ (d - 1) - 1).prod <
      2 * (L.map fun b => b - 1).prod * ((keptFast u).map fun d => 5 ^ (d - 1) - 2).prod)

theorem tailOK_of_tailFast {u : ℕ} {L : List ℕ} (h : tailFast u L = true) :
    tailOK u L = true := by
  unfold tailFast at h
  unfold tailOK
  rw [keptFast_eq] at h
  exact h

end ReceiverSieve
end OddPerfect

#print axioms OddPerfect.ReceiverSieve.primeFastAux_sound
#print axioms OddPerfect.ReceiverSieve.primeFastAux_complete
#print axioms OddPerfect.ReceiverSieve.primeFast_iff
#print axioms OddPerfect.ReceiverSieve.primeFast_eq
#print axioms OddPerfect.ReceiverSieve.envOK_of_envFast_aux
#print axioms OddPerfect.ReceiverSieve.envOK_of_envFast
#print axioms OddPerfect.ReceiverSieve.gsum_succ'
#print axioms OddPerfect.ReceiverSieve.pure_cond_of
#print axioms OddPerfect.ReceiverSieve.pureOK_of_pureFast
#print axioms OddPerfect.ReceiverSieve.absentOK_of_absentFast
#print axioms OddPerfect.ReceiverSieve.keptFast_eq
#print axioms OddPerfect.ReceiverSieve.tailOK_of_tailFast
