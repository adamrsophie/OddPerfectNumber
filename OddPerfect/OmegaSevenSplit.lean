import OddPerfect.OmegaSevenEngine

/-!
# Exponent splits of search states

Two ways to cut a search state of `OmegaSixSearch.Holds` into smaller kernel checks of the
engine `OmegaSevenEngine.run`, used by `OddPerfect/OmegaSevenRoots*.lean`:
* `closed_of_split`: at an inexact entry `(p, k)`, either the exponent of `p` is exactly `k`,
  or it is at least the next exponent allowed by Euler's theorem.
* `closed_of_cover`: the next unlisted prime lies in an interval, and the interval is covered
  by pieces. A piece is one child state (`cover_one`) or a range of children checked by one
  kernel run (`ival_sound`); joined by `cover_join`.
-/

namespace OddPerfect.OmegaSevenSplit

open OmegaSixSearch (Ent Holds nextValid valid kmin bounds lowB minB enum_sound)
open OmegaSevenEngine (pickP LadGood ladT ladT_good run closed_of_run)
open OmegaSevenSearch (Closed)

variable {N : ℕ}

private theorem valid_fact (h : OddPerfect N) {p : ℕ} (hp : p.Prime) :
    valid p (N.factorization p) = true := by
  obtain ⟨q, -, -, hq4, hqe, hev⟩ := exists_special_prime h
  simp only [valid, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]
  by_cases hpq : p = q
  · subst hpq; exact Or.inr ⟨hq4, hqe⟩
  · exact Or.inl (Nat.even_iff.mp (hev p hp hpq))

private theorem nextValid_le {p k f : ℕ} (hk : k < f) (hf : valid p f = true) :
    nextValid p k ≤ f := by
  unfold nextValid
  split_ifs with h
  · omega
  · rcases Nat.lt_or_ge (k + 1) f with h1 | h1
    · omega
    · exact absurd (show f = k + 1 by omega ▸ hf) h

/-- Replacing an entry by one with the same prime that also holds keeps the state. -/
private theorem holds_repl {pre post : List Ent} {j m : ℕ} {e x : Ent}
    (H : Holds N (pre ++ e :: post) j m) (hx : x.Holds N) (hxp : x.p = e.p) :
    Holds N (pre ++ x :: post) j m := by
  obtain ⟨h, hnd, hent, hcard, hbig⟩ := H
  have hmap : (pre ++ x :: post).map Ent.p = (pre ++ e :: post).map Ent.p := by
    simp [hxp]
  refine ⟨h, hmap ▸ hnd, ?_, by simpa using hcard, fun q hq hn => hbig q hq (hmap ▸ hn)⟩
  intro y hy
  simp only [List.mem_append, List.mem_cons] at hy
  rcases hy with hy | rfl | hy
  · exact hent y (by simp [hy])
  · exact hx
  · exact hent y (by simp [hy])

/-- An exponent split: a state with the inexact entry `(p, k)` is closed when the state with
the exact exponent `k` and the state with the inexact exponent `nextValid p k` are closed. -/
theorem closed_of_split {pre post : List Ent} {j m p k k' : ℕ} (hk : nextValid p k = k')
    (h1 : Closed (pre ++ ⟨p, k, true⟩ :: post) j m)
    (h2 : Closed (pre ++ ⟨p, k', false⟩ :: post) j m) :
    Closed (pre ++ ⟨p, k, false⟩ :: post) j m := by
  intro N H
  have he : (⟨p, k, false⟩ : Ent).Holds N := H.2.2.1 _ (by simp)
  obtain ⟨hpN, hkf, -⟩ := he
  rcases Nat.eq_or_lt_of_le hkf with hf | hf
  · exact h1 N (holds_repl H ⟨hpN, hkf, fun _ => hf.symm⟩ rfl)
  · have hv := valid_fact H.1 (Nat.prime_of_mem_primeFactors hpN)
    exact h2 N (holds_repl H ⟨hpN, hk ▸ nextValid_le hf hv, fun h => by simp at h⟩ rfl)

private theorem pickP_good {lad : List (ℕ × ℕ)} (hlad : LadGood lad) (lo : ℕ) :
    ∀ b : ℕ × ℕ, (∀ r : ℕ, r.Prime → r ∣ b.2 → r < lo) →
      ∀ r : ℕ, r.Prime → r ∣ (pickP lad lo b).2 → r < lo := by
  induction lad with
  | nil => intro b hb; exact hb
  | cons x t ih =>
    intro b hb
    show ∀ r : ℕ, r.Prime → r ∣ (cond (Nat.blt x.1 lo) (pickP t lo x) b).2 → r < lo
    cases hx : Nat.blt x.1 lo
    · exact hb
    · have hx' : x.1 < lo := by simpa using hx
      exact ih (fun y hy => hlad y (by simp [hy])) x
        (fun r hr hrd => lt_of_le_of_lt (hlad x (by simp) r hr hrd) hx')

/-- A prime filter: `q` is coprime to the ladder product of the primes below `q`. -/
def candR (q : ℕ) : Bool := Nat.beq (Nat.gcd q (pickP ladT q (0, 1)).2) 1

private theorem candR_of_prime {q : ℕ} (hq : q.Prime) : candR q = true := by
  unfold candR
  rw [Nat.beq_eq]
  by_contra hne
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
  have h1 : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp (hrd.trans (Nat.gcd_dvd_left _ _))
  have h2 := pickP_good ladT_good q (0, 1) (fun r hr hd => absurd (Nat.le_of_dvd one_pos hd)
    (by have := hr.two_le; omega)) r hr (hrd.trans (Nat.gcd_dvd_right _ _))
  omega

/-- One kernel run over the children `a, ..., a + n - 1` of the state `(l, j)`: each child is a
non prime or is closed by `run 60`. -/
def ivalR (l : List Ent) (j a n : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => ih && (!candR (a + i) ||
      run 60 (l ++ [⟨a + i, kmin (a + i), false⟩]) (j - 1) (a + i))) n

private theorem ival_aux {l : List Ent} {j a : ℕ} : ∀ n, ivalR l j a n = true →
    ∀ q, a ≤ q → q < a + n → Closed (l ++ [⟨q, kmin q, false⟩]) (j - 1) q := by
  intro n
  induction n with
  | zero => intro _ q h1 h2; omega
  | succ n ih =>
    intro h q h1 h2
    have h' : (ivalR l j a n && (!candR (a + n) ||
        run 60 (l ++ [⟨a + n, kmin (a + n), false⟩]) (j - 1) (a + n))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    rcases Nat.lt_or_ge q (a + n) with hq | hq
    · exact ih h'.1 q h1 hq
    · have hq' : q = a + n := by omega
      subst hq'
      rcases h'.2 with hc | hr
      · intro N H
        have he := H.2.2.1 ⟨a + n, kmin (a + n), false⟩ (by simp)
        have := candR_of_prime (Nat.prime_of_mem_primeFactors he.1)
        simp_all
      · exact closed_of_run hr

/-- A range of children closed by one kernel run. -/
theorem ival_sound {l : List Ent} {j a b : ℕ} (h : ivalR l j a (b - a) = true) :
    ∀ q, a ≤ q → q < b → Closed (l ++ [⟨q, kmin q, false⟩]) (j - 1) q :=
  fun q h1 h2 => ival_aux (b - a) h q h1 (by omega)

/-- A single closed child covers a range of length one. -/
theorem cover_one {P : ℕ → Prop} {a b : ℕ} (hb : a + 1 = b) (h : P a) :
    ∀ q, a ≤ q → q < b → P q := fun q h1 h2 => (show q = a by omega) ▸ h

/-- Two adjacent ranges cover their union. -/
theorem cover_join {P : ℕ → Prop} {a b c : ℕ} (h1 : ∀ q, a ≤ q → q < b → P q)
    (h2 : ∀ q, b ≤ q → q < c → P q) : ∀ q, a ≤ q → q < c → P q :=
  fun q ha hc => (Nat.lt_or_ge q b).elim (h1 q ha) (fun hb => h2 q hb hc)

/-- A state is closed when every child with next prime in a range around its window is closed. -/
theorem closed_of_cover {l : List Ent} {j m a c : ℕ} (hj : j ≠ 0) (hb : bounds l j m ≠ [])
    (ha : a ≤ lowB l j m) (hc : minB (bounds l j m) < c)
    (h : ∀ q, a ≤ q → q < c → Closed (l ++ [⟨q, kmin q, false⟩]) (j - 1) q) : Closed l j m := by
  intro N H
  obtain ⟨q, h1, h2, -, H'⟩ := enum_sound H hj hb
  exact h q (by omega) (by omega) N H'

end OddPerfect.OmegaSevenSplit

#print axioms OddPerfect.OmegaSevenSplit.closed_of_split
#print axioms OddPerfect.OmegaSevenSplit.ival_sound
#print axioms OddPerfect.OmegaSevenSplit.cover_one
#print axioms OddPerfect.OmegaSevenSplit.cover_join
#print axioms OddPerfect.OmegaSevenSplit.closed_of_cover
