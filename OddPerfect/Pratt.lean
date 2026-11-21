import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.List.Prime
import Mathlib.Tactic.Ring

/-!
# Pratt primality certificates checked by kernel reduction

A certificate is a flat list of entries `(p, a, fs)` in dependency order. The entry
claims that `fs` is the list of prime factors of `p - 1` with multiplicity and that
`a` has order `p - 1` modulo `p`. Every element of `fs` must either occur as the
prime of an earlier entry or pass trial division. `check` verifies all entries with
fast modular exponentiation, and `check_sound` turns an accepted certificate into
primality via `lucas_primality`. Since all functions use structural recursion,
`decide +kernel` evaluates them.
-/

namespace OddPerfect.Pratt

/-- Binary modular exponentiation with fuel: returns `acc * b ^ e % n` when `e < fuel`. -/
def powModAux (n : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc % n
  | fuel + 1, b, e, acc =>
    if e = 0 then acc % n
    else powModAux n fuel (b * b % n) (e / 2) (if e % 2 = 1 then acc * b % n else acc)

/-- Fast modular exponentiation `a ^ b % n`, evaluable by the kernel. -/
def powMod (a b n : ℕ) : ℕ := powModAux n (b + 1) a b 1

/-- Correctness of `powModAux` under sufficient fuel. -/
theorem powModAux_eq (n : ℕ) : ∀ fuel b e acc, e < fuel →
    powModAux n fuel b e acc = acc * b ^ e % n
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, b, e, acc, h => by
    unfold powModAux
    split_ifs with h0 h1
    · simp [h0]
    · rw [powModAux_eq n fuel _ _ _ (by omega)]
      obtain ⟨k, rfl⟩ : ∃ k, e = 2 * k + 1 := ⟨e / 2, by omega⟩
      have hk : (2 * k + 1) / 2 = k := by omega
      rw [hk]
      refine ((Nat.mod_modEq _ _).mul ((Nat.mod_modEq _ _).pow _)).trans ?_
      ring_nf
      rfl
    · rw [powModAux_eq n fuel _ _ _ (by omega)]
      obtain ⟨k, rfl⟩ : ∃ k, e = 2 * k := ⟨e / 2, by omega⟩
      have hk : 2 * k / 2 = k := by omega
      rw [hk]
      refine ((Nat.ModEq.refl acc).mul ((Nat.mod_modEq _ _).pow _)).trans ?_
      ring_nf
      rfl

/-- Correctness of `powMod`. -/
theorem powMod_eq (a b n : ℕ) : powMod a b n = a ^ b % n := by
  rw [powMod, powModAux_eq n _ _ _ _ (Nat.lt_succ_self b), one_mul]

/-- Primality by trial division over all `2 ≤ d < q`; meant for small `q`. -/
def trialPrime (q : ℕ) : Bool :=
  2 ≤ q && (List.range' 2 (q - 2)).all fun d => q % d != 0

/-- Soundness of trial division. -/
theorem trialPrime_sound {q : ℕ} (h : trialPrime q = true) : q.Prime := by
  simp only [trialPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range'_1, bne_iff_ne, ne_eq] at h
  refine Nat.prime_def_lt.2 ⟨h.1, fun m hm hd => ?_⟩
  rcases Nat.lt_or_ge m 2 with h2 | h2
  · interval_cases m
    · simp at hd; omega
    · rfl
  · exact absurd (Nat.mod_eq_zero_of_dvd hd) (h.2 m ⟨h2, by omega⟩)

/-- Check one entry `(p, a, fs)` given a list `known` of already certified primes. -/
def checkEntry (known : List ℕ) (p a : ℕ) (fs : List ℕ) : Bool :=
  fs.prod == p - 1 && fs.all (fun q => known.contains q || trialPrime q) &&
    powMod a (p - 1) p == 1 && fs.all (fun q => powMod a ((p - 1) / q) p != 1)

/-- Check a flat certificate, accumulating the certified primes. -/
def checkAux : List ℕ → List (ℕ × ℕ × List ℕ) → Bool
  | _, [] => true
  | known, (p, a, fs) :: rest => checkEntry known p a fs && checkAux (p :: known) rest

/-- Check a flat Pratt certificate: a list of entries `(p, a, prime factors of p - 1)`. -/
def check (c : List (ℕ × ℕ × List ℕ)) : Bool := checkAux [] c

/-- Check a certificate and that it certifies `p`. -/
def checkPrime (p : ℕ) (c : List (ℕ × ℕ × List ℕ)) : Bool :=
  check c && (c.map Prod.fst).contains p

/-- Soundness of one entry, given that every known number is prime. -/
theorem checkEntry_sound {known : List ℕ} {p a : ℕ} {fs : List ℕ}
    (hk : ∀ q ∈ known, q.Prime) (h : checkEntry known p a fs = true) : p.Prime := by
  simp only [checkEntry, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    List.contains_iff_mem, bne_iff_ne, ne_eq, powMod_eq] at h
  obtain ⟨⟨⟨hprod, hfs⟩, hpow⟩, hne⟩ := h
  have hfsP : ∀ q ∈ fs, q.Prime := fun q hq =>
    (hfs q hq).elim (hk q) trialPrime_sound
  have hp1 : p ≠ 1 := by rintro rfl; simp at hpow
  have h1 : 1 % p = 1 := by
    rcases Nat.lt_or_ge p 2 with h | h
    · interval_cases p <;> simp_all
    · exact Nat.mod_eq_of_lt h
  have key : ∀ k, ((a : ZMod p) ^ k = 1 ↔ a ^ k % p = 1) := fun k => by
    rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff', h1]
  refine lucas_primality p (a : ZMod p) ((key _).2 hpow) fun q hq hd => ?_
  rw [← hprod] at hd
  obtain ⟨r, hr, hqr⟩ := (Prime.dvd_prod_iff hq.prime).1 hd
  rw [(Nat.prime_dvd_prime_iff_eq hq (hfsP r hr)).1 hqr, Ne, key]
  exact hne r hr

/-- Soundness of `checkAux`, given that every known number is prime. -/
theorem checkAux_sound : ∀ (known : List ℕ) (c : List (ℕ × ℕ × List ℕ)),
    (∀ q ∈ known, q.Prime) → checkAux known c = true → ∀ e ∈ c, e.1.Prime
  | _, [], _, _, e, he => absurd he List.not_mem_nil
  | known, (p, a, fs) :: rest, hk, h, e, he => by
    simp only [checkAux, Bool.and_eq_true] at h
    have hp := checkEntry_sound hk h.1
    rcases List.mem_cons.1 he with rfl | he
    · exact hp
    · exact checkAux_sound (p :: known) rest
        (fun q hq => (List.mem_cons.1 hq).elim (fun e => e ▸ hp) (hk q)) h.2 e he

/-- Soundness: every prime listed in an accepted certificate is prime. -/
theorem check_sound {c : List (ℕ × ℕ × List ℕ)} (h : check c = true) :
    ∀ e ∈ c, e.1.Prime :=
  checkAux_sound [] c (by simp) h

/-- Soundness of `checkPrime`. -/
theorem prime_of_checkPrime {p : ℕ} {c : List (ℕ × ℕ × List ℕ)}
    (h : checkPrime p c = true) : p.Prime := by
  simp only [checkPrime, Bool.and_eq_true, List.contains_iff_mem, List.mem_map] at h
  obtain ⟨hc, e, he, rfl⟩ := h
  exact check_sound hc e he

/-! ## Demonstrations -/

/-- `3169` is prime. -/
theorem prime_3169 : Nat.Prime 3169 :=
  prime_of_checkPrime (c := [(3169, 7, [2, 2, 2, 2, 2, 3, 3, 11])]) (by decide +kernel)

/-- `2221` is prime. -/
theorem prime_2221 : Nat.Prime 2221 :=
  prime_of_checkPrime (c := [(2221, 2, [2, 2, 3, 5, 37])]) (by decide +kernel)

/-- `1093` is prime. -/
theorem prime_1093 : Nat.Prime 1093 :=
  prime_of_checkPrime (c := [(1093, 5, [2, 2, 3, 7, 13])]) (by decide +kernel)

/-- `9701563` is prime. -/
theorem prime_9701563 : Nat.Prime 9701563 :=
  prime_of_checkPrime (c := [(509, 2, [2, 2, 127]), (1019, 2, [2, 509]), (2039, 7, [2, 1019]),
    (9701563, 5, [2, 3, 13, 61, 2039])]) (by decide +kernel)

/-- The certificate for the witness of `OPNSquarefull.witness_prime`. -/
def witnessCert : List (ℕ × ℕ × List ℕ) :=
  [(6299, 2, [2, 47, 67]),
   (509, 2, [2, 2, 127]),
   (1019, 2, [2, 509]),
   (2039, 7, [2, 1019]),
   (9701563, 5, [2, 3, 13, 61, 2039]),
   (27779, 2, [2, 17, 19, 43]),
   (1738423, 5, [2, 3, 3, 3, 3, 3, 7, 7, 73]),
   (966563189, 2, [2, 2, 139, 1738423]),
   (666928600411, 13, [2, 3, 5, 23, 966563189]),
   (12004714807399, 6, [2, 3, 3, 666928600411]),
   (192750846182877882539, 2, [2, 17, 17, 27779, 12004714807399]),
   (47116128896261596331524418282573, 2, [2, 2, 6299, 9701563, 192750846182877882539])]

/-- The witness of `OPNSquarefull.witness_prime` is prime. -/
theorem prime_witness : Nat.Prime 47116128896261596331524418282573 :=
  prime_of_checkPrime (c := witnessCert) (by decide +kernel)

end OddPerfect.Pratt

#print axioms OddPerfect.Pratt.powModAux_eq
#print axioms OddPerfect.Pratt.powMod_eq
#print axioms OddPerfect.Pratt.trialPrime_sound
#print axioms OddPerfect.Pratt.checkEntry_sound
#print axioms OddPerfect.Pratt.checkAux_sound
#print axioms OddPerfect.Pratt.check_sound
#print axioms OddPerfect.Pratt.prime_of_checkPrime
#print axioms OddPerfect.Pratt.prime_3169
#print axioms OddPerfect.Pratt.prime_2221
#print axioms OddPerfect.Pratt.prime_1093
#print axioms OddPerfect.Pratt.prime_9701563
#print axioms OddPerfect.Pratt.prime_witness
