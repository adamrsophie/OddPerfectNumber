import OddPerfect.Network
import OddPerfect.Valuation
import OddPerfect.Zsigmondy
import OddPerfect.SpecialPrime
import OddPerfect.Spoof

/-!
# Order data at the nodes of the divisor sum network

Every node of the network of an odd perfect number is a prime, so for an edge `p → r`
(that is, `r ∣ σ(p ^ e_p)`) the multiplicative order `d` of `p` modulo `r` divides both
`e_p + 1` and `r - 1` (Fermat's little theorem at the receiver). This file extracts the
consequences of that fact which depend on the relative size of `p` and `r`.

* `three_le_orderOf_of_lt`: an upward edge `p → r` with `p < r` (both odd primes) has order
  `d ≥ 3`, so `e_p ≥ 2` and `r ≡ 1 (mod d)`. Orders `1` and `2` would force `r ∣ p - 1` or
  `r ∣ p + 1`, impossible for `r > p` odd.
* `odd_orderOf_of_even`: a sender with even exponent has odd order at every receiver; so if
  `r` is a prime with `r - 1` a power of two and `p ≠ r` is a prime sender with even exponent
  `e_p` and `r ∣ σ(p ^ e_p)`, then `p ≡ 1 (mod r)` and `r ∣ e_p + 1`
  (`eq_one_of_fermat_receiver`). The even exponent hypothesis is needed: `17 ∣ σ(67) = 68`
  while `67 ≡ -1 (mod 17)`, with exponent 1.
* `exists_upward_edge_into_largest`: the largest prime factor `P` of an odd perfect number
  receives an edge from a smaller prime `p` with order `d ≥ 3`, `d ∣ e_p + 1`, `P ≡ 1 (mod d)`
  and `e_p ≥ 2`. In particular the special component with exponent `1` never feeds `P`.
* `two_mul_factorization_add_five_le_largest`: if the largest prime factor `P` has even
  exponent `e`, then `2 e + 5 ≤ P` (one better than the general row bound `2 e + 3`).
* `special_receiver_dichotomy`: an ordinary sender into the special prime `q` either
  satisfies `p ≡ 1 (mod q)` and `q ∣ e_p + 1`, or has odd order `d ≥ 3` with `4 d ∣ q - 1`.

The companion `not_maxReceives_descartes` shows that Descartes' spoof
`3² 7² 11² 13² 22021` violates the formal version `MaxReceives` of the largest prime
statement, while `maxReceives_of_oddPerfect` proves it for every odd perfect number. The
violation has a plain cause: `22021 = 19² · 61` is not a node, and its prime factors `19`
and `61` arrive from three different components, so no single component feeds `22021`.
None of this is a global obstruction: the network `3⁴ 7² 11² 19² 127` (Voight's spoof with
`-127` replaced by `127`) is closed (every odd prime factor of every `σ(p ^ e_p)` is a node)
and satisfies the upward edge, Fermat receiver and largest prime statements at every edge.
It fails Euler's form (`127 ≡ 3 (mod 4)` has odd exponent) and conservation: `2` receives
`7` instead of `1`, `3` receives `2` instead of `4`, and `7` receives `1` instead of `2`.
The per edge lemmas here hold for any pair of primes; `MaxReceives` needs only an in edge at
the maximum (conservation); only the `2 e + 5` bound needs the Zsigmondy witness to be a node.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## Order of an edge between primes -/

/-- For primes `p ≠ r` with `r ∣ σ(p ^ e)`, the order of `p` modulo `r` divides `e + 1`,
unless it is `1`, in which case `r ∣ e + 1`. Restated from `dvd_sigma_prime_pow_iff`. -/
private theorem orderOf_dvd_or {p r e : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    (hd : r ∣ σ 1 (p ^ e)) :
    (orderOf (p : ZMod r) = 1 ∧ r ∣ e + 1) ∨ (orderOf (p : ZMod r) ≠ 1 ∧
      orderOf (p : ZMod r) ∣ e + 1) := by
  have h := (dvd_sigma_prime_pow_iff hp hr hpr).mp hd
  split_ifs at h with h1
  · exact Or.inl ⟨h1, h⟩
  · exact Or.inr ⟨h1, h⟩

/-- Upward edges have order at least three. If `p < r` are primes, `p` odd, and
`r ∣ σ(p ^ e)`, then the order `d` of `p` modulo `r` satisfies `3 ≤ d`, `d ∣ e + 1` and
`r % d = 1`. -/
theorem three_le_orderOf_of_lt {p r e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime)
    (hpr : p < r) (hd : r ∣ σ 1 (p ^ e)) :
    3 ≤ orderOf (p : ZMod r) ∧ orderOf (p : ZMod r) ∣ e + 1 ∧
      r % orderOf (p : ZMod r) = 1 := by
  have : Fact r.Prime := ⟨hr⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp0 : (p : ZMod r) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact absurd (Nat.le_of_dvd hp.pos h) (by omega)
  have hp1 : (p : ZMod r) ≠ 1 := by
    intro h
    have h' : ((p - 1 : ℕ) : ZMod r) = 0 := by
      rw [Nat.cast_sub (by omega), h, Nat.cast_one, sub_self]
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact absurd (Nat.le_of_dvd (by omega) h') (by omega)
  have hord1 : orderOf (p : ZMod r) ≠ 1 := fun h => hp1 (orderOf_eq_one_iff.mp h)
  have hdvd := ZMod.orderOf_dvd_card_sub_one hp0
  have hord0 : orderOf (p : ZMod r) ≠ 0 := by
    intro h
    rw [h, zero_dvd_iff] at hdvd
    have := hr.two_le
    omega
  have hord2 : orderOf (p : ZMod r) ≠ 2 := by
    intro h
    have hsq : (p : ZMod r) * (p : ZMod r) = 1 := by
      rw [← sq, ← h]; exact pow_orderOf_eq_one _
    rcases mul_self_eq_one_iff.mp hsq with h1 | h1
    · exact hp1 h1
    · have h' : ((p + 1 : ℕ) : ZMod r) = 0 := by
        push_cast; rw [h1]; ring
      rw [ZMod.natCast_eq_zero_iff] at h'
      have hle := Nat.le_of_dvd (by omega) h'
      have hre : r = p + 1 := by omega
      have hpo : Odd p := hp.odd_of_ne_two hp2
      have hreven : Even r := by rw [hre]; exact hpo.add_one
      have := (Nat.Prime.even_iff hr).mp hreven
      omega
  have hsucc : orderOf (p : ZMod r) ∣ e + 1 := by
    rcases orderOf_dvd_or hp hr (by omega) hd with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd h1 hord1
    · exact h2
  refine ⟨by omega, hsucc, ?_⟩
  have := (Nat.modEq_iff_dvd' hr.one_lt.le).mpr hdvd
  rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega : 1 < orderOf (p : ZMod r))] at this
  exact this.symm

/-- A divisor `m` of `r - 1` with `m` and `r` odd: then `2 m ∣ r - 1`. -/
private theorem two_mul_dvd_pred {m r : ℕ} (hm : Odd m) (hr : Odd r) (h : m ∣ r - 1) :
    2 * m ∣ r - 1 := by
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_two_left.mpr hm) ?_ h
  obtain ⟨k, rfl⟩ := hr
  exact ⟨k, by omega⟩

/-- From `m ∣ r - 1`, `1 < m` and `1 ≤ r`, get `r % m = 1`. -/
private theorem mod_eq_one_of_dvd_pred {m r : ℕ} (hm : 1 < m) (hr : 1 ≤ r) (h : m ∣ r - 1) :
    r % m = 1 := by
  have := (Nat.modEq_iff_dvd' hr).mpr h
  rw [Nat.ModEq, Nat.mod_eq_of_lt hm] at this
  exact this.symm

/-- A sender with even exponent has odd order at every receiver: if `p ≠ r` are primes,
`e` is even and `r ∣ σ(p ^ e)`, then the order of `p` modulo `r` is odd. -/
theorem odd_orderOf_of_even {p r e : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    (he : Even e) (hd : r ∣ σ 1 (p ^ e)) : Odd (orderOf (p : ZMod r)) := by
  rcases orderOf_dvd_or hp hr hpr hd with ⟨h1, -⟩ | ⟨-, h2⟩
  · rw [h1]; exact odd_one
  · exact (he.add_one).of_dvd_nat h2

/-- Fermat type receivers. If `r` is a prime with `r - 1 = 2 ^ j`, `p ≠ r` is a prime, `e`
is even and `r ∣ σ(p ^ e)`, then `p ≡ 1 (mod r)` and `r ∣ e + 1`. The hypothesis that `e` is
even is needed: `17 ∣ σ(67) = 68` while `67 ≡ -1 (mod 17)`, with exponent 1. -/
theorem eq_one_of_fermat_receiver {p r e j : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hrj : r - 1 = 2 ^ j) (hpr : p ≠ r) (he : Even e) (hd : r ∣ σ 1 (p ^ e)) :
    (p : ZMod r) = 1 ∧ r ∣ e + 1 := by
  have : Fact r.Prime := ⟨hr⟩
  have hp0 : (p : ZMod r) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hpr ((Nat.prime_dvd_prime_iff_eq hr hp).mp h).symm
  have hodd := odd_orderOf_of_even hp hr hpr he hd
  have hdvd := ZMod.orderOf_dvd_card_sub_one hp0
  rw [hrj] at hdvd
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have h1 : orderOf (p : ZMod r) = 1 := by
    rcases i with _ | i
    · simpa using hi
    · rw [hi, pow_succ] at hodd
      exact absurd hodd (Nat.not_odd_iff_even.mpr (even_two.mul_left _))
  refine ⟨orderOf_eq_one_iff.mp h1, ?_⟩
  rcases orderOf_dvd_or hp hr hpr hd with ⟨-, h2⟩ | ⟨h2, -⟩
  · exact h2
  · exact absurd h1 h2

/-! ## Upward edges in an odd perfect number -/

variable {N : ℕ}

private theorem ne_two_of_mem (h : OddPerfect N) {p : ℕ} (hp : p ∈ N.primeFactors) : p ≠ 2 := by
  rintro rfl
  exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hp)

/-- Upward edges of an odd perfect number. If `p < r` are prime factors of `N` and
`r ∣ σ(p ^ e_p)`, then the order `d` of `p` modulo `r` satisfies `3 ≤ d`, `d ∣ e_p + 1`,
`r ≡ 1 (mod d)`, and `e_p ≥ 2`. -/
theorem upward_edge (h : OddPerfect N) {p r : ℕ} (hp : p ∈ N.primeFactors)
    (hr : r ∈ N.primeFactors) (hpr : p < r) (hd : r ∣ σ 1 (p ^ N.factorization p)) :
    3 ≤ orderOf (p : ZMod r) ∧ orderOf (p : ZMod r) ∣ N.factorization p + 1 ∧
      r % orderOf (p : ZMod r) = 1 ∧ 2 ≤ N.factorization p := by
  obtain ⟨h3, hdv, hmod⟩ := three_le_orderOf_of_lt (Nat.prime_of_mem_primeFactors hp)
    (ne_two_of_mem h hp) (Nat.prime_of_mem_primeFactors hr) hpr hd
  refine ⟨h3, hdv, hmod, ?_⟩
  have := Nat.le_of_dvd (Nat.succ_pos _) hdv
  omega

/-- Upward edges from an ordinary prime (even exponent): the order `d` is odd and
`r ≡ 1 (mod 2 d)`, so `2 d + 1 ≤ r`. -/
theorem upward_edge_of_even (h : OddPerfect N) {p r : ℕ} (hp : p ∈ N.primeFactors)
    (hr : r ∈ N.primeFactors) (hpr : p < r) (hd : r ∣ σ 1 (p ^ N.factorization p))
    (he : Even (N.factorization p)) :
    Odd (orderOf (p : ZMod r)) ∧ r % (2 * orderOf (p : ZMod r)) = 1 ∧
      2 * orderOf (p : ZMod r) + 1 ≤ r := by
  have hrp := Nat.prime_of_mem_primeFactors hr
  have : Fact r.Prime := ⟨hrp⟩
  obtain ⟨h3, hdv, -, -⟩ := upward_edge h hp hr hpr hd
  have hodd : Odd (orderOf (p : ZMod r)) := (he.add_one).of_dvd_nat hdv
  have hp0 : (p : ZMod r) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hh
    exact absurd (Nat.le_of_dvd (Nat.prime_of_mem_primeFactors hp).pos hh) (by omega)
  have hr1 := two_mul_dvd_pred hodd (h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr))
    (ZMod.orderOf_dvd_card_sub_one hp0)
  have hle := Nat.le_of_dvd (by have := hrp.two_le; omega) hr1
  exact ⟨hodd, mod_eq_one_of_dvd_pred (by omega) hrp.one_lt.le hr1, by omega⟩

/-- The largest prime factor `P` of an odd perfect number receives an upward edge: some
prime factor `p < P` has `P ∣ σ(p ^ e_p)`, and the order `d` of `p` modulo `P` satisfies
`3 ≤ d`, `d ∣ e_p + 1`, `P ≡ 1 (mod d)`; in particular `e_p ≥ 2`. -/
theorem exists_upward_edge_into_largest (h : OddPerfect N) {P : ℕ} (hP : P ∈ N.primeFactors)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P) :
    ∃ p ∈ N.primeFactors, p < P ∧ P ∣ σ 1 (p ^ N.factorization p) ∧
      3 ≤ orderOf (p : ZMod P) ∧ orderOf (p : ZMod P) ∣ N.factorization p + 1 ∧
      P % orderOf (p : ZMod P) = 1 ∧ 2 ≤ N.factorization p := by
  obtain ⟨p, hpP, hp, -, hd⟩ := exists_sigmaEdge_into h.perfect hP (ne_two_of_mem h hP)
  have hlt : p < P := lt_of_le_of_ne (hmax p hp) hpP
  exact ⟨p, hp, hlt, hd, upward_edge h hp hP hlt hd⟩

/-- No prime with exponent one (that is, the special prime with exponent `1`) feeds the
largest prime factor: every component `p` with `P ∣ σ(p ^ e_p)` has `e_p ≥ 2`. -/
theorem two_le_factorization_of_dvd_largest (h : OddPerfect N) {P p : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hp : p ∈ N.primeFactors)
    (hd : P ∣ σ 1 (p ^ N.factorization p)) : 2 ≤ N.factorization p := by
  have hpP : p ≠ P := by
    rintro rfl
    have := (prime_dvd_sigma_prime_pow (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hp) hd).1
    exact this rfl
  exact (upward_edge h hp hP (lt_of_le_of_ne (hmax p hp) hpP) hd).2.2.2

/-- Row bound at the top. If the largest prime factor `P` of an odd perfect number has even
exponent `e`, then `2 e + 5 ≤ P`. The primitive prime of order `e + 1` for `P` is a prime
factor `r ≡ 1 (mod 2 (e + 1))` with `r < P`. -/
theorem two_mul_factorization_add_five_le_largest (h : OddPerfect N) {P : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (he : Even (N.factorization P)) : 2 * N.factorization P + 5 ≤ P := by
  have he1 : 1 ≤ N.factorization P := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hP)
  have he2 : 2 ≤ N.factorization P := by
    obtain ⟨j, hj⟩ := he; omega
  obtain ⟨r, hr, ho, hmod⟩ := exists_primeFactor_modEq_one h hP (d := N.factorization P + 1)
    (by omega) dvd_rfl
  have hrp := Nat.prime_of_mem_primeFactors hr
  have : Fact r.Prime := ⟨hrp⟩
  have hrP : r ≠ P := by
    rintro rfl
    rw [ZMod.natCast_self, orderOf_zero] at ho
    omega
  have hlt : r < P := lt_of_le_of_ne (hmax r hr) hrP
  have hdv : N.factorization P + 1 ∣ r - 1 := by
    refine (Nat.modEq_iff_dvd' hrp.one_lt.le).mp ?_
    change 1 % _ = r % _
    rw [hmod, Nat.mod_eq_of_lt (by omega)]
  have h2 := two_mul_dvd_pred (he.add_one)
    (h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr)) hdv
  have hle := Nat.le_of_dvd (by have := hrp.two_le; omega) h2
  have hPodd : P % 2 = 1 := Nat.odd_iff.mp (h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hP))
  omega

/-- Receivers of the special prime. Let `q` be the special prime (odd exponent) of an odd
perfect number and `p ≠ q` a prime factor with `q ∣ σ(p ^ e_p)`. Then either `p ≡ 1 (mod q)`
and `q ∣ e_p + 1`, or the order `d` of `p` modulo `q` is odd, `d ≥ 3`, `d ∣ e_p + 1` and
`q ≡ 1 (mod 4 d)`. -/
theorem special_receiver_dichotomy (h : OddPerfect N) {q p : ℕ} (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hp : p ∈ N.primeFactors) (hpq : p ≠ q)
    (hd : q ∣ σ 1 (p ^ N.factorization p)) :
    ((p : ZMod q) = 1 ∧ q ∣ N.factorization p + 1) ∨
      (3 ≤ orderOf (p : ZMod q) ∧ Odd (orderOf (p : ZMod q)) ∧
        orderOf (p : ZMod q) ∣ N.factorization p + 1 ∧ q % (4 * orderOf (p : ZMod q)) = 1) := by
  have : Fact q.Prime := ⟨hq⟩
  have hpp := Nat.prime_of_mem_primeFactors hp
  have he := even_factorization_of_ne h hq hodd hpp hpq
  have hoddd := odd_orderOf_of_even hpp hq hpq he hd
  rcases orderOf_dvd_or hpp hq hpq hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨orderOf_eq_one_iff.mp h1, h2⟩
  · right
    have hp0 : (p : ZMod q) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun hh => hpq ((Nat.prime_dvd_prime_iff_eq hq hpp).mp hh).symm
    have hdq := ZMod.orderOf_dvd_card_sub_one hp0
    have h0 : orderOf (p : ZMod q) ≠ 0 := fun h0 => by
      rw [h0, zero_dvd_iff] at h2; omega
    have h3 : 3 ≤ orderOf (p : ZMod q) := by
      obtain ⟨k, hk⟩ := hoddd; omega
    have h4 : q % 4 = 1 := (special_mod_four h hq hodd).1
    have h4d : 4 ∣ q - 1 := ⟨q / 4, by omega⟩
    have hcop : Nat.Coprime 4 (orderOf (p : ZMod q)) := by
      have := Nat.coprime_two_left.mpr hoddd
      exact Nat.Coprime.pow_left 2 this
    have hdiv := hcop.mul_dvd_of_dvd_of_dvd h4d hdq
    exact ⟨h3, hoddd, h2, mod_eq_one_of_dvd_pred (by omega) hq.one_lt.le hdiv⟩

/-! ## A formal statement violated by Descartes' spoof -/

/-- Formal version of `exists_upward_edge_into_largest` for a finite set `S` of bases with
exponents `e`, phrased with `Spoof.geom` and powers so that it is decidable: the largest base
`P` divides `geom b (e b)` for some smaller base `b` with `e b ≥ 2`, and some divisor
`d ≥ 3` of `e b + 1` has `P ≡ 1 (mod d)` and `b ^ d ≡ 1 (mod P)`. It asks only for
`b ^ d ≡ 1 (mod P)`, not that `d` be the exact multiplicative order of `b` modulo `P`; so it is
implied by, and weaker than, the exact order statement of `exists_upward_edge_into_largest`.
The implication from genuine odd perfect numbers (`maxReceives_of_oddPerfect`) stays valid. -/
def MaxReceives (S : Finset ℕ) (e : ℕ → ℕ) : Prop :=
  ∀ P ∈ S, (∀ r ∈ S, r ≤ P) → ∃ b ∈ S, b < P ∧ P ∣ Spoof.geom b (e b) ∧ 2 ≤ e b ∧
    ∃ d ∈ (e b + 1).divisors, 3 ≤ d ∧ P % d = 1 ∧ b ^ d % P = 1

/-- Every odd perfect number satisfies `MaxReceives` on its prime factors and exponents. -/
theorem maxReceives_of_oddPerfect (h : OddPerfect N) :
    MaxReceives N.primeFactors N.factorization := by
  intro P hP hmax
  obtain ⟨p, hp, hlt, hd, h3, hdv, hmod, he2⟩ := exists_upward_edge_into_largest h hP hmax
  have : Fact P.Prime := ⟨Nat.prime_of_mem_primeFactors hP⟩
  refine ⟨p, hp, hlt, ?_, he2, orderOf (p : ZMod P),
    Nat.mem_divisors.mpr ⟨hdv, Nat.succ_ne_zero _⟩, h3, hmod, ?_⟩
  · rwa [← Spoof.sigma_prime_pow (Nat.prime_of_mem_primeFactors hp)]
  · have h1 : ((p ^ orderOf (p : ZMod P) : ℕ) : ZMod P) = ((1 : ℕ) : ZMod P) := by
      push_cast; exact pow_orderOf_eq_one _
    rw [ZMod.natCast_eq_natCast_iff'] at h1
    rw [h1, Nat.mod_eq_of_lt (Nat.prime_of_mem_primeFactors hP).one_lt]

/-- Exponents of Descartes' spoof `3² 7² 11² 13² 22021`. -/
def descartesExp (b : ℕ) : ℕ := if b = 22021 then 1 else 2

/-- Descartes' spoof violates `MaxReceives`: no base divides `geom b (e b)` by `22021`.
The cause is that `22021 = 19² · 61` is not prime, and the formal divisor sums deliver its
factors `19, 19, 61` from three different components (`7², 11², 13²`). -/
theorem not_maxReceives_descartes : ¬ MaxReceives {3, 7, 11, 13, 22021} descartesExp := by
  intro hM
  obtain ⟨b, hb, -, hdiv, -⟩ := hM 22021 (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> revert hdiv <;> decide

/-- `descartesExp` and the Finset `{3, 7, 11, 13, 22021}` are exactly the data of
`Spoof.descartes`. -/
theorem descartes_data :
    Spoof.descartes.map Prod.fst = [3, 7, 11, 13, 22021] ∧
      ∀ x ∈ Spoof.descartes, descartesExp x.1 = x.2 := by
  decide

end OddPerfect

#print axioms OddPerfect.three_le_orderOf_of_lt
#print axioms OddPerfect.odd_orderOf_of_even
#print axioms OddPerfect.eq_one_of_fermat_receiver
#print axioms OddPerfect.upward_edge
#print axioms OddPerfect.upward_edge_of_even
#print axioms OddPerfect.exists_upward_edge_into_largest
#print axioms OddPerfect.two_le_factorization_of_dvd_largest
#print axioms OddPerfect.two_mul_factorization_add_five_le_largest
#print axioms OddPerfect.special_receiver_dichotomy
#print axioms OddPerfect.maxReceives_of_oddPerfect
#print axioms OddPerfect.not_maxReceives_descartes
#print axioms OddPerfect.descartes_data
