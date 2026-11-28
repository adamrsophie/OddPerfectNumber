import OddPerfect.EulerIndexExponentBound
import OddPerfect.ReceiverSqueeze
import OddPerfect.UpperBound

/-!
# The number of prime factors through the Euler index and the index primes

Let `N = q ^ a * m ^ 2` be an odd perfect number in Euler's form, with `q` the special prime and
`q ∤ m`, and let `J = eulerIndex q a m`, `k = ω(J)`.

* If, for every prime factor `r` of `J`, every prime factor of `e_r + 1` is at most `T`, then
  `ω(N) ≤ 1 + k T ^ k + k / 2`, and so `N < 2 ^ (4 ^ (1 + k T ^ k + k / 2))`.
* In the prime power index family (every `e_p + 1` with `p ≠ q` a power of one prime `l`),
  `ω(N) ≤ 1 + k B ^ k + k / 2` with `B = 16 (k + 1) ^ 2 4 ^ (k + 1)`.

These bound the number of prime factors of `N` by quantities of the Euler index; `ω(J)` and the
exponents stay unbounded, and no odd perfect number is excluded. Restricted result; no published
source was checked; novelty not verified. The odd perfect number conjecture remains open.
-/

namespace OddPerfect

/-- For every odd perfect number `N = q ^ a * m ^ 2` with special prime `q` and `q ∤ m`: if, for
every prime factor `r` of the Euler index `J`, every prime factor of `e_r + 1` is at most `T`,
then `ω(N) ≤ 1 + ω(J) T ^ ω(J) + ω(J) / 2`. A bound through quantities of the Euler index only;
nothing is excluded. Restricted result; no published source was checked; novelty not
verified. -/
theorem card_primeFactors_le_of_eulerIndex_index_primes {N q a m T : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m)
    (hT : ∀ r ∈ (eulerIndex q a m).primeFactors,
      ∀ d ∈ (N.factorization r + 1).primeFactors, d ≤ T) :
    N.primeFactors.card ≤
      1 + (eulerIndex q a m).primeFactors.card * T ^ (eulerIndex q a m).primeFactors.card +
        (eulerIndex q a m).primeFactors.card / 2 := by
  have hB : ∀ r ∈ (eulerIndex q a m).primeFactors,
      N.factorization r ≤ T ^ (eulerIndex q a m).primeFactors.card - 1 := fun r hr => by
    have := factorization_succ_le_pow_of_mem_eulerIndex h hq hN hqm hr (hT r hr)
    omega
  have hA := card_primeFactors_le_of_eulerIndex_exponents h hq hN hqm le_rfl hB
  have hpos : 1 ≤ T ^ (eulerIndex q a m).primeFactors.card := by
    have h3 := three_le_eulerIndex h hq hN hqm
    obtain ⟨r, hr⟩ := Nat.nonempty_primeFactors.mpr (show 1 < eulerIndex q a m by omega)
    have := factorization_succ_le_pow_of_mem_eulerIndex h hq hN hqm hr (hT r hr)
    omega
  rwa [Nat.sub_add_cancel hpos] at hA

/-- For every odd perfect number `N = q ^ a * m ^ 2` with special prime `q` and `q ∤ m`: if, for
every prime factor `r` of the Euler index `J`, every prime factor of `e_r + 1` is at most `T`,
then `N < 2 ^ (4 ^ (1 + ω(J) T ^ ω(J) + ω(J) / 2))`, by the bound `N < 2 ^ (4 ^ ω(N))`. A size
bound through quantities of the Euler index only; nothing is excluded. Restricted result; no
published source was checked; novelty not verified. -/
theorem lt_two_pow_four_pow_of_eulerIndex_index_primes {N q a m T : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m)
    (hT : ∀ r ∈ (eulerIndex q a m).primeFactors,
      ∀ d ∈ (N.factorization r + 1).primeFactors, d ≤ T) :
    N < 2 ^ (4 ^ (1 + (eulerIndex q a m).primeFactors.card *
        T ^ (eulerIndex q a m).primeFactors.card +
      (eulerIndex q a m).primeFactors.card / 2)) := by
  have hC := card_primeFactors_le_of_eulerIndex_index_primes h hq hN hqm hT
  exact (lt_two_pow_four_pow h).trans_le
    (Nat.pow_le_pow_right two_pos (Nat.pow_le_pow_right (by norm_num) hC))

/-- Prime power index family: let `N = q ^ a * m ^ 2` be an odd perfect number with special
prime `q`, `q ∤ m`, and `l` a prime with `e_p + 1` a positive power of `l` for every prime
factor `p ≠ q`. With `k = ω(J)` for the Euler index `J` and `B = 16 (k + 1) ^ 2 4 ^ (k + 1)`,
`ω(N) ≤ 1 + k B ^ k + k / 2`: an explicit bound through `k` alone. The family is not excluded.
Restricted result; no published source was checked; novelty not verified. -/
theorem card_primeFactors_le_of_prime_pow_index_eulerIndex {N q a m l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (hl : l.Prime)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, 1 ≤ γ ∧ N.factorization p + 1 = l ^ γ) :
    N.primeFactors.card ≤
      1 + (eulerIndex q a m).primeFactors.card *
          (16 * ((eulerIndex q a m).primeFactors.card + 1) ^ 2 *
            4 ^ ((eulerIndex q a m).primeFactors.card + 1)) ^
              (eulerIndex q a m).primeFactors.card +
        (eulerIndex q a m).primeFactors.card / 2 := by
  have hcomp : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1 := fun p hp hpq => by
    obtain ⟨γ, hγ, he⟩ := hidx p hp hpq
    rw [he]
    exact dvd_pow_self l (by omega)
  have hle := index_le_of_common_index_eulerIndex h hq hN hqm hl hcomp
  apply card_primeFactors_le_of_eulerIndex_index_primes h hq hN hqm
  intro r hr d hd
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hrp := Nat.prime_of_mem_primeFactors hr
  have hrm : r ∣ m := hrp.dvd_of_dvd_pow
    ((Nat.dvd_of_mem_primeFactors hr).trans (eulerIndex_dvd_sq h hq hN hqm))
  have hrq : r ≠ q := by rintro rfl; exact hqm hrm
  have hrN : r ∈ N.primeFactors := Nat.mem_primeFactors.mpr
    ⟨hrp, hrm.trans (hN ▸ (dvd_pow_self m two_ne_zero).mul_left _), h.ne_zero⟩
  obtain ⟨γ, hγ, he⟩ := hidx r hrN hrq
  rw [he, Nat.primeFactors_prime_pow (by omega) hl, Finset.mem_singleton] at hd
  rw [hd]
  exact hle

end OddPerfect

#print axioms OddPerfect.card_primeFactors_le_of_eulerIndex_index_primes
#print axioms OddPerfect.lt_two_pow_four_pow_of_eulerIndex_index_primes
#print axioms OddPerfect.card_primeFactors_le_of_prime_pow_index_eulerIndex
