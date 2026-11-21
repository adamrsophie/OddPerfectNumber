import OddPerfect.Certificate

/-!
# Three free seed exclusions by certificate

Kernel checked exclusions of exponent patterns for odd perfect numbers `N` with `¬ 3 ∣ N`.
Each certificate starts from the state `[notDvd 3, exact 5 2, exact 11 2, exact 29 2, exact x 2]`
and is accepted by `check` through `decide +kernel`; `check_sound` turns acceptance into a proof.
The certificates were produced and independently rechecked by an untrusted Python generator.
-/

namespace OddPerfect.Cert

/-- Certificate for the seeds `5, 11, 29, 17` with exponent 2 and `¬ 3 ∣ N`. σ(5^2) = 31, σ(11^2) = 7 * 19, σ(29^2) = 13 * 67, σ(17^2) = 307 force six primes, and the divisor `5^2 11^2 17^2 29^2 7 13 19 31 67 307` is already abundant. -/
def certThreeFree17 : Cert :=
  .force 5 2 2 31 <|
    .force 11 2 2 7 <|
    .force 11 2 2 19 <|
    .force 29 2 2 13 <|
    .force 29 2 2 67 <|
    .force 17 2 2 307 <|
    .abundant [(5, 2), (7, 1), (11, 2), (13, 1), (17, 2), (19, 1), (29, 2), (31, 1), (67, 1), (307, 1)]

/-- No odd perfect number with `¬ 3 ∣ N` has exponent exactly 2 at each of 5, 11, 17, 29. -/
theorem exclude_three_free_5_11_17_29 {N : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N)
    (h5 : N.factorization 5 = 2) (h11 : N.factorization 11 = 2)
    (h17 : N.factorization 17 = 2) (h29 : N.factorization 29 = 2) : False :=
  check_sound (s := [.notDvd 3, .exact 5 2, .exact 11 2, .exact 29 2, .exact 17 2])
    (c := certThreeFree17) (by decide +kernel) N h
    (by simp [State.Holds, Fact.Holds, h3, h5, h11, h17, h29])

/-- No odd perfect number has exponent exactly 2 at each of 5, 11, 17, 29. -/
theorem exclude_exact_squares_5_11_17_29 {N : ℕ} (h : OddPerfect N)
    (h5 : N.factorization 5 = 2) (h11 : N.factorization 11 = 2)
    (hx : N.factorization 17 = 2) (h29 : N.factorization 29 = 2) : False :=
  check_sound (s := [.exact 5 2, .exact 11 2, .exact 29 2, .exact 17 2])
    (c := certThreeFree17) (by decide +kernel) N h
    (by simp [State.Holds, Fact.Holds, h5, h11, hx, h29])

/-- Certificate for the seeds `5, 11, 29, 23` with exponent 2 and `¬ 3 ∣ N`. σ(23^2) = 7 * 79 forces 79 next to the primes forced by 5, 11, 29; the divisor with all forced primes to the first power is abundant. -/
def certThreeFree23 : Cert :=
  .force 5 2 2 31 <|
    .force 11 2 2 7 <|
    .force 11 2 2 19 <|
    .force 29 2 2 13 <|
    .force 29 2 2 67 <|
    .force 23 2 2 79 <|
    .abundant [(5, 2), (7, 1), (11, 2), (13, 1), (19, 1), (23, 2), (29, 2), (31, 1), (67, 1), (79, 1)]

/-- No odd perfect number with `¬ 3 ∣ N` has exponent exactly 2 at each of 5, 11, 23, 29. -/
theorem exclude_three_free_5_11_23_29 {N : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N)
    (h5 : N.factorization 5 = 2) (h11 : N.factorization 11 = 2)
    (h23 : N.factorization 23 = 2) (h29 : N.factorization 29 = 2) : False :=
  check_sound (s := [.notDvd 3, .exact 5 2, .exact 11 2, .exact 29 2, .exact 23 2])
    (c := certThreeFree23) (by decide +kernel) N h
    (by simp [State.Holds, Fact.Holds, h3, h5, h11, h23, h29])

/-- No odd perfect number has exponent exactly 2 at each of 5, 11, 23, 29. -/
theorem exclude_exact_squares_5_11_23_29 {N : ℕ} (h : OddPerfect N)
    (h5 : N.factorization 5 = 2) (h11 : N.factorization 11 = 2)
    (hx : N.factorization 23 = 2) (h29 : N.factorization 29 = 2) : False :=
  check_sound (s := [.exact 5 2, .exact 11 2, .exact 29 2, .exact 23 2])
    (c := certThreeFree23) (by decide +kernel) N h
    (by simp [State.Holds, Fact.Holds, h5, h11, hx, h29])

/-- Certificate for the seeds `5, 11, 29, 41` with exponent 2 and `¬ 3 ∣ N`. σ(41^2) = 1723 is prime. The exponent of 7 is odd (closed by parity, since 7 % 4 = 3), or 2 (then 3 ∣ σ(7^2) = 57 gives 3 ∣ N), or at least 4; in the last case the recorded divisor is abundant. -/
def certThreeFree41 : Cert :=
  .force 5 2 2 31 <|
    .force 11 2 2 7 <|
    .force 11 2 2 19 <|
    .force 29 2 2 13 <|
    .force 29 2 2 67 <|
    .force 41 2 2 1723 <|
    .split 7 1
      (.paritySpecial 7 1)
      (.split 7 2
          (.force 7 2 2 3 <|
            .notDvd 3 1)
          (.split 7 3
              (.paritySpecial 7 3)
              (.abundant [(5, 2), (7, 4), (11, 2), (13, 1), (19, 1), (29, 2), (31, 1), (41, 2), (67, 1), (1723, 1)])))

/-- No odd perfect number with `¬ 3 ∣ N` has exponent exactly 2 at each of 5, 11, 41, 29. -/
theorem exclude_three_free_5_11_41_29 {N : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N)
    (h5 : N.factorization 5 = 2) (h11 : N.factorization 11 = 2)
    (h41 : N.factorization 41 = 2) (h29 : N.factorization 29 = 2) : False :=
  check_sound (s := [.notDvd 3, .exact 5 2, .exact 11 2, .exact 29 2, .exact 41 2])
    (c := certThreeFree41) (by decide +kernel) N h
    (by simp [State.Holds, Fact.Holds, h3, h5, h11, h41, h29])

/-- Certificate for the seeds `5, 11, 29, 47` with exponent 2 and `¬ 3 ∣ N`. σ(47^2) = 37 * 61 forces 37 and 61; the divisor with all forced primes to the first power is abundant. -/
def certThreeFree47 : Cert :=
  .force 5 2 2 31 <|
    .force 11 2 2 7 <|
    .force 11 2 2 19 <|
    .force 29 2 2 13 <|
    .force 29 2 2 67 <|
    .force 47 2 2 37 <|
    .force 47 2 2 61 <|
    .abundant [(5, 2), (7, 1), (11, 2), (13, 1), (19, 1), (29, 2), (31, 1), (37, 1), (47, 2), (61, 1), (67, 1)]

/-- No odd perfect number with `¬ 3 ∣ N` has exponent exactly 2 at each of 5, 11, 47, 29. -/
theorem exclude_three_free_5_11_47_29 {N : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N)
    (h5 : N.factorization 5 = 2) (h11 : N.factorization 11 = 2)
    (h47 : N.factorization 47 = 2) (h29 : N.factorization 29 = 2) : False :=
  check_sound (s := [.notDvd 3, .exact 5 2, .exact 11 2, .exact 29 2, .exact 47 2])
    (c := certThreeFree47) (by decide +kernel) N h
    (by simp [State.Holds, Fact.Holds, h3, h5, h11, h47, h29])

/-- No odd perfect number has exponent exactly 2 at each of 5, 11, 47, 29. -/
theorem exclude_exact_squares_5_11_47_29 {N : ℕ} (h : OddPerfect N)
    (h5 : N.factorization 5 = 2) (h11 : N.factorization 11 = 2)
    (hx : N.factorization 47 = 2) (h29 : N.factorization 29 = 2) : False :=
  check_sound (s := [.exact 5 2, .exact 11 2, .exact 29 2, .exact 47 2])
    (c := certThreeFree47) (by decide +kernel) N h
    (by simp [State.Holds, Fact.Holds, h5, h11, hx, h29])

/-- Certificate for the seeds `5, 11, 29, 53` with exponent 2 and `¬ 3 ∣ N`. σ(53^2) = 7 * 409. The exponents of 7 and of 19 are each odd (closed by parity), 2 (then 3 ∣ N, since 7 and 19 are 1 mod 3), or at least 4; in the last case the recorded divisor is abundant. -/
def certThreeFree53 : Cert :=
  .force 5 2 2 31 <|
    .force 11 2 2 7 <|
    .force 11 2 2 19 <|
    .force 29 2 2 13 <|
    .force 29 2 2 67 <|
    .force 53 2 2 409 <|
    .split 7 1
      (.paritySpecial 7 1)
      (.split 7 2
          (.force 7 2 2 3 <|
            .notDvd 3 1)
          (.split 7 3
              (.paritySpecial 7 3)
              (.split 19 1
                  (.paritySpecial 19 1)
                  (.split 19 2
                      (.force 19 2 2 3 <|
                        .notDvd 3 1)
                      (.split 19 3
                          (.paritySpecial 19 3)
                          (.abundant [(5, 2), (7, 4), (11, 2), (13, 1), (19, 4), (29, 2), (31, 1), (53, 2), (67, 1), (409, 1)]))))))

/-- No odd perfect number with `¬ 3 ∣ N` has exponent exactly 2 at each of 5, 11, 53, 29. -/
theorem exclude_three_free_5_11_53_29 {N : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N)
    (h5 : N.factorization 5 = 2) (h11 : N.factorization 11 = 2)
    (h53 : N.factorization 53 = 2) (h29 : N.factorization 29 = 2) : False :=
  check_sound (s := [.notDvd 3, .exact 5 2, .exact 11 2, .exact 29 2, .exact 53 2])
    (c := certThreeFree53) (by decide +kernel) N h
    (by simp [State.Holds, Fact.Holds, h3, h5, h11, h53, h29])

end OddPerfect.Cert

#print axioms OddPerfect.Cert.exclude_three_free_5_11_17_29
#print axioms OddPerfect.Cert.exclude_three_free_5_11_23_29
#print axioms OddPerfect.Cert.exclude_three_free_5_11_41_29
#print axioms OddPerfect.Cert.exclude_three_free_5_11_47_29
#print axioms OddPerfect.Cert.exclude_three_free_5_11_53_29
#print axioms OddPerfect.Cert.exclude_exact_squares_5_11_17_29
#print axioms OddPerfect.Cert.exclude_exact_squares_5_11_23_29
#print axioms OddPerfect.Cert.exclude_exact_squares_5_11_47_29
