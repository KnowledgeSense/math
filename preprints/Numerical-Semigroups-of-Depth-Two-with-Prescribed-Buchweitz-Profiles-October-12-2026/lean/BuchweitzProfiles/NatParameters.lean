import BuchweitzProfiles.Construction

namespace BuchweitzProfiles

/-- Natural-number quotients used to enumerate the large generators. -/
def natQuotient (N L : ℕ) (a : ℤ → ℤ) (n : ℕ) : ℕ :=
  (quotient N L a n).toNat

/-- Natural-number Euclidean remainders. -/
def natRemainder (N L : ℕ) (a : ℤ → ℤ) (n : ℕ) : ℕ :=
  (remainder N L a n).toNat

@[simp] theorem natQuotient_one (N L : ℕ) (a : ℤ → ℤ) :
    natQuotient N L a 1 = (N+1)^2 + 2*L*(N+1) := by
  simp only [natQuotient, Nat.cast_one, quotient, ite_true]
  have he : largeCount (N : ℤ) L = (((N+1)^2 + 2*L*(N+1) : ℕ) : ℤ) := by
    simp [largeCount]
  rw [he, Int.toNat_natCast]

lemma natQuotient_cast {N L : ℕ} {a : ℤ → ℤ}
    (hN : 2 ≤ N) (hL : 1 ≤ L)
    (ha : ∀ k : ℤ, 1 ≤ k → k ≤ N → -(L:ℤ) ≤ a k ∧ a k ≤ L)
    {n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    (natQuotient N L a n : ℤ) = quotient N L a n := by
  unfold natQuotient
  apply Int.toNat_of_nonneg
  by_cases he : n = 1
  · subst n
    simp only [Nat.cast_one, quotient, ite_true]
    have := largeCount_gt N L (by exact_mod_cast hN) (by exact_mod_cast hL)
    omega
  · exact quotient_nonnegative N L a (by exact_mod_cast hN) (by exact_mod_cast hL)
      ha n (by omega) (by exact_mod_cast hnN)

lemma natQuotient_decreasing {N L : ℕ} {a : ℤ → ℤ}
    (hN : 2 ≤ N) (hL : 1 ≤ L) (ha1 : a 1 = 1)
    (ha : ∀ k : ℤ, 1 ≤ k → k ≤ N → -(L:ℤ) ≤ a k ∧ a k ≤ L)
    {i : ℕ} (hi : 1 ≤ i) (hiN : i < N) :
    natQuotient N L a (i+1) < natQuotient N L a i := by
  have hc1 := natQuotient_cast hN hL ha (show 1 ≤ i+1 by omega) (show i+1 ≤ N by omega)
  have hc0 := natQuotient_cast hN hL ha hi (show i ≤ N by omega)
  have hqi : quotient N L a (i+1) < quotient N L a i := by
    by_cases he : i = 1
    · subst i
      simpa using quotient_two_lt N L a (by exact_mod_cast hN) (by exact_mod_cast hL)
        ha1 (ha 2 (by omega) (by omega)).2
    · have hh := quotient_decreasing N L a (by exact_mod_cast hN) (by exact_mod_cast hL)
        ha ((i:ℤ)+1) (by omega) (by omega)
      simpa using hh
  push_cast at hc1
  omega

lemma natRemainder_cast (N L : ℕ) (a : ℤ → ℤ) {n : ℕ} (hn : 2 ≤ n) :
    (natRemainder N L a n : ℤ) = remainder N L a n := by
  exact Int.toNat_of_nonneg (remainder_bounds N L a n (by exact_mod_cast hn)).1

lemma natRemainder_bounds (N L : ℕ) (a : ℤ → ℤ) {n : ℕ} (hn : 2 ≤ n) :
    natRemainder N L a n ≤ 2*n-2 := by
  have h := (remainder_bounds N L a n (by exact_mod_cast hn)).2
  have hc := natRemainder_cast N L a hn
  omega

lemma nat_division_identity {N L : ℕ} {a : ℤ → ℤ}
    (hN : 2 ≤ N) (hL : 1 ≤ L)
    (ha : ∀ k : ℤ, 1 ≤ k → k ≤ N → -(L:ℤ) ≤ a k ∧ a k ≤ L)
    {n : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N) :
    (2*(n:ℤ)-1) * natQuotient N L a n + natRemainder N L a n =
      2 * ((N+1:ℕ)^2 + 2*L*(N+1) : ℕ) + 5 - 2*(n:ℤ) + a n - a ((n:ℤ)-1) := by
  rw [natQuotient_cast hN hL ha (by omega) hnN, natRemainder_cast N L a hn]
  convert division_identity N L a n (by exact_mod_cast hn) using 1
  simp [divisionNumerator, largeCount]

/-- The multiplicity prescribed by the main theorem. -/
def profileMultiplicity (N L : ℕ) : ℕ :=
  2*(N+1)*(4*(N+1)+3)*((N+1)^2+2*L*(N+1)+1)+1

/-- The genus prescribed by the main theorem. -/
def profileGenus (N L : ℕ) : ℕ :=
  8*(N+1)^4+(16*L+6)*(N+1)^3+(12*L+9)*(N+1)^2+(2*L+6)*(N+1)+4

lemma profileMultiplicity_eq (N L : ℕ) :
    profileMultiplicity N L =
      (2*(N+1))*(((2*(2*(N+1))+1)*((N+1)^2+2*L*(N+1)+1))+
        2*((N+1)^2+2*L*(N+1)+1))+1 := by
  unfold profileMultiplicity
  ring

lemma profileGenus_eq (N L : ℕ) :
    profileGenus N L = profileMultiplicity N L - 1 + ((N+1)^2+2*L*(N+1)+4) := by
  unfold profileGenus profileMultiplicity
  simp only [Nat.add_sub_cancel]
  ring

end BuchweitzProfiles
