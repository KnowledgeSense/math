import Fan.InvariantUniquenessIdentification

namespace Fan

/-- Exact positive finite coefficient formula for the actual fan inverse-Z invariant. -/
theorem inverseZ_coefficient_formula (n k : ℕ) (hn : 0<n) (hk : k≤n) :
    ((inverseZ n).coeff k : ℝ)=2^(n-1)*
      ∑ r∈Finset.range (min k (n-k)+1),
        ballotWeight n r*delannoy (1/2) (k-r) (n-k-r) := by
  rw [inverseZ_coeff_eq_fanCoefficient n k hn,fanCoefficient_formula n k hn hk]

theorem inverseZ_coefficient_pos (n k : ℕ) (hn : 0<n) (hk : k≤n) :
    0<(inverseZ n).coeff k := by
  have h := fanCoefficient_pos n k hn hk
  rw [← inverseZ_coeff_eq_fanCoefficient n k hn] at h
  exact_mod_cast h

theorem inverseZ_coefficient_symm (n k : ℕ) (hn : 0<n) (hk : k≤n) :
    (inverseZ n).coeff (n-k)=(inverseZ n).coeff k := by
  have h := fanCoefficient_symm n k hn hk
  rw [← inverseZ_coeff_eq_fanCoefficient n (n-k) hn,← inverseZ_coeff_eq_fanCoefficient n k hn] at h
  exact_mod_cast h

theorem inverseZ_coefficient_strict (n k : ℕ) (hn : 0<n) (hk : 1≤k) (hkn : k<n) :
    (inverseZ n).coeff (k-1)*(inverseZ n).coeff (k+1)<(inverseZ n).coeff k^2 := by
  have h := fanCoefficient_strict_log_concave n k hn hk hkn
  rw [← inverseZ_coeff_eq_fanCoefficient n (k-1) hn,← inverseZ_coeff_eq_fanCoefficient n (k+1) hn,
    ← inverseZ_coeff_eq_fanCoefficient n k hn] at h
  exact_mod_cast h

theorem inverseZ_coefficient_above (n k : ℕ) (hn : 0<n) (hk : n<k) :
    (inverseZ n).coeff k=0 := by
  have h := fanCoefficient_outside n k hn hk
  rw [← inverseZ_coeff_eq_fanCoefficient n k hn] at h
  exact_mod_cast h

theorem inverseZ_degree (n : ℕ) (hn : 0<n) : (inverseZ n).natDegree=n := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      (fun k hk => inverseZ_coefficient_above n k hn hk)
  · exact ne_of_gt (inverseZ_coefficient_pos n n hn le_rfl)

theorem inverseZ_one : inverseZ 1=1+Polynomial.X := by
  apply Polynomial.ext
  intro k
  cases k with
  | zero =>
    have h := inverseZ_coeff_eq_fanCoefficient 1 0 (by omega)
    rw [fanCoefficient_rank_one_zero] at h
    have hi : (inverseZ 1).coeff 0=1 := by exact_mod_cast h
    simpa using hi
  | succ k =>
    cases k with
    | zero =>
      have h := inverseZ_coeff_eq_fanCoefficient 1 1 (by omega)
      rw [fanCoefficient_rank_one_one] at h
      have hi : (inverseZ 1).coeff 1=1 := by exact_mod_cast h
      simpa [Polynomial.coeff_one] using hi
    | succ k =>
      rw [inverseZ_coefficient_above 1 _ (by omega) (by omega)]
      simp [Polynomial.coeff_one,Polynomial.coeff_X]

/-- Every fan, with an apex and a path on n vertices, has positive symmetric
inverse-Z coefficients and strict log-concavity at every internal index. -/
theorem fan_inverseZ_main (n : ℕ) (hn : 1≤n) :
    (inverseZ n).natDegree=n ∧
    (∀ k≤n,0<(inverseZ n).coeff k) ∧
    (∀ k≤n,(inverseZ n).coeff (n-k)=(inverseZ n).coeff k) ∧
    (∀ k,1≤k → k<n →
      (inverseZ n).coeff (k-1)*(inverseZ n).coeff (k+1)<(inverseZ n).coeff k^2) := by
  exact ⟨inverseZ_degree n hn,fun k hk => inverseZ_coefficient_pos n k hn hk,
    fun k hk => inverseZ_coefficient_symm n k hn hk,
    fun k hk hkn => inverseZ_coefficient_strict n k hn hk hkn⟩

end Fan
