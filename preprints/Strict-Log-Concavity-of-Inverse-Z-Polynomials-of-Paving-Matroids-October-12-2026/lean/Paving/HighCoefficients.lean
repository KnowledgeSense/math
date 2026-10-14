import Paving.BooleanFlats

namespace Paving
open MatroidInverseZ Polynomial Finset
variable {α : Type*} [Fintype α]

noncomputable def flatSummand (M : Matroid α) (F : MatroidInverseZ.Flat M) : Polynomial ℤ :=
  C (((-1 : ℤ)^(rank M-MatroidInverseZ.flatRank M F))*IncidenceAlgebra.mu ℤ F ⊤) *
    X^(rank M-MatroidInverseZ.flatRank M F) *
      inverseKL (MatroidInverseZ.flatRank M) ⊥ F

theorem actual_inverseZ_sum (M : Matroid α) :
    matroidInverseZ M = ∑ F : MatroidInverseZ.Flat M, flatSummand M F := by
  classical
  change inverseZ (MatroidInverseZ.flatRank M) ⊥ ⊤ = _
  unfold inverseZ
  rw [show Icc (⊥ : MatroidInverseZ.Flat M) ⊤ = univ by ext F; simp]
  simp only [actualFlatRank_top]
  rfl

/-- Above the middle, only the Boolean lower intervals at complementary rank
contribute; the unknown top and hyperplane inverse-KL polynomials vanish. -/
theorem IsPaving.flatSummand_high_coeff {M : Matroid α} (hM : IsPaving M)
    (hr : 3 ≤ rank M) (F : MatroidInverseZ.Flat M) (j : ℕ)
    (hj : 2 ≤ j) (hjr : rank M < 2*j) (hjr' : j ≤ rank M) :
    (flatSummand M F).coeff j =
      if MatroidInverseZ.flatRank M F = rank M-j then
        (-1 : ℤ)^j * IncidenceAlgebra.mu ℤ F ⊤ else 0 := by
  classical
  have hle : MatroidInverseZ.flatRank M F ≤ rank M := subsetRank_le M F.1
  by_cases hlo : MatroidInverseZ.flatRank M F+1 < rank M
  · have hi := hM.flat_indep_of_rank F.2 hlo
    rw [flatSummand, actual_independentFlat_inverseKL F.1 hi F.2, mul_one,
      coeff_C_mul, coeff_X_pow]
    by_cases he : MatroidInverseZ.flatRank M F = rank M-j
    · have hexp : rank M-MatroidInverseZ.flatRank M F = j := by omega
      simp only [ite_eq_left he, hexp, ite_true, mul_one]
    · have hexp : rank M-MatroidInverseZ.flatRank M F ≠ j := by omega
      simp only [ite_eq_right he, ite_eq_right hexp.symm, mul_zero]
  · have hne : (⊥ : MatroidInverseZ.Flat M) ≠ F := by
      intro he
      have h0 : MatroidInverseZ.flatRank M F = 0 := by rw [← he, actualFlatRank_bot]
      omega
    have hexp : rank M-MatroidInverseZ.flatRank M F ≤ j := by omega
    have hdeg : MatroidInverseZ.flatRank M F ≤ 2*(j-(rank M-MatroidInverseZ.flatRank M F)) := by omega
    rw [flatSummand, mul_assoc, coeff_C_mul, coeff_X_pow_mul', ite_eq_left hexp,
      inverseKL_high_coeff (MatroidInverseZ.flatRank M) (actualFlatRank_strictMono M).monotone
        ⊥ F bot_le hne _ (by simpa only [actualFlatRank_bot, Nat.sub_zero] using hdeg), mul_zero,
      ite_eq_right (by omega : MatroidInverseZ.flatRank M F ≠ rank M-j)]

theorem IsPaving.actual_inverseZ_high_coeff {M : Matroid α} (hM : IsPaving M)
    (hr : 3 ≤ rank M) (j : ℕ) (hj : 2 ≤ j) (hjr : rank M < 2*j) (hjr' : j ≤ rank M) :
    (matroidInverseZ M).coeff j =
      ∑ F : MatroidInverseZ.Flat M,
        if MatroidInverseZ.flatRank M F = rank M-j then
          (-1 : ℤ)^j * IncidenceAlgebra.mu ℤ F ⊤ else 0 := by
  classical
  rw [actual_inverseZ_sum, finsetSum_coeff]
  exact sum_congr rfl (fun F _ => hM.flatSummand_high_coeff hr F j hj hjr hjr')

/-- All lower-half noncentral coefficients are actual upper Möbius sums. -/
theorem IsPaving.actual_inverseZ_lower_mu {M : Matroid α} (hM : IsPaving M)
    (hr : 3 ≤ rank M) (k : ℕ) (hk : 2*k < rank M) :
    (matroidInverseZ M).coeff k =
      ∑ F : MatroidInverseZ.Flat M,
        if MatroidInverseZ.flatRank M F = k then
          (-1 : ℤ)^(rank M-k) * IncidenceAlgebra.mu ℤ F ⊤ else 0 := by
  rw [actual_inverseZ_coeff_symm M k (by omega),
    hM.actual_inverseZ_high_coeff hr (rank M-k) (by omega) (by omega) (by omega),
    Nat.sub_sub_self (by omega : k ≤ rank M)]

end Paving
