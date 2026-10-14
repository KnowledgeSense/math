import MainTheorems.WishartBlocks.SpectralLaw.Weyl.CayleyMatrix

namespace ResearchMain.WishartBlocks.Weyl

noncomputable def inverseCayleyMatrix {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (Q - 1) * (Q + 1)⁻¹

theorem inverseCayleyMatrix_mul_one_add {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : (1 + Q).det ≠ 0) :
    inverseCayleyMatrix Q * (Q + 1) = Q - 1 := by
  have hunit : IsUnit (Q + 1).det := by
    rw [add_comm]
    exact isUnit_iff_ne_zero.mpr hQ
  rw [inverseCayleyMatrix, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one]

theorem inverseCayleyMatrix_transpose {n : ℕ}
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) (hQ : (1 + Q.val).det ≠ 0) :
    (inverseCayleyMatrix Q.val).transpose = -inverseCayleyMatrix Q.val := by
  let A : Matrix (Fin n) (Fin n) ℝ := Q.val + 1
  let K := inverseCayleyMatrix Q.val
  have hunit : IsUnit A.det := by
    dsimp [A]
    rw [add_comm]
    exact isUnit_iff_ne_zero.mpr hQ
  have hunitT : IsUnit A.transpose.det := by rwa [Matrix.det_transpose]
  have hKA : K * A = Q.val - 1 := inverseCayleyMatrix_mul_one_add Q.val hQ
  have horth := (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp Q.property
  have hzero : A.transpose * (K.transpose + K) * A = 0 := by
    calc
      A.transpose * (K.transpose + K) * A =
        (K * A).transpose * A + A.transpose * (K * A) := by
          simp only [Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul,
            Matrix.mul_assoc]
      _ = (Q.val - 1).transpose * A + A.transpose * (Q.val - 1) := by rw [hKA]
      _ = (Q.val.transpose * Q.val - 1) + (Q.val.transpose * Q.val - 1) := by
        dsimp [A]
        simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one]
        noncomm_ring
      _ = 0 := by rw [horth]; simp
  have hcancel := congrArg (fun W : Matrix (Fin n) (Fin n) ℝ =>
    A.transpose⁻¹ * W * A⁻¹) hzero
  have hcancelL : A.transpose⁻¹ * (A.transpose * (K.transpose + K) * A) * A⁻¹ =
      K.transpose + K := by
    calc
      _ = ((A.transpose⁻¹ * A.transpose) * (K.transpose + K)) * (A * A⁻¹) := by
        simp only [Matrix.mul_assoc]
      _ = K.transpose + K := by
        rw [Matrix.nonsing_inv_mul _ hunitT, Matrix.mul_nonsing_inv _ hunit,
          Matrix.one_mul, Matrix.mul_one]
  have hsum : K.transpose + K = 0 := by
    simpa only [hcancelL, Matrix.mul_zero, Matrix.zero_mul] using hcancel
  exact eq_neg_of_add_eq_zero_left hsum

theorem cayleyMatrix_inverseCayleyMatrix {n : ℕ}
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) (hQ : (1 + Q.val).det ≠ 0) :
    cayleyMatrix (inverseCayleyMatrix Q.val) = Q.val := by
  let K := inverseCayleyMatrix Q.val
  have hskew : K.transpose = -K := inverseCayleyMatrix_transpose Q hQ
  have hunit : IsUnit (1 - K).det :=
    isUnit_iff_ne_zero.mpr (one_sub_skew_det_ne_zero hskew)
  have hKA : K * (Q.val + 1) = Q.val - 1 :=
    inverseCayleyMatrix_mul_one_add Q.val hQ
  have hEQ : (1 - K) * Q.val = 1 + K := by
    have h := hKA
    rw [Matrix.mul_add, Matrix.mul_one] at h
    calc
      (1 - K) * Q.val = Q.val - K * Q.val := by noncomm_ring
      _ = 1 + K := by
        apply sub_eq_iff_eq_add.mpr
        calc
          Q.val = (Q.val - 1) + 1 := by noncomm_ring
          _ = (K * Q.val + K) + 1 := by rw [h]
          _ = (1 + K) + K * Q.val := by abel
  change (1 - K)⁻¹ * (1 + K) = Q.val
  rw [← hEQ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul]

theorem skewMatrix_coordinates {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    (hK : K.transpose = -K) : skewMatrix (symmetricCoordinates K) = K := by
  ext i j
  have hdiag (i : Fin n) : K i i = 0 := by
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i i) hK
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
    linarith
  have hoff (i j : Fin n) : K j i = -K i j := by
    exact congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hK
  rcases lt_trichotomy j i with h | h | h
  · simp only [skewMatrix, dite_eq_left h]
    rfl
  · subst j
    simp [skewMatrix, hdiag]
  · simp only [skewMatrix, dite_eq_right (not_lt_of_gt h), dite_eq_left h]
    change -K j i = K i j
    exact (hoff j i).symm

theorem orthogonal_has_signed_cayley_representation {n : ℕ}
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    ∃ (s : Fin n → Bool) (z : LowerIndex n → ℝ),
      cayleyOrthogonalMatrix z = Q * signOrthogonal s := by
  obtain ⟨s, hs⟩ := exists_signed_columns_det_one_add_ne_zero Q.val
  let U : Matrix.orthogonalGroup (Fin n) ℝ := Q * signOrthogonal s
  have hU : (1 + U.val).det ≠ 0 := hs
  let K := inverseCayleyMatrix U.val
  have hskew : K.transpose = -K := inverseCayleyMatrix_transpose U hU
  refine ⟨s, symmetricCoordinates K, Subtype.ext ?_⟩
  change cayleyMatrix (skewMatrix (symmetricCoordinates K)) = U.val
  rw [skewMatrix_coordinates hskew]
  exact cayleyMatrix_inverseCayleyMatrix U hU

end ResearchMain.WishartBlocks.Weyl
