import MainTheorems.AHOConstants.TwoDimensionPositivePowers

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open ResearchMain.DiagonalSchatten

noncomputable def positivePhase (z : ℂ) : ℂ :=
  if z = 0 then 1 else star z / (‖z‖ : ℝ)

theorem positivePhase_norm (z : ℂ) : ‖positivePhase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [positivePhase, hz]
  · simp only [positivePhase, hz, ite_false, norm_div, norm_star, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg z), div_self (norm_ne_zero_iff.mpr hz)]

theorem positivePhase_star_self (z : ℂ) : star (positivePhase z) * positivePhase z = 1 := by
  simpa [RCLike.star_def, positivePhase_norm z] using Complex.conj_mul' (positivePhase z)

theorem positivePhase_self_star (z : ℂ) : positivePhase z * star (positivePhase z) = 1 := by
  rw [mul_comm, positivePhase_star_self]

theorem positivePhase_mul (z : ℂ) : positivePhase z * z = (‖z‖ : ℝ) := by
  by_cases hz : z = 0
  · simp [hz]
  · have hn : (‖z‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hz
    have hnc : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
    simp only [positivePhase, hz, ite_false]
    field_simp [hnc]
    simpa only [RCLike.star_def, ← Complex.ofReal_pow, pow_two] using Complex.conj_mul' z

noncomputable def phaseMatrix (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![positivePhase z, 1]

theorem phaseMatrix_unitary (z : ℂ) : phaseMatrix z ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Unitary.mem_iff]
  constructor
  · simp only [phaseMatrix, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    change Matrix.diagonal (fun i : Fin 2 =>
      star (![positivePhase z, 1] i) * ![positivePhase z, 1] i) =
        Matrix.diagonal (fun _ : Fin 2 => (1 : ℂ))
    apply congrArg Matrix.diagonal
    funext i
    fin_cases i
    · exact positivePhase_star_self z
    · simp
  · simp only [phaseMatrix, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    change Matrix.diagonal (fun i : Fin 2 =>
      ![positivePhase z, 1] i * star (![positivePhase z, 1] i)) =
        Matrix.diagonal (fun _ : Fin 2 => (1 : ℂ))
    apply congrArg Matrix.diagonal
    funext i
    fin_cases i
    · exact positivePhase_self_star z
    · simp

noncomputable def phaseUnitary (z : ℂ) : unitary (Matrix (Fin 2) (Fin 2) ℂ) :=
  ⟨phaseMatrix z, phaseMatrix_unitary z⟩

theorem hermitianTwo_phase_conjugation (a b : ℝ) (z : ℂ) :
    Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) (phaseUnitary z)
      (hermitianTwo a b z) = hermitianTwo a b ((‖z‖ : ℝ) : ℂ) := by
  rw [Unitary.conjStarAlgAut_apply]
  change phaseMatrix z * hermitianTwo a b z * star (phaseMatrix z) = _
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [phaseMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, hermitianTwo]
    calc
      positivePhase z * (a : ℂ) * star (positivePhase z) =
          (a : ℂ) * (positivePhase z * star (positivePhase z)) := by ring
      _ = (a : ℂ) := by rw [positivePhase_self_star, mul_one]
  · simp [phaseMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      hermitianTwo, positivePhase_mul]
  · have h := congrArg star (positivePhase_mul z)
    simp only [star_mul, RCLike.star_def, Complex.conj_ofReal] at h
    simpa [phaseMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, hermitianTwo] using h
  · simp [phaseMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, hermitianTwo]

theorem diagonal_phase_conjugation (v : Fin 2 → ℂ) (z : ℂ) :
    Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) (phaseUnitary z)
      (Matrix.diagonal v) = Matrix.diagonal v := by
  rw [Unitary.conjStarAlgAut_apply]
  change phaseMatrix z * Matrix.diagonal v * star (phaseMatrix z) = _
  have hc : phaseMatrix z * Matrix.diagonal v = Matrix.diagonal v * phaseMatrix z := by
    unfold phaseMatrix
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    exact mul_comm _ _
  rw [hc, Matrix.mul_assoc, Unitary.mul_star_self_of_mem (phaseMatrix_unitary z), Matrix.mul_one]

theorem hermitianTwo_representation {B : Matrix (Fin 2) (Fin 2) ℂ} (hB : B.IsHermitian) :
    B = hermitianTwo (B 0 0).re (B 1 1).re (B 0 1) := by
  have hdiag : ∀ i, ((B i i).re : ℂ) = B i i := fun i =>
    RCLike.conj_eq_iff_re.mp (by simpa only [RCLike.star_def] using hB.apply i i)
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [hermitianTwo] using (hdiag 0).symm
  · simp [hermitianTwo]
  · simpa [hermitianTwo] using (hB.apply 1 0).symm
  · simpa [hermitianTwo] using (hdiag 1).symm

theorem twoDimension_normal_form {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ∃ (U : unitary (Matrix (Fin 2) (Fin 2) ℂ)) (v : Fin 2 → ℝ),
      (∀ i, 0 ≤ v i) ∧
      Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) U A =
        Matrix.diagonal (fun i => (v i : ℂ)) ∧
      ∀ (r : ℝ), 0 ≤ r → ∀ i j,
        0 ≤ (spectralPower (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) U B) r i j).re ∧
          (spectralPower (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) U B) r i j).im = 0 := by
  let V := star hA.isHermitian.eigenvectorUnitary
  let C := Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) V B
  have hC : C.PosSemidef := conjugation_posSemidef hB V
  let a := (C 0 0).re
  let b := (C 1 1).re
  let z := C 0 1
  let U := phaseUnitary z * V
  have hnorm : Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) U B =
      hermitianTwo a b ((‖z‖ : ℝ) : ℂ) := by
    rw [Unitary.conjStarAlgAut_mul_apply]
    change Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) (phaseUnitary z) C = _
    rw [hermitianTwo_representation hC.isHermitian]
    exact hermitianTwo_phase_conjugation a b z
  refine ⟨U, hA.isHermitian.eigenvalues, hA.eigenvalues_nonneg, ?_, ?_⟩
  · rw [Unitary.conjStarAlgAut_mul_apply]
    rw [hA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary]
    simpa only [RCLike.ofReal_eq_complex_ofReal, Function.comp_def] using
      diagonal_phase_conjugation (fun i => (hA.isHermitian.eigenvalues i : ℂ)) z
  · intro r hr i j
    have hPD := conjugation_posSemidef hB U
    rw [hnorm] at hPD ⊢
    exact hermitianTwo_nonnegative_power_entries (norm_nonneg z) hPD hr i j

end ResearchMain.AHOConstants
