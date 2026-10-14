import EdgeColoringMixing.RetainedCandidate
import EdgeColoringMixing.PosteriorFirstMoment
import EdgeColoringMixing.RetainedRecursion

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EdgeColoringMixing.WeightedInjection
open Finset Matrix

variable {d q : ℕ}

noncomputable def marginalInverse (μ : FiniteLaw (Injection d q)) :
    Matrix (Fin d × Fin q) (Fin d × Fin q) ℝ :=
  Matrix.diagonal (fun x => 1 / mean μ x.1 x.2)

theorem diagonal_inverse_diagonal (μ : FiniteLaw (Injection d q)) :
    Matrix.diagonal (marginalVector μ) * marginalInverse μ *
      Matrix.diagonal (marginalVector μ) = Matrix.diagonal (marginalVector μ) := by
  ext x y
  simp only [marginalInverse, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, marginalVector]
  split_ifs
  · by_cases hx : mean μ x.1 x.2 = 0
    · simp [hx]
    · field_simp
  · rfl

theorem retained_inverse_diagonal (μ : FiniteLaw (Injection d q)) :
    retainedNegative μ * marginalInverse μ * Matrix.diagonal (marginalVector μ) = retainedNegative μ := by
  ext x y
  simp only [marginalInverse, Matrix.mul_diagonal, marginalVector]
  by_cases hy : mean μ y.1 y.2 = 0
  · simp [hy, retainedNegative_zero_of_mean_zero μ x y hy]
  · field_simp

theorem diagonal_inverse_retained (μ : FiniteLaw (Injection d q)) :
    Matrix.diagonal (marginalVector μ) * marginalInverse μ * retainedNegative μ = retainedNegative μ := by
  ext x y
  simp only [marginalInverse, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul, marginalVector]
  by_cases hx : mean μ x.1 x.2 = 0
  · simp [hx, retainedNegative]
  · field_simp

/-- Exact pseudoinverse expansion, with null cells handled by their zero retained block. -/
theorem retained_shift_square (μ : FiniteLaw (Injection d q)) (b : ℝ) :
    (retainedNegative μ + b • Matrix.diagonal (marginalVector μ)) * marginalInverse μ *
      (retainedNegative μ + b • Matrix.diagonal (marginalVector μ)) =
    retainedNegative μ * marginalInverse μ * retainedNegative μ +
      (2 * b) • retainedNegative μ + b^2 • Matrix.diagonal (marginalVector μ) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    diagonal_inverse_retained, retained_inverse_diagonal, diagonal_inverse_diagonal]
  ext x y
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The child candidate written on the parent's full cell coordinates. -/
noncomputable def posteriorCandidateOf (μ : FiniteLaw (Injection d q))
    (F : (Fin d × Fin q) → Matrix (Fin d × Fin q) (Fin d × Fin q) ℝ)
    (b : ℝ) (x : Fin d × Fin q) : Matrix (Fin d × Fin q) (Fin d × Fin q) ℝ :=
  (1 / (((d : ℝ) - 1) * ((d : ℝ) - 2))) •
    (F x + b • Matrix.diagonal (posteriorMean μ x))

/-- Exact average of embedded child candidates under the actual local stationary law. -/
theorem posteriorCandidate_average (μ : FiniteLaw (Injection d q))
    (F : (Fin d × Fin q) → Matrix (Fin d × Fin q) (Fin d × Fin q) ℝ)
    (b : ℝ) (hd : 3 ≤ d) :
    (∑ x ∈ active μ, (mean μ x.1 x.2 / d) • posteriorCandidateOf μ F b x) =
      (1 / ((d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2))) •
        ((∑ x ∈ active μ, mean μ x.1 x.2 • F x) +
          (b * ((d : ℝ) - 1)) • Matrix.diagonal (marginalVector μ)) := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hdm : 0 < (d : ℝ) - 1 := by
    have h : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hdn : 0 < (d : ℝ) - 2 := by
    have h : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsplit : (∑ x ∈ active μ, (mean μ x.1 x.2 / d) • posteriorCandidateOf μ F b x) =
      (1 / ((d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2))) •
        ((∑ x ∈ active μ, mean μ x.1 x.2 • F x) +
          b • (∑ x ∈ active μ, mean μ x.1 x.2 • Matrix.diagonal (posteriorMean μ x))) := by
    ext y z
    simp only [Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      posteriorCandidateOf]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    field_simp
  rw [hsplit, posterior_diagonal_first_moment]
  simp only [smul_smul]
  rfl

/-- The full matrix recursion follows from the retained-block error and scalar budget. -/
theorem retainedCandidate_recursion (W : Fin d → Fin q → ℝ) {s b b' C : ℝ}
    (hW : RowSurplus W s) (hd : 3 ≤ d) (hb : 0 ≤ b)
    (F : (Fin d × Fin q) → Matrix (Fin d × Fin q) (Fin d × Fin q) ℝ)
    (herror : let μ := law W hW.nonneg (partition_pos W hW)
      (C • Matrix.diagonal (marginalVector μ) -
        ((∑ x ∈ active μ, mean μ x.1 x.2 • F x) -
          ((d : ℝ) - 2) • retainedNegative μ +
          retainedNegative μ * marginalInverse μ * retainedNegative μ)).PosSemidef)
    (hbudget : C + 2 * b / (s + 1) + b^2 ≤ ((d : ℝ) - 2) * b - ((d : ℝ) - 1) * b') :
    let μ := law W hW.nonneg (partition_pos W hW)
    (retainedCandidate μ b - (((d : ℝ) - 1) / ((d : ℝ) - 2)) •
        (retainedCandidate μ b * ((d : ℝ) • marginalInverse μ) * retainedCandidate μ b) -
      ∑ x ∈ active μ, (mean μ x.1 x.2 / d) • posteriorCandidateOf μ F b' x).PosSemidef := by
  dsimp only at herror ⊢
  let μ := law W hW.nonneg (partition_pos W hW)
  let D := Matrix.diagonal (marginalVector μ)
  let A := retainedNegative μ
  let E := ∑ x ∈ active μ, mean μ x.1 x.2 • F x
  have hD : D.PosSemidef := Matrix.posSemidef_diagonal_iff.mpr (fun x => mean_nonneg μ x.1 x.2)
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hdm : 0 < (d : ℝ) - 1 := by
    have h : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hdn : 0 < (d : ℝ) - 2 := by
    have h : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsmall := (retainedNegative_upper W hW).smul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb)
  have hslack := hD.smul (sub_nonneg.mpr hbudget)
  have hsum := ((herror.add hsmall).add hslack).smul
    (show 0 ≤ 1 / ((d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2)) by positivity)
  have hsq : retainedCandidate μ b * ((d : ℝ) • marginalInverse μ) * retainedCandidate μ b =
      ((d : ℝ) / ((d : ℝ) * ((d : ℝ) - 1))^2) •
        (A * marginalInverse μ * A + (2 * b) • A + b^2 • D) := by
    unfold retainedCandidate
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, retained_shift_square]
    congr 1
    field_simp
  change (retainedCandidate μ b - (((d : ℝ) - 1) / ((d : ℝ) - 2)) •
      (retainedCandidate μ b * ((d : ℝ) • marginalInverse μ) * retainedCandidate μ b) -
      ∑ x ∈ active μ, (mean μ x.1 x.2 / d) • posteriorCandidateOf μ F b' x).PosSemidef
  rw [hsq, posteriorCandidate_average μ F b' hd]
  convert hsum using 1
  ext y z
  simp only [retainedCandidate, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul]
  dsimp only [D, A, E]
  field_simp
  ring

/-- The original harmonic candidate satisfies the full matrix recursion on the actual
weighted-injection law. No covariance or matrix-recursion premise remains. -/
theorem retainedCandidate_column_recursion (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (Δ : ℕ) (hd : 3 ≤ d) (hdΔ : d ≤ Δ)
    (hfirst : 8 * harmonicHeight Δ ≤ s + 1)
    (hsecond : 4 * (22 + 8 * ((q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2)) *
      (Δ : ℝ) * (harmonicHeight Δ)^2 ≤ (s + 1)^2) :
    let μ := law W hW.nonneg (partition_pos W hW)
    let L := 22 + 8 * ((q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2)
    let b := columnError L (s + 1) d
    let b' := columnError L (s + 1) (d - 1)
    (retainedCandidate μ b - (((d : ℝ) - 1) / ((d : ℝ) - 2)) •
        (retainedCandidate μ b * ((d : ℝ) • marginalInverse μ) * retainedCandidate μ b) -
      ∑ x ∈ active μ, (mean μ x.1 x.2 / d) •
        posteriorCandidateOf μ (retainedPosterior μ) b' x).PosSemidef := by
  have hs : 0 < s + 1 := by linarith [hW.positive]
  have hV : 0 ≤ (q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2 := by
    have := hW.positive
    positivity
  apply retainedCandidate_recursion W hW hd
    (columnError_nonneg (by positivity) (by omega))
    (retainedPosterior (law W hW.nonneg (partition_pos W hW)))
  · exact retainedRecursionError_bound W hW Δ hdΔ
  · exact columnError_recursion hs hV hd hdΔ hfirst hsecond

end EdgeColoringMixing.WeightedInjection
