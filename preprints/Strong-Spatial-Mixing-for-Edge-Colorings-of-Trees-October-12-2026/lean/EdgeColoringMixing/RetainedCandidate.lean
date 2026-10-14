import EdgeColoringMixing.ColumnCoercivity
import EdgeColoringMixing.ColumnParameters

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EdgeColoringMixing.WeightedInjection
open Finset Matrix

variable {d q : ℕ}

/-- The unnormalized diagonal stationary law, extended by zero at null cells. -/
noncomputable def rawPi (μ : FiniteLaw (Injection d q)) :
    Matrix (Fin d × Fin q) (Fin d × Fin q) ℝ :=
  (1 / (d : ℝ)) • Matrix.diagonal (marginalVector μ)

/-- The candidate matrix in the release's retained-column induction. -/
noncomputable def retainedCandidate (μ : FiniteLaw (Injection d q)) (b : ℝ) :
    Matrix (Fin d × Fin q) (Fin d × Fin q) ℝ :=
  (1 / ((d : ℝ) * ((d : ℝ) - 1))) •
    (retainedNegative μ + b • Matrix.diagonal (marginalVector μ))

/-- The local-walk centered matrix, expressed via the exact covariance identity. -/
noncomputable def covarianceTarget (μ : FiniteLaw (Injection d q)) :
    Matrix (Fin d × Fin q) (Fin d × Fin q) ℝ :=
  (1 / ((d : ℝ) * ((d : ℝ) - 1))) •
    (covariance μ - Matrix.diagonal (marginalVector μ))

theorem rawPi_posSemidef (μ : FiniteLaw (Injection d q)) : (rawPi μ).PosSemidef := by
  have hD : (Matrix.diagonal (marginalVector μ)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun x => mean_nonneg μ x.1 x.2)
  exact hD.smul (show 0 ≤ 1 / (d : ℝ) by positivity)

theorem retainedCandidate_hermitian (μ : FiniteLaw (Injection d q)) (b : ℝ) :
    (retainedCandidate μ b).IsHermitian := by
  have hD : (Matrix.diagonal (marginalVector μ)).IsHermitian := by simp
  unfold retainedCandidate
  exact ((retainedNegative_hermitian μ).add (hD.smul (IsSelfAdjoint.all b))).smul
    (IsSelfAdjoint.all _)

/-- The candidate's spectral cap follows from the actual marginal upper bound. -/
theorem retainedCandidate_surplus_upper (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (hd : 2 ≤ d) (b : ℝ) :
    let μ := law W hW.nonneg (partition_pos W hW)
    (((b + 1 / (s + 1)) / ((d : ℝ) - 1)) • rawPi μ - retainedCandidate μ b).PosSemidef := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hdm : 0 < (d : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h := (retainedNegative_upper W hW).smul
    (show 0 ≤ 1 / ((d : ℝ) * ((d : ℝ) - 1)) by positivity)
  dsimp only at h ⊢
  convert h using 1
  ext x y
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, retainedCandidate,
    rawPi, Matrix.add_apply]
  field_simp
  ring

theorem retainedCandidate_spectral_cap (W : Fin d → Fin q → ℝ) {s b : ℝ}
    (hW : RowSurplus W s) (hd : 2 ≤ d)
    (hcap : (b + 1 / (s + 1)) / ((d : ℝ) - 1) ≤ ((d : ℝ) - 1) / (3 * (d : ℝ) - 1)) :
    let μ := law W hW.nonneg (partition_pos W hW)
    ((((d : ℝ) - 1) / (3 * (d : ℝ) - 1)) • rawPi μ - retainedCandidate μ b).PosSemidef := by
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  have h := (retainedCandidate_surplus_upper W hW hd b).add
    ((rawPi_posSemidef μ).smul (sub_nonneg.mpr hcap))
  convert h using 1
  ext x y
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Exact scaling between retained covariance and the local-walk target. -/
theorem retainedCandidate_sub_target (μ : FiniteLaw (Injection d q)) (b : ℝ) :
    retainedCandidate μ b - covarianceTarget μ =
      (1 / ((d : ℝ) * ((d : ℝ) - 1))) •
        (((1 + b) • Matrix.diagonal (marginalVector μ)) + retainedNegative μ - covariance μ) := by
  ext x y
  simp only [retainedCandidate, covarianceTarget, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

/-- The actual two-row base satisfies the matrix induction, including its surplus-dependent constant. -/
theorem retainedCandidate_base (W : Fin 2 → Fin q → ℝ) {s b : ℝ}
    (hW : RowSurplus W s) (hb : 10 / (s + 1)^2 ≤ b) :
    let μ := law W hW.nonneg (partition_pos W hW)
    (retainedCandidate μ b - covarianceTarget μ).PosSemidef := by
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  have hD : (Matrix.diagonal (marginalVector μ)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun x => mean_nonneg μ x.1 x.2)
  have h := (two_row_retained_covariance W hW).add (hD.smul (sub_nonneg.mpr hb))
  have hret : (((1 + b) • Matrix.diagonal (marginalVector μ)) + retainedNegative μ - covariance μ).PosSemidef := by
    convert h using 1
    ext x y
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [retainedCandidate_sub_target]
  exact hret.smul (by norm_num)

/-- Returning from the matrix induction yields the actual retained-column covariance inequality. -/
theorem retained_covariance_of_candidate (W : Fin d → Fin q → ℝ) {s b : ℝ}
    (hW : RowSurplus W s) (hd : 2 ≤ d)
    (hcandidate : let μ := law W hW.nonneg (partition_pos W hW)
      (retainedCandidate μ b - covarianceTarget μ).PosSemidef) :
    let μ := law W hW.nonneg (partition_pos W hW)
    (((1 + b) • Matrix.diagonal (marginalVector μ)) + retainedNegative μ - covariance μ).PosSemidef := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hdm : 0 < (d : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  dsimp only at hcandidate ⊢
  rw [retainedCandidate_sub_target] at hcandidate
  have h := hcandidate.smul (show 0 ≤ (d : ℝ) * ((d : ℝ) - 1) by positivity)
  convert h using 1
  ext x y
  simp only [Matrix.smul_apply, smul_eq_mul]
  field_simp

end EdgeColoringMixing.WeightedInjection
