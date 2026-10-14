import HardCoreActivityThreshold.InfluenceSimilarity
import HardCoreActivityThreshold.FiniteVariance

/-! Genuine influence similarity also includes deterministic pinned coordinates. -/
namespace HardCoreActivityThreshold
open Finset Matrix
open scoped ENNReal
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem correlationMatrix_zero_variance_right (μ : FiniteLaw (Finset V)) (u v : V)
    (hv : occupationVariance μ v = 0) : correlationMatrix μ u v = 0 := by
  unfold correlationMatrix occupationCovariance
  rw [FiniteLaw.covariance_eq_zero_of_variance_eq_zero μ _ _ hv, zero_div]

theorem correlationMatrix_zero_variance_left (μ : FiniteLaw (Finset V)) (u v : V)
    (hu : occupationVariance μ u = 0) : correlationMatrix μ u v = 0 := by
  rw [correlationMatrix_symm, correlationMatrix_zero_variance_right μ v u hu]

noncomputable def varianceActive (μ : FiniteLaw (Finset V)) (v : V) : ℝ :=
  if occupationVariance μ v = 0 then 0 else 1

noncomputable def regularizedVarianceScale (μ : FiniteLaw (Finset V)) (v : V) : ℝ :=
  if occupationVariance μ v = 0 then 1 else Real.sqrt (occupationVariance μ v)

noncomputable def absoluteActiveCorrelation (μ : FiniteLaw (Finset V)) : Matrix V V ℝ :=
  Matrix.of (fun u v => |correlationMatrix μ u v|) - Matrix.diagonal (varianceActive μ)

theorem regularizedVarianceScale_pos (μ : FiniteLaw (Finset V)) (v : V) :
    0 < regularizedVarianceScale μ v := by
  unfold regularizedVarianceScale
  split_ifs with hv
  · norm_num
  · apply Real.sqrt_pos.mpr
    exact lt_of_le_of_ne (μ.variance_nonneg _) (Ne.symm hv)

theorem varianceActive_mem (μ : FiniteLaw (Finset V)) (v : V) :
    0 ≤ varianceActive μ v ∧ varianceActive μ v ≤ 1 := by
  unfold varianceActive
  split_ifs <;> norm_num

theorem correlationMatrix_diag_active (μ : FiniteLaw (Finset V)) (v : V) :
    correlationMatrix μ v v = varianceActive μ v := by
  by_cases hv : occupationVariance μ v = 0
  · simp [varianceActive, hv, correlationMatrix_zero_variance_right μ v v hv]
  · have hpos : 0 < occupationVariance μ v := lt_of_le_of_ne (μ.variance_nonneg _) (Ne.symm hv)
    simp [varianceActive, hv, correlationMatrix_diag μ v hpos]

theorem influence_regularized_entry (μ : FiniteLaw (Finset V)) (u v : V) :
    influenceMatrix μ u v = (regularizedVarianceScale μ u)⁻¹ *
      absoluteActiveCorrelation μ u v * regularizedVarianceScale μ v := by
  by_cases huv : u = v
  · subst v
    simp only [influenceMatrix, true_or, ↓reduceIte, absoluteActiveCorrelation,
      Matrix.sub_apply, Matrix.of_apply, Matrix.diagonal_apply_eq, correlationMatrix_diag_active,
      abs_of_nonneg (varianceActive_mem μ u).1, sub_self, mul_zero, zero_mul]
  · by_cases hu : occupationVariance μ u = 0
    · simp [influenceMatrix, hu, absoluteActiveCorrelation, huv,
        correlationMatrix_zero_variance_left μ u v hu]
    · have hup : 0 < occupationVariance μ u := lt_of_le_of_ne (μ.variance_nonneg _) (Ne.symm hu)
      have hmu := marginal_mem_Ioo_of_variance_pos μ u hup
      rw [influenceMatrix_eq_covariance μ huv hmu.1 hmu.2]
      by_cases hv : occupationVariance μ v = 0
      · have hc : occupationCovariance μ u v = 0 := μ.covariance_eq_zero_of_variance_eq_zero _ _ hv
        simp [hc, absoluteActiveCorrelation, huv,
          correlationMatrix_zero_variance_right μ u v hv]
      · have hvp : 0 < occupationVariance μ v := lt_of_le_of_ne (μ.variance_nonneg _) (Ne.symm hv)
        simp only [regularizedVarianceScale, hu, hv, ↓reduceIte, absoluteActiveCorrelation,
          Matrix.sub_apply, Matrix.of_apply, Matrix.diagonal_apply, huv, sub_zero, correlationMatrix]
        rw [abs_div, Real.sqrt_mul hup.le, abs_mul,
          abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
        have hsu : Real.sqrt (occupationVariance μ u) ≠ 0 := (Real.sqrt_pos.mpr hup).ne'
        have hsv : Real.sqrt (occupationVariance μ v) ≠ 0 := (Real.sqrt_pos.mpr hvp).ne'
        have he := Real.sq_sqrt hup.le
        field_simp
        rw [he]


noncomputable def regularizedVarianceUnit (μ : FiniteLaw (Finset V)) : (Matrix V V ℝ)ˣ where
  val := diagonal (regularizedVarianceScale μ)
  inv := diagonal (fun v => (regularizedVarianceScale μ v)⁻¹)
  val_inv := by
    rw [diagonal_mul_diagonal]
    have he (v : V) : regularizedVarianceScale μ v * (regularizedVarianceScale μ v)⁻¹ = 1 :=
      mul_inv_cancel₀ (regularizedVarianceScale_pos μ v).ne'
    simp_rw [he]
    exact diagonal_one
  inv_val := by
    rw [diagonal_mul_diagonal]
    have he (v : V) : (regularizedVarianceScale μ v)⁻¹ * regularizedVarianceScale μ v = 1 :=
      inv_mul_cancel₀ (regularizedVarianceScale_pos μ v).ne'
    simp_rw [he]
    exact diagonal_one

theorem influence_regularized_similarity (μ : FiniteLaw (Finset V)) :
    influenceMatrix μ = ((regularizedVarianceUnit μ)⁻¹ : (Matrix V V ℝ)ˣ) *
      absoluteActiveCorrelation μ * (regularizedVarianceUnit μ : Matrix V V ℝ) := by
  ext u v
  change influenceMatrix μ u v =
    (diagonal (fun v => (regularizedVarianceScale μ v)⁻¹) * absoluteActiveCorrelation μ *
      diagonal (regularizedVarianceScale μ)) u v
  simp only [diagonal_mul, mul_diagonal]
  exact influence_regularized_entry μ u v

/-- The actual conditional-influence radius is unchanged by the regularized similarity. -/
theorem influenceSpectralRadius_eq_active (μ : FiniteLaw (Finset V)) :
    influenceSpectralRadius μ = spectralRadius ℂ
      ((absoluteActiveCorrelation μ).map (fun x : ℝ => (x : ℂ))) := by
  let f : Matrix V V ℝ →+* Matrix V V ℂ := Complex.ofRealHom.mapMatrix
  let U := Units.map f.toMonoidHom (regularizedVarianceUnit μ)
  have he : f (influenceMatrix μ) = (U⁻¹ : (Matrix V V ℂ)ˣ) *
      f (absoluteActiveCorrelation μ) * (U : Matrix V V ℂ) := by
    rw [influence_regularized_similarity μ, map_mul, map_mul]
    rfl
  unfold influenceSpectralRadius
  rw [spectralRadius_eq_of_unital, spectralRadius_eq_of_unital]
  have hs : spectrum ℂ (f (influenceMatrix μ)) = spectrum ℂ (f (absoluteActiveCorrelation μ)) := by
    rw [he]
    exact spectrum.units_conjugate'
  change (⨆ z ∈ spectrum ℂ (f (influenceMatrix μ)), (‖z‖₊ : ℝ≥0∞)) =
    ⨆ z ∈ spectrum ℂ (f (absoluteActiveCorrelation μ)), (‖z‖₊ : ℝ≥0∞)
  rw [hs]

end HardCoreActivityThreshold
