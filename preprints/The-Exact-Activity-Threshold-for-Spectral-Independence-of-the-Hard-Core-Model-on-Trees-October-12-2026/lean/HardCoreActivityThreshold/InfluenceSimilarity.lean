import HardCoreActivityThreshold.MatrixSpectrum

/-! The actual influence matrix is diagonally similar to absolute correlation minus identity. -/
namespace HardCoreActivityThreshold
open Finset Matrix
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem marginal_mem_Ioo_of_variance_pos (μ : FiniteLaw (Finset V)) (v : V)
    (hv : 0 < occupationVariance μ v) : marginal μ v ∈ Set.Ioo (0 : ℝ) 1 := by
  have hlo := marginal_nonneg μ v
  have hhi := marginal_le_one μ v
  change 0 < μ.variance (occupation v) at hv
  rw [occupation_variance] at hv
  constructor <;> nlinarith

noncomputable def absoluteCorrelationMinusIdentity (μ : FiniteLaw (Finset V)) : Matrix V V ℝ :=
  Matrix.of (fun u v => |correlationMatrix μ u v|) - 1

theorem influence_similarity_entry (μ : FiniteLaw (Finset V))
    (hvar : ∀ v, 0 < occupationVariance μ v) (u v : V) :
    influenceMatrix μ u v = (Real.sqrt (occupationVariance μ u))⁻¹ *
      absoluteCorrelationMinusIdentity μ u v * Real.sqrt (occupationVariance μ v) := by
  by_cases huv : u = v
  · subst v
    simp [absoluteCorrelationMinusIdentity, correlationMatrix_diag μ u (hvar u)]
  · have hmu := marginal_mem_Ioo_of_variance_pos μ u (hvar u)
    rw [influenceMatrix_eq_covariance μ huv hmu.1 hmu.2]
    simp only [absoluteCorrelationMinusIdentity, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply, huv,
      ite_false, sub_zero, correlationMatrix]
    rw [abs_div, Real.sqrt_mul (hvar u).le, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
    have hsu : 0 < Real.sqrt (occupationVariance μ u) := Real.sqrt_pos.mpr (hvar u)
    have hsv : 0 < Real.sqrt (occupationVariance μ v) := Real.sqrt_pos.mpr (hvar v)
    have he := Real.sq_sqrt (hvar u).le
    field_simp
    rw [he]
    field_simp [(hvar u).ne']

noncomputable def varianceStandardizer (μ : FiniteLaw (Finset V)) : Matrix V V ℝ :=
  diagonal (fun v => Real.sqrt (occupationVariance μ v))

noncomputable def inverseVarianceStandardizer (μ : FiniteLaw (Finset V)) : Matrix V V ℝ :=
  diagonal (fun v => (Real.sqrt (occupationVariance μ v))⁻¹)

theorem varianceStandardizer_mul_inverse (μ : FiniteLaw (Finset V))
    (hvar : ∀ v, 0 < occupationVariance μ v) :
    varianceStandardizer μ * inverseVarianceStandardizer μ = 1 := by
  unfold varianceStandardizer inverseVarianceStandardizer
  rw [diagonal_mul_diagonal]
  have h (v : V) : Real.sqrt (occupationVariance μ v) * (Real.sqrt (occupationVariance μ v))⁻¹ = 1 :=
    mul_inv_cancel₀ (Real.sqrt_pos.mpr (hvar v)).ne'
  simp_rw [h]
  exact diagonal_one

theorem inverseVarianceStandardizer_mul (μ : FiniteLaw (Finset V))
    (hvar : ∀ v, 0 < occupationVariance μ v) :
    inverseVarianceStandardizer μ * varianceStandardizer μ = 1 := by
  unfold varianceStandardizer inverseVarianceStandardizer
  rw [diagonal_mul_diagonal]
  have h (v : V) : (Real.sqrt (occupationVariance μ v))⁻¹ * Real.sqrt (occupationVariance μ v) = 1 :=
    inv_mul_cancel₀ (Real.sqrt_pos.mpr (hvar v)).ne'
  simp_rw [h]
  exact diagonal_one

/-- The similarity is a theorem about conditional-probability influences of the finite law. -/
theorem influenceMatrix_similarity (μ : FiniteLaw (Finset V))
    (hvar : ∀ v, 0 < occupationVariance μ v) :
    influenceMatrix μ = inverseVarianceStandardizer μ * absoluteCorrelationMinusIdentity μ *
      varianceStandardizer μ := by
  ext u v
  simp only [varianceStandardizer, inverseVarianceStandardizer, mul_diagonal, diagonal_mul]
  exact influence_similarity_entry μ hvar u v

noncomputable def varianceStandardizerUnit (μ : FiniteLaw (Finset V))
    (hvar : ∀ v, 0 < occupationVariance μ v) : (Matrix V V ℝ)ˣ where
  val := varianceStandardizer μ
  inv := inverseVarianceStandardizer μ
  val_inv := varianceStandardizer_mul_inverse μ hvar
  inv_val := inverseVarianceStandardizer_mul μ hvar

theorem influenceMatrix_complex_spectrum (μ : FiniteLaw (Finset V))
    (hvar : ∀ v, 0 < occupationVariance μ v) :
    spectrum ℂ ((influenceMatrix μ).map (fun x : ℝ => (x : ℂ))) =
      spectrum ℂ ((absoluteCorrelationMinusIdentity μ).map (fun x : ℝ => (x : ℂ))) := by
  let f : Matrix V V ℝ →+* Matrix V V ℂ := Complex.ofRealHom.mapMatrix
  let U := Units.map f.toMonoidHom (varianceStandardizerUnit μ hvar)
  have he : f (influenceMatrix μ) = (U⁻¹ : (Matrix V V ℂ)ˣ) *
      f (absoluteCorrelationMinusIdentity μ) * (U : Matrix V V ℂ) := by
    rw [influenceMatrix_similarity μ hvar, map_mul, map_mul]
    rfl
  change spectrum ℂ (f (influenceMatrix μ)) = spectrum ℂ (f (absoluteCorrelationMinusIdentity μ))
  rw [he]
  exact spectrum.units_conjugate'

/-- Equality of genuine complex spectral radii follows from the proved similarity. -/
theorem influenceSpectralRadius_eq_absoluteCorrelation (μ : FiniteLaw (Finset V))
    (hvar : ∀ v, 0 < occupationVariance μ v) :
    influenceSpectralRadius μ = spectralRadius ℂ
      ((absoluteCorrelationMinusIdentity μ).map (fun x : ℝ => (x : ℂ))) := by
  unfold influenceSpectralRadius
  rw [spectralRadius_eq_of_unital, spectralRadius_eq_of_unital,
    influenceMatrix_complex_spectrum μ hvar]

end HardCoreActivityThreshold
