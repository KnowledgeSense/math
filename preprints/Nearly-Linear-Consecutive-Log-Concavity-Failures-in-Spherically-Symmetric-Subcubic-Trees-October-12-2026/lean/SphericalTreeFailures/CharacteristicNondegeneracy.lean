import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Probability.Moments.Variance

/-! # Strict characteristic modulus near zero from positive variance -/
namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology ProbabilityTheory

 theorem charFun_standardized_lt_one_near_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : AEMeasurable X μ)
    (hmean : ∫ x, X x ∂μ = 0) (hsq : ∫ x, X x ^ 2 ∂μ = 1) :
    ∀ᶠ t : ℝ in 𝓝 0, t ≠ 0 → ‖charFun (μ.map X) t‖ < 1 := by
  have hTaylor := taylor_charFun_two hX hmean hsq
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, t ^ 2 < 1 :=
    (continuousAt_id.pow 2).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) ^ 2 < 1))
  filter_upwards [hTaylor.bound (by norm_num : (0 : ℝ) < 1 / 4), hsmall] with t ht hs hne
  have hpoly : ‖(1 - (t : ℂ) ^ 2 / 2 : ℂ)‖ = 1 - t ^ 2 / 2 := by
    have he : (1 - (t : ℂ) ^ 2 / 2 : ℂ) = ((1 - t ^ 2 / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have he : ‖charFun (μ.map X) t‖ ≤
      ‖charFun (μ.map X) t - (1 - (t : ℂ) ^ 2 / 2)‖ + ‖1 - (t : ℂ) ^ 2 / 2‖ :=
    calc
      _ = ‖(charFun (μ.map X) t - (1 - (t : ℂ) ^ 2 / 2)) + (1 - (t : ℂ) ^ 2 / 2)‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [hpoly] at he
  simp only [norm_pow, Real.norm_eq_abs, sq_abs] at ht
  have hpos : 0 < t ^ 2 := sq_pos_of_ne_zero hne
  nlinarith

 theorem charFun_lt_one_near_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hL2 : MemLp id 2 μ) (hv : 0 < Var[id; μ]) :
    ∀ᶠ t : ℝ in 𝓝 0, t ≠ 0 → ‖charFun μ t‖ < 1 := by
  let m : ℝ := ∫ x : ℝ, x ∂μ
  let σ : ℝ := Real.sqrt Var[id; μ]
  let Z : ℝ → ℝ := fun x => (x - m) / σ
  have hσ : 0 < σ := Real.sqrt_pos.mpr hv
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have hσsq : σ ^ 2 = Var[id; μ] := Real.sq_sqrt hv.le
  have hint : Integrable (fun x : ℝ => x) μ := hL2.integrable (by norm_num)
  have hZ : Measurable Z := by dsimp [Z]; fun_prop
  have hmean : ∫ x, Z x ∂μ = 0 := by
    dsimp [Z]
    rw [integral_div, integral_sub hint (integrable_const _)]
    simp [m]
  have hsq : ∫ x, Z x ^ 2 ∂μ = 1 := by
    simp only [Z, div_pow, integral_div, hσsq]
    change (∫ a, (id a - ∫ x, id x ∂μ) ^ 2 ∂μ) / Var[id; μ] = 1
    rw [← variance_eq_integral measurable_id.aemeasurable]
    exact div_self (ne_of_gt hv)
  have hlocal := charFun_standardized_lt_one_near_zero μ Z hZ.aemeasurable hmean hsq
  have hscale : Tendsto (fun t : ℝ => σ * t) (𝓝 0) (𝓝 0) := by
    have hs : Tendsto (fun t : ℝ => σ * t) (𝓝 0) (𝓝 (σ * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    simpa only [mul_zero] using hs
  have hnorm (t : ℝ) : ‖charFun (μ.map Z) (σ * t)‖ = ‖charFun μ t‖ := by
    rw [charFun_apply_real, integral_map hZ.aemeasurable (by fun_prop)]
    have he (x : ℝ) : Complex.exp (((σ * t : ℝ) : ℂ) * (Z x) * Complex.I) =
        Complex.exp ((t : ℂ) * x * Complex.I) * Complex.exp ((-t * m : ℝ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      dsimp [Z]
      push_cast
      have hs : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ0
      field_simp
      ring
    simp_rw [he]
    rw [integral_mul_const, norm_mul]
    have hu : ‖Complex.exp ((-t * m : ℝ) * Complex.I)‖ = 1 := by simp [Complex.norm_exp]
    rw [hu, mul_one, charFun_apply_real]
  filter_upwards [hscale.eventually hlocal] with t ht hne
  rw [← hnorm t]
  exact ht (mul_ne_zero hσ0 hne)

end SphericalTreeFailures
