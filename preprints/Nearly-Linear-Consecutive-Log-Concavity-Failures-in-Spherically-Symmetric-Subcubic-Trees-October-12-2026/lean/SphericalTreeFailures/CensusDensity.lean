import SphericalTreeFailures.CharacteristicInversion
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! # The genuine entire densities of the conditional census limits -/
namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal FourierTransform

noncomputable def censusDensity (p : unitInterval) (i : Bool) (x : ℝ) : ℝ :=
  realFourierIntegral (censusCharacteristic p i) 0 x

theorem censusDensity_eq_characteristicDensity (p : unitInterval) (i : Bool) :
    censusDensity p i = characteristicDensity (censusLimitLaw p i) := by
  funext x
  exact realFourierIntegral_zero_eq _ x

theorem censusDensity_nonneg (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) (i : Bool) (x : ℝ) : 0 ≤ censusDensity p i x := by
  rw [censusDensity_eq_characteristicDensity]
  exact characteristicDensity_nonneg _ (censusCharacteristic_integrable p hc hp1 i) x

theorem censusDensity_continuous (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) (i : Bool) : Continuous (censusDensity p i) := by
  rw [censusDensity_eq_characteristicDensity]
  exact characteristicDensity_continuous _ (censusCharacteristic_integrable p hc hp1 i)

theorem censusDensity_integrable (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) (i : Bool) : Integrable (censusDensity p i) := by
  rw [censusDensity_eq_characteristicDensity]
  exact characteristicDensity_integrable _ (censusCharacteristic_integrable p hc hp1 i)

/-- The actual law, rather than a postulated limiting density. -/
theorem censusLimitLaw_eq_withDensity (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) (i : Bool) :
    censusLimitLaw p i = volume.withDensity (fun x => ENNReal.ofReal (censusDensity p i x)) := by
  rw [censusDensity_eq_characteristicDensity]
  exact measure_eq_withDensity_characteristicDensity _ (censusCharacteristic_integrable p hc hp1 i)

theorem censusDensity_integral (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) (i : Bool) : ∫ x, censusDensity p i x = 1 := by
  have h := congrArg (fun μ : Measure ℝ => ∫ _x : ℝ, (1 : ℝ) ∂μ)
    (censusLimitLaw_eq_withDensity p hc hp1 i)
  rw [integral_withDensity_eq_integral_toReal_smul
    (censusDensity_continuous p hc hp1 i).measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _] at h
  simp only [integral_const, probReal_univ, ENNReal.toReal_ofReal (censusDensity_nonneg p hc hp1 i _),
    smul_eq_mul, mul_one] at h
  exact h.symm

theorem censusDensity_analytic (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) (i : Bool) (x : ℝ) : AnalyticAt ℝ (censusDensity p i) x := by
  exact ((complexFourierIntegral_entire (censusCharacteristic_continuous p i)
    (censusCharacteristic_exponentialFourierIntegrable p hc hp1 i) 0).analyticAt x).re_ofReal

theorem censusDensity_not_zero (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) (i : Bool) : censusDensity p i ≠ 0 := by
  intro h
  have hh := censusDensity_integral p hc hp1 i
  rw [h] at hh
  simp at hh

/-- A nonzero globally real-analytic function cannot vanish on any nonempty open interval. -/
theorem analytic_not_identically_zero_dense_support {f : ℝ → ℝ}
    (ha : ∀ x, AnalyticAt ℝ f x) (h0 : f ≠ 0) : Dense (Function.support f) := by
  rw [dense_iff_inter_open]
  intro s hs hsne
  by_contra hnone
  have hz : ∀ x ∈ s, f x = 0 := by
    intro x hx
    by_contra hfx
    exact hnone ⟨x, ⟨hx, hfx⟩⟩
  obtain ⟨x, hx⟩ := hsne
  have he : f =ᶠ[𝓝 x] 0 := by
    filter_upwards [show ∀ᶠ y in 𝓝 x, y ∈ s from hs.mem_nhds hx] with y hy
    exact hz y hy
  have hall : Set.EqOn f 0 Set.univ :=
    (show AnalyticOnNhd ℝ f Set.univ from fun x _ => ha x).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ x) he
  apply h0
  exact funext fun x => hall (Set.mem_univ x)

theorem censusDensity_dense_support (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) (i : Bool) : Dense (Function.support (censusDensity p i)) :=
  analytic_not_identically_zero_dense_support (censusDensity_analytic p hc hp1 i)
    (censusDensity_not_zero p hc hp1 i)

end SphericalTreeFailures
