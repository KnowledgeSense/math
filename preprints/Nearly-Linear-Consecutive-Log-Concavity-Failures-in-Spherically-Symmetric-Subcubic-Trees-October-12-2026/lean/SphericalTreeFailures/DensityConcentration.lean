import SphericalTreeFailures.CensusDensityPositivity
import Mathlib.Analysis.Convex.Function

/-! # Concentration and interval maxima for the actual census densities -/
namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem density_measureReal_eq_integral (μ : Measure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x)
    (he : μ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {s : Set ℝ} (hs : MeasurableSet s) : μ.real s = ∫ x in s, f x := by
  rw [he]
  have h := setIntegral_withDensity_eq_setIntegral_toReal_smul (μ := volume)
    hf.ennreal_ofReal (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))
    (fun _ : ℝ => (1 : ℝ)) hs
  simpa only [setIntegral_const, smul_eq_mul, mul_one, ENNReal.toReal_ofReal (hfn _)] using h

theorem interval_density_peak {f : ℝ → ℝ} (hf : Continuous f) (hfi : Integrable f)
    {u v M : ℝ} (huv : u < v) (hM : M ≤ ∫ x in Set.Icc u v, f x) :
    ∃ x ∈ Set.Icc u v, M ≤ (v - u) * f x := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr huv.le) hf.continuousOn
  refine ⟨x, hx, hM.trans ?_⟩
  calc
    _ ≤ ∫ _ in Set.Icc u v, f x := setIntegral_mono_on hfi.integrableOn
      (integrableOn_const (by simp [Real.volume_Icc])) measurableSet_Icc (fun y hy => hmax hy)
    _ = (v - u) * f x := by
      rw [setIntegral_const, Real.volume_real_Icc, max_eq_left (sub_nonneg.mpr huv.le)]
      rfl

theorem censusLimitLaw_memLp_id (p : unitInterval) (i : Bool) :
    MemLp (id : ℝ → ℝ) 2 (censusLimitLaw p i) := by
  exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable
    (measurable_censusLimit p i).aemeasurable).mpr (memLp_censusLimit p i)

theorem censusLimitLaw_mean (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) (i : Bool) :
    ∫ x, x ∂censusLimitLaw p i = boolIndicator i - stationaryProbability p := by
  change (∫ x, id x ∂(broadcastMeasure p).map (censusLimit p i)) = _
  rw [integral_map (measurable_censusLimit p i).aemeasurable
    measurable_id.aestronglyMeasurable]
  exact integral_censusLimit p hc i

theorem censusLimitLaw_chebyshev (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp : 99 / 100 < (p : ℝ)) (i : Bool) {r : ℝ} (hr : 0 < r) :
    (censusLimitLaw p i).real {x | r ≤ |x - (boolIndicator i - stationaryProbability p)|} ≤
      2 * (1 - (p : ℝ)) / r ^ 2 := by
  have h := meas_ge_le_variance_div_sq (censusLimitLaw_memLp_id p i) hr
  change censusLimitLaw p i {x | r ≤ |x - ∫ y, y ∂censusLimitLaw p i|} ≤ _ at h
  rw [censusLimitLaw_mean p hc i] at h
  have hb := (variance_censusLimit_bound p hc i).trans (sharp_variance_bound hp p.property.2)
  have hv : Var[id; censusLimitLaw p i] = Var[censusLimit p i; broadcastMeasure p] :=
    variance_id_map (measurable_censusLimit p i).aemeasurable
  have hn : 0 ≤ Var[id; censusLimitLaw p i] / r ^ 2 := div_nonneg (variance_nonneg _ _) (sq_nonneg r)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans
    (by rw [ENNReal.toReal_ofReal hn, hv]; exact div_le_div_of_nonneg_right hb (sq_nonneg r))

theorem censusDensity_interval_mass (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp : 99 / 100 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (i : Bool) {r : ℝ} (hr : 0 < r) :
    1 - 2 * (1 - (p : ℝ)) / r ^ 2 ≤
      ∫ x in Set.Icc (boolIndicator i - stationaryProbability p - r)
        (boolIndicator i - stationaryProbability p + r), censusDensity p i x := by
  rw [← density_measureReal_eq_integral _ (censusDensity_continuous p hc hp1 i).measurable
    (censusDensity_nonneg p hc hp1 i) (censusLimitLaw_eq_withDensity p hc hp1 i) measurableSet_Icc]
  have ht := censusLimitLaw_chebyshev p hc hp i hr
  have hs : (Set.Icc (boolIndicator i - stationaryProbability p - r)
      (boolIndicator i - stationaryProbability p + r))ᶜ ⊆
      {x | r ≤ |x - (boolIndicator i - stationaryProbability p)|} := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · exact le_trans (by linarith : r ≤ -(x - (boolIndicator i - stationaryProbability p))) (neg_le_abs _)
    · exact le_trans (by linarith : r ≤ x - (boolIndicator i - stationaryProbability p)) (le_abs_self _)
  have hb := (measureReal_mono (μ := censusLimitLaw p i) hs).trans ht
  rw [probReal_compl_eq_one_sub measurableSet_Icc] at hb
  linarith

end SphericalTreeFailures
