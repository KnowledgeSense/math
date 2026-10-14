import SphericalTreeFailures.DensityScaling

/-! # Everywhere positivity from the actual independent-child fixed points -/
namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem censusLimitLaw_scaled_convolution (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (i : Bool) :
    censusLimitLaw p i = ((descendantLaw p i) ∗ (descendantLaw p i)).map
      (fun x : ℝ => -(censusScale p)⁻¹ * x) := by
  rw [censusLimitLaw_fixedPoint p hc i, Measure.conv,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  dsimp
  ring

theorem censusDensity_one_pos (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) (x : ℝ) : 0 < censusDensity p true x := by
  rw [censusDensity_eq_characteristicDensity, censusLimitLaw_scaled_convolution p hc true]
  change 0 < characteristicDensity ((censusLimitLaw p false ∗ censusLimitLaw p false).map
    (fun y : ℝ => -(censusScale p)⁻¹ * y)) x
  have hg : censusScale p ≠ 0 := ne_of_gt ((by linarith [censusScale_gt_one p hc]) : 0 < censusScale p)
  rw [characteristicDensity_map_mul _ (neg_ne_zero.mpr (inv_ne_zero hg)),
    characteristicDensity_conv _ (censusCharacteristic_integrable p hc hp1 false)]
  apply mul_pos (abs_pos.mpr (inv_ne_zero (neg_ne_zero.mpr (inv_ne_zero hg))))
  rw [← censusDensity_eq_characteristicDensity]
  apply densityConvolution_pos_of_dense_support
    (censusDensity_continuous p hc hp1 false) (censusDensity_integrable p hc hp1 false)
    _ (censusDensity_nonneg p hc hp1 false) (censusDensity_dense_support p hc hp1 false)
  rw [censusDensity_eq_characteristicDensity]
  exact characteristicDensity_norm_bddAbove _ (censusCharacteristic_integrable p hc hp1 false)

noncomputable def censusMixtureDensity (p : unitInterval) (x : ℝ) : ℝ :=
  (1 - (p : ℝ)) * censusDensity p false x + (p : ℝ) * censusDensity p true x

theorem censusMixtureCharacteristic_integrable (p : unitInterval)
    (hc : 1 < 2 * (p : ℝ) ^ 2) (hp1 : (p : ℝ) < 1) : Integrable (censusMixtureCharacteristic p) := by
  have he : censusMixtureCharacteristic p = fun t =>
      (((1 - (p : ℝ) : ℝ) : ℂ) * censusCharacteristic p false t) +
      ((p : ℂ) * censusCharacteristic p true t) := funext (censusMixtureCharacteristic_eq p)
  rw [he]
  exact ((censusCharacteristic_integrable p hc hp1 false).const_mul _).add
    ((censusCharacteristic_integrable p hc hp1 true).const_mul _)

theorem censusMixtureDensity_nonneg (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) (x : ℝ) : 0 ≤ censusMixtureDensity p x :=
  add_nonneg (mul_nonneg (sub_nonneg.mpr p.property.2) (censusDensity_nonneg p hc hp1 false x))
    (mul_nonneg p.property.1 (censusDensity_nonneg p hc hp1 true x))

theorem censusMixtureDensity_pos (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) (x : ℝ) : 0 < censusMixtureDensity p x :=
  add_pos_of_nonneg_of_pos
    (mul_nonneg (sub_nonneg.mpr p.property.2) (censusDensity_nonneg p hc hp1 false x))
    (mul_pos (by nlinarith [p.property.1] : 0 < (p : ℝ)) (censusDensity_one_pos p hc hp1 x))

theorem censusMixtureDensity_continuous (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) : Continuous (censusMixtureDensity p) :=
  (continuous_const.mul (censusDensity_continuous p hc hp1 false)).add
    (continuous_const.mul (censusDensity_continuous p hc hp1 true))

theorem withDensity_linear_combination {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    volume.withDensity (fun x => ENNReal.ofReal (a * f x + b * g x)) =
      ENNReal.ofReal a • volume.withDensity (fun x => ENNReal.ofReal (f x)) +
      ENNReal.ofReal b • volume.withDensity (fun x => ENNReal.ofReal (g x)) := by
  simp_rw [ENNReal.ofReal_add (mul_nonneg ha (hfn _)) (mul_nonneg hb (hgn _)),
    ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]
  change volume.withDensity ((ENNReal.ofReal a) • (fun x => ENNReal.ofReal (f x)) +
      (ENNReal.ofReal b) • (fun x => ENNReal.ofReal (g x))) = _
  have ham : Measurable ((ENNReal.ofReal a) • (fun x => ENNReal.ofReal (f x))) :=
    measurable_const.mul hf.ennreal_ofReal
  rw [withDensity_add_left ham,
    withDensity_smul _ hf.ennreal_ofReal, withDensity_smul _ hg.ennreal_ofReal]

theorem censusMixtureLaw_eq_withDensity (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) :
    censusMixtureLaw p = volume.withDensity (fun x => ENNReal.ofReal (censusMixtureDensity p x)) := by
  unfold censusMixtureDensity
  rw [withDensity_linear_combination
    (censusDensity_continuous p hc hp1 false).measurable
    (censusDensity_continuous p hc hp1 true).measurable
    (censusDensity_nonneg p hc hp1 false) (censusDensity_nonneg p hc hp1 true)
    (sub_nonneg.mpr p.property.2) p.property.1,
    ← censusLimitLaw_eq_withDensity p hc hp1 false, ← censusLimitLaw_eq_withDensity p hc hp1 true]
  rfl

theorem censusMixtureDensity_eq_characteristicDensity (p : unitInterval)
    (hc : 1 < 2 * (p : ℝ) ^ 2) (hp1 : (p : ℝ) < 1) :
    censusMixtureDensity p = characteristicDensity (censusMixtureLaw p) := by
  apply continuous_density_unique (censusMixtureDensity_continuous p hc hp1)
    (characteristicDensity_continuous _ (censusMixtureCharacteristic_integrable p hc hp1))
    (censusMixtureDensity_nonneg p hc hp1)
    (characteristicDensity_nonneg _ (censusMixtureCharacteristic_integrable p hc hp1))
  rw [← censusMixtureLaw_eq_withDensity p hc hp1,
    ← measure_eq_withDensity_characteristicDensity _ (censusMixtureCharacteristic_integrable p hc hp1)]

theorem censusDensity_zero_pos (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) (x : ℝ) : 0 < censusDensity p false x := by
  rw [censusDensity_eq_characteristicDensity, censusLimitLaw_scaled_convolution p hc false]
  change 0 < characteristicDensity ((censusMixtureLaw p ∗ censusMixtureLaw p).map
    (fun y : ℝ => -(censusScale p)⁻¹ * y)) x
  have hg : censusScale p ≠ 0 := ne_of_gt ((by linarith [censusScale_gt_one p hc]) : 0 < censusScale p)
  rw [characteristicDensity_map_mul _ (neg_ne_zero.mpr (inv_ne_zero hg)),
    characteristicDensity_conv _ (censusMixtureCharacteristic_integrable p hc hp1)]
  apply mul_pos (abs_pos.mpr (inv_ne_zero (neg_ne_zero.mpr (inv_ne_zero hg))))
  apply densityConvolution_pos_of_dense_support
    (characteristicDensity_continuous _ (censusMixtureCharacteristic_integrable p hc hp1))
    (characteristicDensity_integrable _ (censusMixtureCharacteristic_integrable p hc hp1))
    (characteristicDensity_norm_bddAbove _ (censusMixtureCharacteristic_integrable p hc hp1))
    (characteristicDensity_nonneg _ (censusMixtureCharacteristic_integrable p hc hp1))
  have he : Function.support (characteristicDensity (censusMixtureLaw p)) = Set.univ := by
    ext y
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    rw [← censusMixtureDensity_eq_characteristicDensity p hc hp1]
    exact ne_of_gt (censusMixtureDensity_pos p hc hp1 y)
  rw [he]
  exact dense_univ

theorem censusDensity_pos (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) (i : Bool) (x : ℝ) : 0 < censusDensity p i x := by
  cases i
  · exact censusDensity_zero_pos p hc hp1 x
  · exact censusDensity_one_pos p hc hp1 x

end SphericalTreeFailures
