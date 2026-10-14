import SphericalTreeFailures.CensusDensity
import Mathlib.Analysis.Convolution

/-! # Continuous density convolution and strict positivity -/
namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory
open scoped ENNReal Convolution FourierTransform

theorem characteristicDensity_norm_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (charFun μ)) (x : ℝ) :
    ‖characteristicDensity μ x‖ ≤ (2 * Real.pi)⁻¹ * ∫ t, ‖charFun μ t‖ := by
  rw [Real.norm_eq_abs, abs_of_nonneg (characteristicDensity_nonneg μ hint x)]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (2 * Real.pi)⁻¹)
  exact (Complex.re_le_norm _).trans
    (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _)

theorem characteristicDensity_norm_bddAbove (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (charFun μ)) :
    BddAbove (Set.range (fun x => ‖characteristicDensity μ x‖)) := by
  refine ⟨(2 * Real.pi)⁻¹ * ∫ t, ‖charFun μ t‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact characteristicDensity_norm_bound μ hint x

noncomputable def densityConvolution (f g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y, f y * g (x - y)

theorem densityConvolution_integrable_at {f g : ℝ → ℝ} (hf : Integrable f)
    (hg : Continuous g) (hb : BddAbove (Set.range fun x => ‖g x‖)) (x : ℝ) :
    Integrable (fun y => f y * g (x - y)) := by
  obtain ⟨C, hC⟩ := hb
  exact hf.mul_bdd (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun y => hC ⟨x - y, rfl⟩)

theorem densityConvolution_continuous {f g : ℝ → ℝ} (hf : Integrable f)
    (hg : Continuous g) (hb : BddAbove (Set.range fun x => ‖g x‖)) :
    Continuous (densityConvolution f g) :=
  hb.continuous_convolution_right_of_integrable (ContinuousLinearMap.lsmul ℝ ℝ) hf hg

theorem densityConvolution_nonneg {f g : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (x : ℝ) : 0 ≤ densityConvolution f g x :=
  integral_nonneg fun y => mul_nonneg (hf y) (hg (x - y))

theorem conv_withDensity_real {f g : ℝ → ℝ} (hfc : Continuous f) (hfi : Integrable f)
    (hgc : Continuous g) (hgb : BddAbove (Set.range fun x => ‖g x‖))
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) :
    (volume.withDensity (fun x => ENNReal.ofReal (f x))) ∗
      (volume.withDensity (fun x => ENNReal.ofReal (g x))) =
      volume.withDensity (fun x => ENNReal.ofReal (densityConvolution f g x)) := by
  rw [conv_withDensity_eq_lconvolution hfc.measurable.ennreal_ofReal hgc.measurable.ennreal_ofReal]
  congr 1
  funext x
  rw [lconvolution_def, densityConvolution,
    ofReal_integral_eq_lintegral_ofReal (densityConvolution_integrable_at hfi hgc hgb x)
      (ae_of_all _ fun y => mul_nonneg (hfn y) (hgn (x - y)))]
  apply lintegral_congr
  intro y
  rw [ENNReal.ofReal_mul (hfn y)]
  congr 2
  ring

theorem continuous_density_unique {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x)
    (he : volume.withDensity (fun x => ENNReal.ofReal (f x)) =
      volume.withDensity (fun x => ENNReal.ofReal (g x))) : f = g := by
  have hae := (withDensity_eq_iff_of_sigmaFinite hf.measurable.ennreal_ofReal.aemeasurable
    hg.measurable.ennreal_ofReal.aemeasurable).mp he
  apply (hf.ae_eq_iff_eq volume hg).mp
  filter_upwards [hae] with x hx
  exact (ENNReal.ofReal_eq_ofReal_iff (hfn x) (hgn x)).mp hx

theorem charFun_conv_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (charFun μ)) : Integrable (charFun (μ ∗ μ)) := by
  have he : charFun (μ ∗ μ) = fun t => charFun μ t * charFun μ t := by
    funext t
    exact charFun_conv t
  rw [he]
  exact hint.mul_bdd continuous_charFun.aestronglyMeasurable (ae_of_all _ norm_charFun_le_one)

theorem characteristicDensity_conv (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (charFun μ)) :
    characteristicDensity (μ ∗ μ) = densityConvolution (characteristicDensity μ) (characteristicDensity μ) := by
  have hc := characteristicDensity_continuous μ hint
  have hi := characteristicDensity_integrable μ hint
  have hb := characteristicDensity_norm_bddAbove μ hint
  have hn := characteristicDensity_nonneg μ hint
  apply continuous_density_unique
    (characteristicDensity_continuous _ (charFun_conv_integrable μ hint))
    (densityConvolution_continuous hi hc hb)
    (characteristicDensity_nonneg _ (charFun_conv_integrable μ hint))
    (densityConvolution_nonneg hn hn)
  rw [← measure_eq_withDensity_characteristicDensity _ (charFun_conv_integrable μ hint)]
  conv_lhs => rw [measure_eq_withDensity_characteristicDensity μ hint]
  exact conv_withDensity_real hc hi hc hb hn hn

/-- Dense positive support of a continuous nonnegative density makes its self-convolution positive. -/
theorem densityConvolution_pos_of_dense_support {f : ℝ → ℝ} (hc : Continuous f)
    (hi : Integrable f) (hb : BddAbove (Set.range fun x => ‖f x‖))
    (hn : ∀ x, 0 ≤ f x) (hd : Dense (Function.support f)) (x : ℝ) :
    0 < densityConvolution f f x := by
  have hdn := hd.preimage (isOpenMap_sub_left x)
  obtain ⟨y, hy, hy'⟩ := hdn.exists_mem_open hc.isOpen_support hd.nonempty
  apply integral_pos_of_integrable_nonneg_nonzero
    (hc.mul (hc.comp (continuous_const.sub continuous_id)))
    (densityConvolution_integrable_at hi hc hb x)
    (fun y => mul_nonneg (hn y) (hn (x - y)))
  exact mul_ne_zero hy' hy

end SphericalTreeFailures
