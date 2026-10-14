import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic

namespace ResearchMain.WishartBlocks

open MeasureTheory Filter Set
open scoped BigOperators Topology

def realStrip (δ : ℝ) : Set ℂ := {z | |z.re| < δ}

theorem realStrip_open (δ : ℝ) : IsOpen (realStrip δ) :=
  isOpen_lt (Complex.continuous_re.abs) continuous_const

theorem realStrip_preconnected (δ : ℝ) : IsPreconnected (realStrip δ) := by
  have he : realStrip δ = Complex.reCLM ⁻¹' Set.Ioo (-δ) δ := by
    ext z
    simp [realStrip, abs_lt]
  rw [he]
  exact ((convex_Ioo (-δ) δ).linear_preimage Complex.reCLM.toLinearMap).isPreconnected

theorem analytic_real_interval_zero {δ : ℝ} (hδ : 0 < δ) {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (realStrip δ))
    (hzero : ∀ t : ℝ, |t| < δ → F t = 0) :
    Set.EqOn F 0 (realStrip δ) := by
  have h0 : (0 : ℂ) ∈ realStrip δ := by simpa [realStrip] using hδ
  apply hF.eqOn_zero_of_preconnected_of_mem_closure (realStrip_preconnected δ) h0
  apply Metric.mem_closure_iff.mpr
  intro ρ hρ
  let t := min δ ρ / 2
  have ht : 0 < t := by dsimp [t]; exact half_pos (lt_min hδ hρ)
  have htδ : t < δ := by dsimp [t]; nlinarith [min_le_left δ ρ]
  have htρ : t < ρ := by dsimp [t]; nlinarith [min_le_right δ ρ]
  refine ⟨(t : ℂ), ⟨hzero t (by rwa [abs_of_pos ht]), ?_⟩, ?_⟩
  · simpa only [Set.mem_singleton_iff, Complex.ofReal_eq_zero] using ht.ne'
  · simpa only [dist_zero_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] using htρ

noncomputable def weightedLaplace {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (a b : X → ℝ) (c : X → ℂ) (z : ℂ) : ℂ :=
  ∫ w, c w * Complex.exp (-(a w : ℂ) - z * (b w : ℂ)) ∂μ

theorem laplace_strip_kernel_bound {δ a b : ℝ} (_hδ : 0 < δ)
    (hab : δ * |b| ≤ a) {z : ℂ} (hz : z ∈ realStrip δ) :
    ‖Complex.exp (-(a : ℂ) - z * (b : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  have hb := (neg_le_abs (z.re * b)).trans_eq (abs_mul z.re b)
  have hm : |z.re| * |b| ≤ δ * |b| :=
    mul_le_mul_of_nonneg_right hz.le (abs_nonneg b)
  linarith

theorem weightedLaplace_integrable {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {a b : X → ℝ} {c : X → ℂ} (ha : Measurable a) (hb : Measurable b)
    (hc : Measurable c) (hi : Integrable c μ) {δ : ℝ} (hδ : 0 < δ)
    (hab : ∀ᵐ w ∂μ, δ * |b w| ≤ a w) {z : ℂ} (hz : z ∈ realStrip δ) :
    Integrable (fun w => c w * Complex.exp (-(a w : ℂ) - z * (b w : ℂ))) μ := by
  apply hi.norm.mono' (by fun_prop)
  filter_upwards [hab] with w hw
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (laplace_strip_kernel_bound hδ hw hz)
    (norm_nonneg _)).trans_eq (mul_one _)

theorem weightedLaplace_hasDerivAt {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {a b : X → ℝ} {c : X → ℂ} (ha : Measurable a) (hb : Measurable b)
    (hc : Measurable c) (hi : Integrable c μ)
    (hbi : Integrable (fun w => |b w| * ‖c w‖) μ)
    {δ : ℝ} (hδ : 0 < δ) (hab : ∀ᵐ w ∂μ, δ * |b w| ≤ a w)
    {z : ℂ} (hz : z ∈ realStrip δ) :
    HasDerivAt (weightedLaplace μ a b c)
      (∫ w, c w * (-(b w : ℂ)) *
        Complex.exp (-(a w : ℂ) - z * (b w : ℂ)) ∂μ) z := by
  let F := fun z : ℂ => fun w : X =>
    c w * Complex.exp (-(a w : ℂ) - z * (b w : ℂ))
  let F' := fun z : ℂ => fun w : X =>
    c w * (-(b w : ℂ)) * Complex.exp (-(a w : ℂ) - z * (b w : ℂ))
  have hF (u : ℂ) : AEStronglyMeasurable (F u) μ := by dsimp [F]; fun_prop
  have hF' : AEStronglyMeasurable (F' z) μ := by dsimp [F']; fun_prop
  have hbound : ∀ᵐ w ∂μ, ∀ u ∈ realStrip δ, ‖F' u w‖ ≤ |b w| * ‖c w‖ := by
    filter_upwards [hab] with w hw
    intro u hu
    dsimp [F']
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ ‖c w‖ * |b w| * 1 :=
        mul_le_mul_of_nonneg_left (laplace_strip_kernel_bound hδ hw hu) (by positivity)
      _ = _ := by ring
  have hdiff : ∀ᵐ w ∂μ, ∀ u ∈ realStrip δ, HasDerivAt (fun u => F u w) (F' u w) u :=
    ae_of_all _ fun w u _ => by
      have he := (Complex.hasDerivAt_exp (-(a w : ℂ) - u * (b w : ℂ))).comp u
        ((hasDerivAt_const u (-(a w : ℂ))).sub ((hasDerivAt_id' u).mul_const (b w : ℂ)))
      convert (hasDerivAt_const u (c w)).mul he using 1
      · funext z; dsimp [F]
      · dsimp [F']; ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    ((realStrip_open δ).mem_nhds hz) (Filter.Eventually.of_forall hF)
    (weightedLaplace_integrable ha hb hc hi hδ hab hz) hF' hbound hbi hdiff).2

theorem weightedLaplace_analyticOnNhd {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {a b : X → ℝ} {c : X → ℂ} (ha : Measurable a) (hb : Measurable b)
    (hc : Measurable c) (hi : Integrable c μ)
    (hbi : Integrable (fun w => |b w| * ‖c w‖) μ)
    {δ : ℝ} (hδ : 0 < δ) (hab : ∀ᵐ w ∂μ, δ * |b w| ≤ a w) :
    AnalyticOnNhd ℂ (weightedLaplace μ a b c) (realStrip δ) := by
  apply DifferentiableOn.analyticOnNhd _ (realStrip_open δ)
  intro z hz
  exact (weightedLaplace_hasDerivAt ha hb hc hi hbi hδ hab hz).differentiableAt.differentiableWithinAt

theorem polynomial_weightedLaplace_imaginary_zero {X ι : Type*} [MeasurableSpace X]
    [Fintype ι] {μ : Measure X} {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b)
    (c : ι → X → ℂ) (P : ι → Polynomial ℂ)
    (hc : ∀ i, Measurable (c i)) (hi : ∀ i, Integrable (c i) μ)
    (hbi : ∀ i, Integrable (fun w => |b w| * ‖c i w‖) μ)
    {δ : ℝ} (hδ : 0 < δ) (hab : ∀ᵐ w ∂μ, δ * |b w| ≤ a w)
    (hzero : ∀ t : ℝ, |t| < δ →
      (∑ i, (P i).eval (t : ℂ) * weightedLaplace μ a b (c i) t) = 0)
    (y : ℝ) :
    (∑ i, (P i).eval (Complex.I * y) *
      weightedLaplace μ a b (c i) (Complex.I * y)) = 0 := by
  have hF : AnalyticOnNhd ℂ
      (fun z => ∑ i, (P i).eval z * weightedLaplace μ a b (c i) z) (realStrip δ) := by
    apply DifferentiableOn.analyticOnNhd _ (realStrip_open δ)
    apply DifferentiableOn.fun_sum
    intro i _
    exact (P i).differentiableOn.mul
      (weightedLaplace_analyticOnNhd ha hb (hc i) (hi i) (hbi i) hδ hab).differentiableOn
  apply analytic_real_interval_zero hδ hF hzero
  simpa [realStrip] using hδ

end ResearchMain.WishartBlocks

