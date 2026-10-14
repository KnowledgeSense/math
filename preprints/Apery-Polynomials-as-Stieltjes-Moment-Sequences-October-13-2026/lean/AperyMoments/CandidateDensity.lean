import AperyMoments.EllipticReal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
open Set MeasureTheory
namespace AperyMoments

/-- The source's positive continuation of the real part of the elliptic integral. -/
def ellipticKappa (m : ℝ) : ℝ :=
  if m ≤ 1 then ellipticK m else m ^ (-(1 / 2 : ℝ)) * ellipticK m⁻¹

/-- The untruncated square-lattice density expression. -/
def latticeExpression (z : ℝ) : ℝ := ellipticK (1 - z ^ 2 / 16) / (2 * Real.pi ^ 2)

/-- The actual compact square-lattice density, with irrelevant singular-point values totalized. -/
def latticeDensity (z : ℝ) : ℝ := if |z| < 4 then latticeExpression z else 0

/-- Angular form of the arcsine convolution appearing in the source. -/
def spectralDensity (b w : ℝ) : ℝ :=
  (Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..Real.pi, latticeDensity (w - b * Real.cos θ)

/-- The positive, untruncated counterpart of the same convolution. -/
def continuedDensity (b w : ℝ) : ℝ :=
  (Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..Real.pi, latticeExpression (w - b * Real.cos θ)

/-- The real nonnegative continuation correction on the lower support branch. -/
def continuationCorrection (b w : ℝ) : ℝ :=
  (Real.pi ^ 3)⁻¹ * ∫ u in b..w,
    ellipticKappa ((w - u) ^ 2 / 16) / Real.sqrt (u ^ 2 - b ^ 2)

/-- The source reciprocal quadratic map. -/
def reciprocalRadius (α s : ℝ) : ℝ := Real.sqrt s + α / Real.sqrt s

/-- The source's compact upper endpoint. -/
def supportEndpoint (α : ℝ) : ℝ :=
  (((4 + 2 * Real.sqrt α) + Real.sqrt ((4 + 2 * Real.sqrt α) ^ 2 - 4 * α)) / 2) ^ 2

/-- The explicit two-branch candidate density. Its moment identity remains to be proved. -/
def candidateDensity (α s : ℝ) : ℝ :=
  if 0 < s ∧ s < supportEndpoint α ∧ s ≠ α then
    let b := 2 * Real.sqrt α
    let w := reciprocalRadius α s
    if α < s then spectralDensity b w / Real.sqrt s
    else (2 * continuedDensity b w - spectralDensity b w +
      2 * continuationCorrection b w) / Real.sqrt s
  else 0

theorem ellipticK_nonneg {m : ℝ} (hm : m ≤ 1) : 0 ≤ ellipticK m := by
  apply intervalIntegral.integral_nonneg (by positivity)
  intro θ _
  apply Real.rpow_nonneg
  have hs := Real.sin_sq_le_one θ
  by_cases hm0 : 0 ≤ m
  · nlinarith [mul_le_mul_of_nonneg_left hs hm0]
  · have h := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hm0) (sq_nonneg (Real.sin θ))
    linarith

theorem ellipticKappa_nonneg {m : ℝ} (hm : 0 ≤ m) : 0 ≤ ellipticKappa m := by
  unfold ellipticKappa
  split_ifs with h
  · exact ellipticK_nonneg h
  · have hm1 : 1 < m := lt_of_not_ge h
    exact mul_nonneg (Real.rpow_nonneg hm _) (ellipticK_nonneg (by
      rw [inv_le_one₀ (by positivity)]
      exact hm1.le))

theorem latticeExpression_nonneg (z : ℝ) : 0 ≤ latticeExpression z :=
  div_nonneg (ellipticK_nonneg (by nlinarith [sq_nonneg z])) (by positivity)

theorem latticeDensity_nonneg (z : ℝ) : 0 ≤ latticeDensity z := by
  unfold latticeDensity
  split_ifs
  · exact latticeExpression_nonneg z
  · rfl

theorem latticeDensity_le_expression (z : ℝ) : latticeDensity z ≤ latticeExpression z := by
  unfold latticeDensity
  split_ifs
  · rfl
  · exact latticeExpression_nonneg z

theorem spectralDensity_nonneg (b w : ℝ) : 0 ≤ spectralDensity b w := by
  apply mul_nonneg (by positivity)
  exact intervalIntegral.integral_nonneg Real.pi_pos.le (fun θ _ => latticeDensity_nonneg _)

theorem continuedDensity_nonneg (b w : ℝ) : 0 ≤ continuedDensity b w := by
  apply mul_nonneg (by positivity)
  exact intervalIntegral.integral_nonneg Real.pi_pos.le (fun θ _ => latticeExpression_nonneg _)

theorem continuationCorrection_nonneg {b w : ℝ} (hbw : b ≤ w) :
    0 ≤ continuationCorrection b w := by
  apply mul_nonneg (by positivity)
  apply intervalIntegral.integral_nonneg hbw
  intro u _
  exact div_nonneg (ellipticKappa_nonneg (by positivity)) (Real.sqrt_nonneg _)

theorem latticeExpression_continuousOn : ContinuousOn latticeExpression (Ioi 0) := by
  apply ContinuousOn.div_const
  apply ellipticK_continuousOn.comp (by fun_prop)
  intro z hz
  change 1 - z ^ 2 / 16 < 1
  nlinarith [sq_pos_of_pos (show 0 < z from hz)]

theorem shifted_latticeExpression_continuous {b w : ℝ} (hb : 0 ≤ b) (hbw : b < w) :
    Continuous (fun θ : ℝ => latticeExpression (w - b * Real.cos θ)) := by
  apply latticeExpression_continuousOn.comp_continuous (by fun_prop)
  intro θ
  change 0 < w - b * Real.cos θ
  nlinarith [mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hb]

theorem spectralDensity_le_continued {b w : ℝ} (hb : 0 ≤ b) (hbw : b < w) :
    spectralDensity b w ≤ continuedDensity b w := by
  have hc := shifted_latticeExpression_continuous hb hbw
  have hi := hc.intervalIntegrable (μ := volume) 0 Real.pi
  have hm : Measurable (fun θ : ℝ => latticeDensity (w - b * Real.cos θ)) := by
    apply Measurable.ite
    · exact measurableSet_lt (by fun_prop) measurable_const
    · exact hc.measurable
    · exact measurable_const
  have hs : IntervalIntegrable (fun θ : ℝ => latticeDensity (w - b * Real.cos θ))
      volume 0 Real.pi := hi.mono_fun hm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun θ => by
          dsimp only
          rw [Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (latticeDensity_nonneg _), abs_of_nonneg (latticeExpression_nonneg _)]
          exact latticeDensity_le_expression _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact intervalIntegral.integral_mono Real.pi_pos.le hs hi (fun θ => latticeDensity_le_expression _)

theorem reciprocalRadius_gt {α s : ℝ} (hα : 0 ≤ α) (hs : 0 < s) (hne : s ≠ α) :
    2 * Real.sqrt α < reciprocalRadius α s := by
  have hsa := Real.sq_sqrt hα
  have hss := Real.sq_sqrt hs.le
  have hsp := Real.sqrt_pos.mpr hs
  have hne' : Real.sqrt s - Real.sqrt α ≠ 0 := by
    intro h
    apply hne
    nlinarith
  have he : reciprocalRadius α s * Real.sqrt s = s + α := by
    unfold reciprocalRadius
    rw [add_mul, div_mul_cancel₀ _ hsp.ne']
    nlinarith
  nlinarith [sq_pos_of_ne_zero hne']

/-- Positivity of the explicit candidate. Normalization and all-moment reconstruction
are separate analytic obligations and are not inferred from this lemma. -/
theorem candidateDensity_nonneg {α : ℝ} (hα : 0 ≤ α) (s : ℝ) :
    0 ≤ candidateDensity α s := by
  unfold candidateDensity
  split_ifs with hs hhigh
  · exact div_nonneg (spectralDensity_nonneg _ _) (Real.sqrt_nonneg _)
  · have hbw := reciprocalRadius_gt hα hs.1 hs.2.2
    have hh := spectralDensity_le_continued (by positivity : 0 ≤ 2 * Real.sqrt α) hbw
    have ht := continuedDensity_nonneg (2 * Real.sqrt α) (reciprocalRadius α s)
    have hj := continuationCorrection_nonneg hbw.le
    apply div_nonneg _ (Real.sqrt_nonneg _)
    linarith
  · rfl

end AperyMoments
