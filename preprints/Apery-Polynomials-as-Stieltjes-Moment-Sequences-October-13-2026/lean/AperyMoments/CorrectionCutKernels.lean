import AperyMoments.CorrectionCutBounds
import AperyMoments.LowerEllipticScaled

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def correctionFirstKernel (b : ℝ) (w : ℂ) (v : ℝ) : ℂ :=
  ((correctionCutScale b w)⁻¹ : ℝ) •
    (correctionRegular b w (v / correctionCutScale b w) * (correctionWeight (v / correctionCutScale b w) : ℂ))

def correctionSecondPoint (b : ℝ) (w : ℂ) (v : ℝ) : ℝ :=
  (1 + (correctionCutScale b w - 1) * v) / correctionCutScale b w

def correctionSecondKernel (b : ℝ) (w : ℂ) (v : ℝ) : ℂ :=
  (1 - (correctionCutScale b w)⁻¹ : ℝ) •
    (correctionRegular b w (correctionSecondPoint b w v) * (correctionWeight (correctionSecondPoint b w v) : ℂ))

theorem correctionFirstPoint_mem {b : ℝ} {w : ℂ} (hA : 1 < correctionCutScale b w)
    {v : ℝ} (hv : v ∈ Ioo 0 1) : v / correctionCutScale b w ∈ Ioo 0 1 := by
  constructor
  · exact div_pos hv.1 (by linarith)
  · apply (div_lt_one (by linarith : 0 < correctionCutScale b w)).mpr
    linarith [hv.2]

theorem correctionSecondPoint_mem {b : ℝ} {w : ℂ} (hA : 1 < correctionCutScale b w)
    {v : ℝ} (hv : v ∈ Ioo 0 1) : correctionSecondPoint b w v ∈ Ioo 0 1 := by
  have hA0 : 0 < correctionCutScale b w := by linarith
  unfold correctionSecondPoint
  constructor
  · exact div_pos (by nlinarith [mul_pos (by linarith : 0 < correctionCutScale b w - 1) hv.1]) hA0
  · apply (div_lt_one hA0).mpr
    nlinarith [hv.2]

theorem correctionSecondPoint_weight_argument (b : ℝ) {w : ℂ}
    (hA : correctionCutScale b w ≠ 0) (v : ℝ) :
    1 - correctionSecondPoint b w v =
      ((correctionCutScale b w - 1) / correctionCutScale b w) * (1 - v) := by
  unfold correctionSecondPoint
  field_simp
  ring

theorem correctionBase_right_bound {b v : ℝ} (hb : 0 < b) {w : ℂ} (hw : b ≤ w.re)
    (hv : v ∈ Icc 0 1) :
    ‖correctionBase b w v ^ (-(1 / 2 : ℂ))‖ ≤ (2 * b) ^ (-(1 / 2 : ℝ)) := by
  apply inverse_sqrt_cpow_bound_re (by positivity)
  unfold correctionBase
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero]
  nlinarith [mul_nonneg (sub_nonneg.mpr hw) (sub_nonneg.mpr hv.2)]

theorem correctionFirst_weight_bound {b δ M : ℝ} (hδ : 0 < δ) {w : ℂ}
    (hscale : δ ≤ correctionCutScale b w - 1) (hM : correctionCutScale b w ≤ M)
    {v : ℝ} (hv : v ∈ Icc 0 1) :
    correctionWeight (v / correctionCutScale b w) ≤ (δ / M) ^ (-(1 / 2 : ℝ)) := by
  have hA : 0 < correctionCutScale b w := by linarith
  have hM0 : 0 < M := hA.trans_le hM
  have hratio : δ / M ≤ (correctionCutScale b w - 1) / correctionCutScale b w := by
    apply (div_le_div_iff₀ hM0 hA).mpr
    nlinarith [mul_le_mul_of_nonneg_left hM hδ.le, mul_le_mul_of_nonneg_right hscale hM0.le]
  have hbase : δ / M ≤ 1 - v / correctionCutScale b w := by
    have hsmall := (div_le_div_of_nonneg_right hv.2 hA.le)
    have he : (correctionCutScale b w - 1) / correctionCutScale b w = 1 - 1 / correctionCutScale b w := by field_simp
    rw [he] at hratio
    linarith
  exact Real.rpow_le_rpow_of_nonpos (div_pos hδ hM0) hbase (by norm_num)

theorem correctionSecond_weight_bound {b δ M : ℝ} (hδ : 0 < δ) {w : ℂ}
    (hscale : δ ≤ correctionCutScale b w - 1) (hM : correctionCutScale b w ≤ M)
    {v : ℝ} (hv : v ∈ Ioo 0 1) :
    correctionWeight (correctionSecondPoint b w v) ≤
      (δ / M) ^ (-(1 / 2 : ℝ)) * (1 - v) ^ (-(1 / 2 : ℝ)) := by
  have hA : 0 < correctionCutScale b w := by linarith
  have hM0 : 0 < M := hA.trans_le hM
  have hk : 0 < (correctionCutScale b w - 1) / correctionCutScale b w := div_pos (hδ.trans_le hscale) hA
  have hratio : δ / M ≤ (correctionCutScale b w - 1) / correctionCutScale b w := by
    apply (div_le_div_iff₀ hM0 hA).mpr
    nlinarith [mul_le_mul_of_nonneg_left hM hδ.le, mul_le_mul_of_nonneg_right hscale hM0.le]
  unfold correctionWeight
  rw [correctionSecondPoint_weight_argument b hA.ne', Real.mul_rpow hk.le (by linarith [hv.2])]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith [hv.2]) _)
  exact Real.rpow_le_rpow_of_nonpos (div_pos hδ hM0) hratio (by norm_num)

def correctionCutFirstBound (b δ M : ℝ) : ℝ :=
  (Real.pi / 2) * (2 * b) ^ (-(1 / 2 : ℝ)) * (δ / M) ^ (-(1 / 2 : ℝ))

def correctionCutSecondBound (b δ M : ℝ) : ℝ :=
  correctionCutFirstBound b δ M * (δ ^ (-(1 / 2 : ℝ)) + 1)

theorem correctionFirstKernel_bound {b δ M : ℝ} (hb : 0 < b) (hδ : 0 < δ) {w : ℂ}
    (hw : b < w.re) (hscale : δ ≤ correctionCutScale b w - 1) (hM : correctionCutScale b w ≤ M)
    {v : ℝ} (hv : v ∈ Ioo 0 1) :
    ‖correctionFirstKernel b w v‖ ≤ correctionCutFirstBound b δ M * correctionWeight v := by
  have hv0 : 0 < v := hv.1
  have hv1 : 0 < 1 - v := by linarith [hv.2]
  have hA : 1 < correctionCutScale b w := by linarith
  have hA0 : 0 < correctionCutScale b w := by linarith
  have hM0 : 0 < M := hA0.trans_le hM
  have hp := correctionFirstPoint_mem hA hv
  have hraw : 0 < (w.re - b) ^ 2 - w.im ^ 2 := by
    have hs : 0 < Real.sqrt ((w.re - b) ^ 2 - w.im ^ 2) := by
      dsimp [correctionCutScale] at hA0
      linarith
    exact Real.sqrt_pos.mp hs
  have hK := correctionCut_first_elliptic_bound hraw hv
  have hB := correctionBase_right_bound hb hw.le ⟨hp.1.le, hp.2.le⟩
  have hW := correctionFirst_weight_bound hδ hscale hM ⟨hv.1.le, hv.2.le⟩
  have hwgt : 0 ≤ correctionWeight (v / correctionCutScale b w) :=
    Real.rpow_nonneg (by linarith [hp.2]) _
  have hcoeff : (correctionCutScale b w)⁻¹ ≤ 1 := (inv_le_one₀ hA0).mpr hA.le
  have hreg : ‖correctionRegular b w (v / correctionCutScale b w)‖ ≤
      ((Real.pi / 2) * (1 - v) ^ (-(1 / 2 : ℝ))) * (2 * b) ^ (-(1 / 2 : ℝ)) := by
    unfold correctionRegular
    rw [norm_mul]
    exact mul_le_mul hK hB (norm_nonneg _) (by positivity)
  unfold correctionFirstKernel
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hA0), norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwgt]
  calc
    _ ≤ ‖correctionRegular b w (v / correctionCutScale b w)‖ * correctionWeight (v / correctionCutScale b w) := by
      exact (mul_le_mul_of_nonneg_right hcoeff (mul_nonneg (norm_nonneg _) hwgt)).trans_eq (one_mul _)
    _ ≤ (((Real.pi / 2) * (1 - v) ^ (-(1 / 2 : ℝ))) * (2 * b) ^ (-(1 / 2 : ℝ))) *
        (δ / M) ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul hreg hW hwgt (by positivity)
    _ = _ := by unfold correctionCutFirstBound correctionWeight; ring

theorem correctionSecondKernel_bound {b δ M : ℝ} (hb : 0 < b) (hδ : 0 < δ) {w : ℂ}
    (hwim : w.im < 0) (hw : b < w.re) (hscale : δ ≤ correctionCutScale b w - 1)
    (hM : correctionCutScale b w ≤ M) {v : ℝ} (hv : v ∈ Ioo 0 1) :
    ‖correctionSecondKernel b w v‖ ≤ correctionCutSecondBound b δ M * correctionCutEndpointWeight v := by
  have hv0 : 0 < v := hv.1
  have hv1 : 0 < 1 - v := by linarith [hv.2]
  have hA : 1 < correctionCutScale b w := by linarith
  have hA0 : 0 < correctionCutScale b w := by linarith
  have hM0 : 0 < M := hA0.trans_le hM
  have hp := correctionSecondPoint_mem hA hv
  have hK := correctionCut_second_elliptic_bound hδ hwim hw hscale hv
  have hB := correctionBase_right_bound hb hw.le ⟨hp.1.le, hp.2.le⟩
  have hW := correctionSecond_weight_bound hδ hscale hM hv
  have hwgt : 0 ≤ correctionWeight (correctionSecondPoint b w v) :=
    Real.rpow_nonneg (by linarith [hp.2]) _
  have hcoeff0 : 0 < 1 - (correctionCutScale b w)⁻¹ := by
    have := (inv_lt_one₀ hA0).mpr hA
    linarith
  have hcoeff : 1 - (correctionCutScale b w)⁻¹ ≤ 1 := by linarith [inv_pos.mpr hA0]
  have hreg : ‖correctionRegular b w (correctionSecondPoint b w v)‖ ≤
      (((Real.pi / 2) * (δ ^ (-(1 / 2 : ℝ)) + 1)) * v ^ (-(1 / 2 : ℝ))) *
        (2 * b) ^ (-(1 / 2 : ℝ)) := by
    unfold correctionRegular
    rw [norm_mul]
    exact mul_le_mul hK hB (norm_nonneg _) (by positivity)
  unfold correctionSecondKernel
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcoeff0, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwgt]
  calc
    _ ≤ ‖correctionRegular b w (correctionSecondPoint b w v)‖ * correctionWeight (correctionSecondPoint b w v) := by
      exact (mul_le_mul_of_nonneg_right hcoeff (mul_nonneg (norm_nonneg _) hwgt)).trans_eq (one_mul _)
    _ ≤ ((((Real.pi / 2) * (δ ^ (-(1 / 2 : ℝ)) + 1)) * v ^ (-(1 / 2 : ℝ))) *
        (2 * b) ^ (-(1 / 2 : ℝ))) *
        ((δ / M) ^ (-(1 / 2 : ℝ)) * (1 - v) ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul hreg hW hwgt (by positivity)
    _ = _ := by unfold correctionCutSecondBound correctionCutFirstBound correctionCutEndpointWeight; ring

end AperyMoments
