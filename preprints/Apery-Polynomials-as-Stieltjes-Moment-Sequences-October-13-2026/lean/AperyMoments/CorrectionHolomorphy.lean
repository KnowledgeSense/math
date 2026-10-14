import AperyMoments.CorrectionKernel

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def correctionRegularDerivative (b : ℝ) (w : ℂ) (v : ℝ) : ℂ :=
  (deriv complexEllipticK (correctionParameter b w v) *
    ((w - b) * ((v ^ 2 : ℝ) : ℂ) / 8)) *
      correctionBase b w v ^ (-(1 / 2 : ℂ)) +
  complexEllipticK (correctionParameter b w v) *
    ((-(1 / 2 : ℂ)) * correctionBase b w v ^ (-(1 / 2 : ℂ) - 1) * ((1 - v : ℝ) : ℂ))

theorem correctionParameter_hasDerivAt (b v : ℝ) (w : ℂ) :
    HasDerivAt (fun w => correctionParameter b w v)
      ((w - b) * ((v ^ 2 : ℝ) : ℂ) / 8) w := by
  have h := ((((hasDerivAt_id w).sub_const (b : ℂ)).mul_const (v : ℂ)).div_const 4).pow 2
  convert h using 1
  · rfl
  · simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul, id_eq]
    push_cast
    ring

theorem correctionBase_hasDerivAt (b v : ℝ) (w : ℂ) :
    HasDerivAt (fun w => correctionBase b w v) ((1 - v : ℝ) : ℂ) w := by
  unfold correctionBase
  simpa only [one_mul, id_eq] using
    (((hasDerivAt_id w).mul_const ((1 - v : ℝ) : ℂ)).const_add ((b * (1 + v) : ℝ) : ℂ))

theorem correctionRegular_hasDerivAt {b v : ℝ} (hb : 0 < b) {w : ℂ} (hw : w ∈ correctionDomain b)
    (hv : v ∈ Icc 0 1) :
    HasDerivAt (fun w => correctionRegular b w v) (correctionRegularDerivative b w v) w := by
  have hK := (complexEllipticK_differentiableAt (correctionParameter_mem_domain_of_mem hw hv)).hasDerivAt.comp w
    (correctionParameter_hasDerivAt b v w)
  have hB := (correctionBase_hasDerivAt b v w).cpow_const
    (c := -(1 / 2 : ℂ)) (correctionBase_mem_slitPlane_of_mem hb hw hv)
  exact hK.mul hB

theorem correctionRegularDerivative_continuousOn {b : ℝ} (hb : 0 < b) :
    ContinuousOn (fun p : ℂ × ℝ => correctionRegularDerivative b p.1 p.2)
      (correctionDomain b ×ˢ Icc 0 1) := by
  have hpar : ContinuousOn (fun p : ℂ × ℝ => correctionParameter b p.1 p.2)
      (correctionDomain b ×ˢ Icc 0 1) := by unfold correctionParameter; fun_prop
  have hbase : ContinuousOn (fun p : ℂ × ℝ => correctionBase b p.1 p.2)
      (correctionDomain b ×ˢ Icc 0 1) := by unfold correctionBase; fun_prop
  have hmap : MapsTo (fun p : ℂ × ℝ => correctionParameter b p.1 p.2)
      (correctionDomain b ×ˢ Icc 0 1) ellipticDomain :=
    fun p hp => correctionParameter_mem_domain_of_mem hp.1 hp.2
  have hslit p (hp : p ∈ (correctionDomain b ×ˢ Icc (0 : ℝ) 1)) :=
    correctionBase_mem_slitPlane_of_mem hb hp.1 hp.2
  unfold correctionRegularDerivative
  exact ((complexEllipticK_analyticOnNhd.deriv.continuousOn.comp hpar hmap).mul
    (by fun_prop)).mul (hbase.cpow_const hslit) |>.add
    ((complexEllipticK_continuousOn.comp hpar hmap).mul
      ((continuousOn_const.mul (hbase.cpow_const hslit)).mul (by fun_prop)))

theorem correctionRegularDerivative_continuousOn_interval {b : ℝ} (hb : 0 < b) {w : ℂ}
    (hw : w ∈ correctionDomain b) : ContinuousOn (correctionRegularDerivative b w) (Icc 0 1) :=
  (correctionRegularDerivative_continuousOn hb).comp (f := fun v : ℝ => (w, v))
    (by fun_prop) (fun v hv => ⟨hw, hv⟩)

theorem correctionRegularDerivative_weight_integrable {b : ℝ} (hb : 0 < b) {w : ℂ} (hw : w ∈ correctionDomain b) :
    IntervalIntegrable (fun v => correctionRegularDerivative b w v * (correctionWeight v : ℂ)) volume 0 1 := by
  have hi : IntervalIntegrable (fun v => (correctionWeight v : ℂ)) volume 0 1 :=
    ⟨correctionWeight_integrable.1.ofReal, correctionWeight_integrable.2.ofReal⟩
  apply IntervalIntegrable.continuousOn_mul hi
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact correctionRegularDerivative_continuousOn_interval hb hw

theorem continuedCorrection_differentiableAt {b : ℝ} (hb : 0 < b) {w : ℂ} (hw : w ∈ correctionDomain b) :
    DifferentiableAt ℂ (continuedCorrection b) w := by
  have hopen := correctionDomain_isOpen b
  obtain ⟨ε, hε, he⟩ := Metric.isOpen_iff.mp hopen w hw
  have hc : Metric.closedBall w (ε / 2) ⊆ correctionDomain b :=
    (Metric.closedBall_subset_ball (by linarith)).trans he
  have hcompact := (isCompact_closedBall w (ε / 2)).prod
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
    ((correctionRegularDerivative_continuousOn hb).mono (fun p hp => ⟨hc hp.1, hp.2⟩))
  have hd := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w v => correctionRegular b w v * (correctionWeight v : ℂ))
    (F' := fun w v => correctionRegularDerivative b w v * (correctionWeight v : ℂ)) (μ := volume)
    (bound := fun v => C * |correctionWeight v|) (a := 0) (b := 1)
    (s := Metric.ball w (ε / 2)) (Metric.ball_mem_nhds w (by linarith))
    (by
      filter_upwards [hopen.mem_nhds hw] with z hz
      have hi := correctionRegular_weight_integrable hb hz
      rw [intervalIntegrable_iff] at hi
      exact hi.aestronglyMeasurable)
    (correctionRegular_weight_integrable hb hw)
    (by
      have hi := correctionRegularDerivative_weight_integrable hb hw
      rw [intervalIntegrable_iff] at hi
      exact hi.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun v hv z hz => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      apply hC (z, v)
      refine ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hz).le, ?_⟩
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
      exact ⟨hv.1.le, hv.2⟩)
    (IntervalIntegrable.const_mul correctionWeight_integrable.abs C)
    (Filter.Eventually.of_forall fun v hv z hz => by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
      exact (correctionRegular_hasDerivAt hb
        (hc (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hz).le)) ⟨hv.1.le, hv.2⟩).mul_const _)
  have hslit := correctionPrefactor_mem_slitPlane hw
  have hpow := ((hasDerivAt_id w).const_sub (b : ℂ)).cpow_const
    (c := -(1 / 2 : ℂ)) hslit
  exact (((differentiableAt_const (b : ℂ)).sub differentiableAt_id).mul hpow.differentiableAt).div_const _ |>.mul hd.2.differentiableAt

theorem continuedCorrection_analyticOnNhd {b : ℝ} (hb : 0 < b) :
    AnalyticOnNhd ℂ (continuedCorrection b) {w : ℂ | w.im < 0} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt Complex.continuous_im continuous_const)
  intro w hw
  exact (continuedCorrection_differentiableAt hb (Or.inl hw)).differentiableWithinAt

theorem continuedCorrection_analyticOnNhd_domain {b : ℝ} (hb : 0 < b) :
    AnalyticOnNhd ℂ (continuedCorrection b) (correctionDomain b) := by
  apply DifferentiableOn.analyticOnNhd _ (correctionDomain_isOpen b)
  intro w hw
  exact (continuedCorrection_differentiableAt hb hw).differentiableWithinAt

end AperyMoments
