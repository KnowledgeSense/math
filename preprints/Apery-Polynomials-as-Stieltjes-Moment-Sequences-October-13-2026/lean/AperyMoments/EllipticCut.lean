import AperyMoments.SquareRootSingularity
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

theorem elliptic_cut_zero_subsingleton {m : ℝ} (_hm : 1 < m) :
    Set.Subsingleton {θ : ℝ | θ ∈ Icc 0 (Real.pi / 2) ∧ 1 - m * Real.sin θ ^ 2 = 0} := by
  intro θ hθ φ hφ
  have hsθ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.1
    (hθ.1.2.trans (by linarith [Real.pi_pos]))
  have hsφ := Real.sin_nonneg_of_nonneg_of_le_pi hφ.1.1
    (hφ.1.2.trans (by linarith [Real.pi_pos]))
  have hsq : Real.sin θ ^ 2 = Real.sin φ ^ 2 := by nlinarith [hθ.2, hφ.2]
  have hsin : Real.sin θ = Real.sin φ := by nlinarith
  exact Real.strictMonoOn_sin.injOn ⟨by linarith [hθ.1.1, Real.pi_pos], hθ.1.2⟩
    ⟨by linarith [hφ.1.1, Real.pi_pos], hφ.1.2⟩ hsin

theorem elliptic_cut_ae_nonzero {m : ℝ} (hm : 1 < m) :
    ∀ᵐ θ : ℝ, θ ∈ Icc 0 (Real.pi / 2) → 1 - m * Real.sin θ ^ 2 ≠ 0 := by
  have hzero := (elliptic_cut_zero_subsingleton hm).countable.measure_zero volume
  apply ae_iff.mpr
  simpa only [not_forall, not_imp, not_not, exists_prop] using hzero

theorem cpow_continuousWithinAt_upper_real {a : ℝ} (ha : a ≠ 0) (p : ℂ) :
    ContinuousWithinAt (fun z : ℂ => z ^ p) {z : ℂ | 0 ≤ z.im} (a : ℂ) := by
  by_cases hp : 0 < a
  · exact (continuousAt_cpow_const
      (Complex.mem_slitPlane_iff.mpr (Or.inl hp))).continuousWithinAt
  · have hneg : a < 0 := lt_of_le_of_ne (le_of_not_gt hp) ha
    have hlog := Complex.continuousWithinAt_log_of_re_neg_of_im_zero
      (show (a : ℂ).re < 0 from hneg) (show (a : ℂ).im = 0 from rfl)
    have he := Complex.continuous_exp.continuousAt.comp_continuousWithinAt (hlog.mul_const p)
    apply he.congr_of_eventuallyEq
    · filter_upwards [(continuousWithinAt_id (s := {z : ℂ | 0 ≤ z.im})).tendsto.eventually_ne
        (show (a : ℂ) ≠ 0 by exact_mod_cast ha)] with z hz
      exact Complex.cpow_def_of_ne_zero hz p
    · exact Complex.cpow_def_of_ne_zero (by exact_mod_cast ha) p

theorem elliptic_vertical_base_re (m ε θ : ℝ) :
    (1 - ((m : ℂ) - Complex.I * ε) * (Real.sin θ : ℂ) ^ 2).re =
      1 - m * Real.sin θ ^ 2 := by
  rw [← Complex.ofReal_pow]
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.mul_im,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, one_mul, zero_add, sub_zero]

theorem elliptic_vertical_base_im (m ε θ : ℝ) :
    (1 - ((m : ℂ) - Complex.I * ε) * (Real.sin θ : ℂ) ^ 2).im = ε * Real.sin θ ^ 2 := by
  rw [← Complex.ofReal_pow]
  simp only [Complex.sub_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, one_mul, zero_add, sub_zero, zero_sub, neg_mul, neg_neg]

theorem elliptic_vertical_integrand_bound (m ε θ : ℝ)
    (hθ : 1 - m * Real.sin θ ^ 2 ≠ 0) :
    ‖(1 - ((m : ℂ) - Complex.I * ε) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤
      ‖1 - m * Real.sin θ ^ 2‖ ^ (-(1 / 2 : ℝ)) := by
  have hn := Complex.norm_cpow_real
    (1 - ((m : ℂ) - Complex.I * ε) * (Real.sin θ : ℂ) ^ 2) (-(1 / 2 : ℝ))
  simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hn
  rw [hn]
  apply Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hθ) _ (by norm_num)
  have hr := Complex.abs_re_le_norm
    (1 - ((m : ℂ) - Complex.I * ε) * (Real.sin θ : ℂ) ^ 2)
  rw [elliptic_vertical_base_re m ε θ] at hr
  simpa only [Real.norm_eq_abs] using hr

theorem elliptic_vertical_integrand_limit (m θ : ℝ) (hθ : 1 - m * Real.sin θ ^ 2 ≠ 0) :
    Tendsto (fun ε : ℝ =>
      (1 - ((m : ℂ) - Complex.I * ε) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)))
      (𝓝[>] 0) (𝓝 ((1 - (m : ℂ) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)))) := by
  have hbase : Tendsto (fun ε : ℝ =>
      1 - ((m : ℂ) - Complex.I * ε) * (Real.sin θ : ℂ) ^ 2)
      (𝓝[>] 0) (𝓝 ((1 - m * Real.sin θ ^ 2 : ℝ) : ℂ)) := by
    convert (show Continuous (fun ε : ℝ =>
      1 - ((m : ℂ) - Complex.I * ε) * (Real.sin θ : ℂ) ^ 2) by fun_prop).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds using 1
    push_cast
    simp
  have hwithin : Tendsto (fun ε : ℝ =>
      1 - ((m : ℂ) - Complex.I * ε) * (Real.sin θ : ℂ) ^ 2)
      (𝓝[>] 0) (𝓝[{z : ℂ | 0 ≤ z.im}] ((1 - m * Real.sin θ ^ 2 : ℝ) : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hbase, ?_⟩
  · convert (cpow_continuousWithinAt_upper_real hθ (-(1 / 2 : ℂ))).tendsto.comp hwithin using 1 <;> push_cast <;> rfl
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [elliptic_vertical_base_im]
    exact mul_nonneg (le_of_lt hε) (sq_nonneg _)

/-- The actual principal elliptic integral has its lower-lip value on the branch cut.
The single square-root singularity is controlled by an integrable majorant. -/
theorem complexEllipticK_lower_cut_limit {m : ℝ} (hm : 1 < m) :
    Tendsto (fun ε : ℝ => complexEllipticK ((m : ℂ) - Complex.I * ε))
      (𝓝[>] 0) (𝓝 (complexEllipticK m)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun θ : ℝ => ‖1 - m * Real.sin θ ^ 2‖ ^ (-(1 / 2 : ℝ)))
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hz : (m : ℂ) - Complex.I * ε ∈ ellipticDomain := by
      left
      simpa using ne_of_gt hε
    exact (complexEllipticK_integrand_continuous hz).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro ε
    filter_upwards [elliptic_cut_ae_nonzero hm] with θ hθ hmem
    rw [uIoc_of_le (by positivity)] at hmem
    exact elliptic_vertical_integrand_bound m ε θ (hθ ⟨hmem.1.le, hmem.2⟩)
  · exact elliptic_cut_majorant_intervalIntegrable hm _ _
  · filter_upwards [elliptic_cut_ae_nonzero hm] with θ hθ hmem
    rw [uIoc_of_le (by positivity)] at hmem
    exact elliptic_vertical_integrand_limit m θ (hθ ⟨hmem.1.le, hmem.2⟩)

end AperyMoments
