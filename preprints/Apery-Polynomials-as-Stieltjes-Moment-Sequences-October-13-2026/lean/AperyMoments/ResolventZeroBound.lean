import AperyMoments.MomentTransformDomain
import AperyMoments.CauchyNorm
import AperyMoments.AuxiliaryDecay

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

theorem norm_sqrt_upper {s : ℂ} (hs : 0 < s.im) : ‖Complex.sqrt s‖ = Real.sqrt ‖s‖ := by
  rw [← sqrt_upper_norm hs, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem reciprocalMap_large_of_small {α D : ℝ} (hα : 0 < α) (hD : 0 < D)
    {s : ℂ} (hs : 0 < s.im) (hn : ‖s‖ ≤ α/2)
    (hq : ‖Complex.sqrt s‖ ≤ α/(2*D)) : D ≤ ‖reciprocalMap α s‖ := by
  have hqp : 0 < ‖Complex.sqrt s‖ := norm_pos_iff.mpr (by
    intro he
    have hp := (sqrt_upper_parts hs).1
    rw [he] at hp
    simp at hp)
  have ht := norm_sub_le (reciprocalMap α s) (Complex.sqrt s)
  rw [show reciprocalMap α s - Complex.sqrt s = (α : ℂ)/Complex.sqrt s by unfold reciprocalMap; ring,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα] at ht
  have ht' := (div_le_iff₀ hqp).mp ht
  have hq' := (le_div_iff₀ (by positivity : 0 < 2*D)).mp hq
  have hsquare := sqrt_upper_norm hs
  nlinarith

/-- A genuinely sublinear singularity at zero; the previously proved decay gives
more than is needed for this integrable inverse-square-root bound. -/
theorem momentTransform_zero_bound {α : ℝ} (hα : 0 < α) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∀ s : ℂ, 0 < s.im → ‖s‖ < ε →
      ‖momentTransform α s‖ ≤ C / Real.sqrt ‖s‖ := by
  let b := 2*Real.sqrt α
  let D := 4*b+32
  let ε := min (α/2) ((α/(2*D))^2)
  let C := 1+2*Real.pi*auxiliaryDecayConstant b
  have hb : 0 < b := by dsimp [b]; positivity
  have hD : 0 < D := by dsimp [D]; linarith
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hC : 0 ≤ C := by dsimp [C]; have := auxiliaryDecayConstant_nonneg hb; positivity
  refine ⟨ε,C,hε,hC,?_⟩
  intro s hs hsn
  have hsa : ‖s‖ < α/2 := hsn.trans_le (min_le_left _ _)
  have hsq : ‖s‖ < (α/(2*D))^2 := hsn.trans_le (min_le_right _ _)
  have hq : ‖Complex.sqrt s‖ ≤ α/(2*D) := by
    have hp : 0 < α/(2*D) := by positivity
    have hn := norm_nonneg (Complex.sqrt s)
    have he := sqrt_upper_norm hs
    nlinarith
  have hr := reciprocalMap_large_of_small hα hD hs hsa.le hq
  have hrim : (reciprocalMap α s).im < 0 := (reciprocalMap_im_sign hs α).1.mpr (by linarith)
  have hrre := (reciprocalMap_re_pos hs hα).le
  have hg : ‖spectralCauchyTransform b (reciprocalMap α s)‖ ≤ 1 :=
    spectralCauchyTransform_norm_le_one hb.le (by dsimp [D] at hr; linarith)
  have hH := continuedAuxiliary_decay hb hrim hrre hr
  have hp : ‖reciprocalMap α s‖ ^ (-(3/8 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by dsimp [D] at hr; linarith) (by norm_num)
  have hHb : ‖continuedAuxiliary b (reciprocalMap α s)‖ ≤ auxiliaryDecayConstant b :=
    hH.trans (by simpa using mul_le_mul_of_nonneg_left hp (auxiliaryDecayConstant_nonneg hb))
  rw [momentTransform_upper α hs, reciprocalResolvent_inner hs (by linarith), norm_div, norm_sqrt_upper hs]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  change ‖spectralCauchyTransform b (reciprocalMap α s) -
    2*Real.pi*Complex.I*continuedAuxiliary b (reciprocalMap α s)‖ ≤ C
  apply (norm_sub_le _ _).trans
  have hn : ‖2*Real.pi*Complex.I*continuedAuxiliary b (reciprocalMap α s)‖ =
      2*Real.pi*‖continuedAuxiliary b (reciprocalMap α s)‖ := by
    simp
  rw [hn]
  have hh := mul_le_mul_of_nonneg_left hHb (show 0 ≤ 2*Real.pi by positivity)
  dsimp [C]
  linarith

end AperyMoments
