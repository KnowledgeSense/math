import SphericalTreeFailures.FrequencyAnnulus

namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory

 theorem release_scaledEnvelope_le_one (k : ℕ) (hk : 16384 ≤ k) (m : ℕ) (t : ℝ) :
    scaledEnvelope m k (releaseParameter k hk) t ≤ 1 := by
  rw [release_scaledEnvelope_eq]
  apply max_le <;>
    exact (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun _ =>
      (sizeExponential_norm _ _).le)).trans_eq (by simp)

theorem release_scale_gt_one (k : ℕ) (hk : 16384 ≤ k) :
    1 < fluctuationScale (releaseParameter k hk) := by
  have h := (broadcastParameter_bounds hk (releaseParameter_spec k hk).1).2.1
  unfold fluctuationScale
  linarith

theorem release_scaledEnvelope_lattice (k : ℕ) (hk : 16384 ≤ k) (m : ℕ)
    {t : ℝ} (ht0 : 0 < |t|)
    (ht : |t| ≤ Real.pi * fluctuationScale (releaseParameter k hk) ^ m) :
    scaledEnvelope m k (releaseParameter k hk) t < 1 := by
  have hg := release_scale_gt_one k hk
  have hgm : 0 < fluctuationScale (releaseParameter k hk) ^ m := by positivity
  obtain ⟨h0, h1⟩ := conditionalCharacteristic_lattice (by omega : 1 ≤ k)
    (releaseParameter_pos k hk) (releaseParameter_spec k hk).2.2 m
    (show 0 < |t / fluctuationScale (releaseParameter k hk) ^ m| by
      rw [abs_div, abs_of_pos hgm]; exact div_pos ht0 hgm)
    (show |t / fluctuationScale (releaseParameter k hk) ^ m| ≤ Real.pi by
      rw [abs_div, abs_of_pos hgm]; exact (div_le_iff₀ hgm).mpr ht)
  exact max_lt h0 h1

theorem release_fixed_depth_annulus (k : ℕ) (hk : 16384 ≤ k) (h : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ t ∈ frequencyAnnulus (Real.pi * fluctuationScale (releaseParameter k hk) ^ h),
        scaledEnvelope h k (releaseParameter k hk) t ≤ ρ := by
  have hg := release_scale_gt_one k hk
  have hp : (1 : ℝ) ≤ fluctuationScale (releaseParameter k hk) ^ h := one_le_pow₀ hg.le
  apply compact_annulus_contraction (by nlinarith [Real.two_le_pi] :
    1 ≤ Real.pi * fluctuationScale (releaseParameter k hk) ^ h)
    (scaledEnvelope_continuous _ _ _)
  · exact fun t _ => scaledEnvelope_nonneg _ _ _ _
  · exact fun t ht => release_scaledEnvelope_lattice k hk h (by linarith [ht.1]) ht.2

end SphericalTreeFailures
