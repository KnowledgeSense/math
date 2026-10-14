import SphericalTreeFailures.FiniteUniformDecay
import SphericalTreeFailures.CensusFourierDecay

namespace SphericalTreeFailures
open Filter

 theorem release_uniform_fourier_decay (k : ℕ) (hk : 16384 ≤ k) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ h : ℕ, ∀ m ≥ h, ∀ t : ℝ,
      |t| ≤ Real.pi * fluctuationScale (releaseParameter k hk) ^ m →
      scaledEnvelope m k (releaseParameter k hk) t ≤
        C * Real.exp (-c * |t| ^ fourierExponent (fluctuationScale (releaseParameter k hk))) := by
  let p := releaseBroadcastParameter k hk
  let r := releaseParameter k hk
  have hg := release_scale_gt_one k hk
  have hp1 : (p : ℝ) < 1 := (broadcastParameter_bounds hk (releaseParameter_spec k hk).1).2.2
  have hκ : tailShift k r ≠ 0 := by have := release_shift_negative k hk; dsimp [r]; linarith
  obtain ⟨ρ, hρ0, hρ1, hb⟩ := compact_annulus_contraction hg.le
    ((censusEnvelope_continuous p).comp (continuous_const.mul continuous_id))
    (F := fun t => censusEnvelope p (tailShift k r * t))
    (fun t _ => (norm_nonneg _).trans (le_max_left _ _))
    (fun t ht => censusEnvelope_lt_one p (releaseBroadcast_supercritical k hk) hp1
      (mul_ne_zero hκ (by have := ht.1; intro h; norm_num [h] at this)))
  obtain ⟨h, hh⟩ := eventually_atTop.mp (release_annulus_eventual_bound k hk hρ1 hb)
  obtain ⟨c, C, hc, hC, hbound⟩ := finite_decay_of_annulus k hk h
    (by linarith : 0 < (1 + ρ) / 2) (by linarith : (1 + ρ) / 2 < 1) hh
  exact ⟨c, C, hc, hC, h, hbound⟩

end SphericalTreeFailures
