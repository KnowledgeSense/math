import SphericalTreeFailures.FiniteAnnulus
import SphericalTreeFailures.ExponentialContraction

namespace SphericalTreeFailures

 theorem finite_decay_of_annulus (k : ℕ) (hk : 16384 ≤ k) (h : ℕ)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hb : ∀ m ≥ h, ∀ t ∈ frequencyAnnulus (fluctuationScale (releaseParameter k hk)),
      scaledEnvelope m k (releaseParameter k hk) t ≤ ρ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ m ≥ h, ∀ t : ℝ,
      |t| ≤ Real.pi * fluctuationScale (releaseParameter k hk) ^ m →
      scaledEnvelope m k (releaseParameter k hk) t ≤
        C * Real.exp (-c * |t| ^ fourierExponent (fluctuationScale (releaseParameter k hk))) := by
  let r := releaseParameter k hk
  let γ := fluctuationScale r
  let β := fourierExponent γ
  have hg : 1 < γ := release_scale_gt_one k hk
  have hg0 : 0 < γ := by linarith
  have hβ : 0 < β := fourierExponent_pos hg
  obtain ⟨ρ₀, hρ₀0, hρ₀1, hb₀⟩ := release_fixed_depth_annulus k hk h
  let D := Real.pi ^ β * (2 : ℝ) ^ h
  have hD : 0 < D := by dsimp [D]; positivity
  let c := min (-Real.log ρ / 2) (-Real.log ρ₀ / D)
  have hc : 0 < c := lt_min
    (contraction_constant_pos hρ0 hρ1 (by norm_num))
    (contraction_constant_pos hρ₀0 hρ₀1 hD)
  refine ⟨c, Real.exp c, hc, Real.exp_pos _, ?_⟩
  intro m hm t ht
  by_cases ht1 : 1 ≤ |t|
  · obtain ⟨j, hj0, _, hjA, hjB, hjPow⟩ := exists_fourier_annulus hg ht1
    have hlarge : scaledEnvelope m k r t ≤ Real.exp (-c * |t| ^ β) := by
      by_cases hj : j ≤ m - h
      · have hmj : h ≤ m - j := by omega
        have he : m = (m - j) + j := by omega
        have hiter := scaledEnvelope_iterate_bound k (releaseParameter_pos k hk)
          (releaseParameter_spec k hk).2.2 (m - j) j t (hb (m - j) hmj (t / γ ^ j) ⟨hjA, hjB⟩)
        rw [← he] at hiter
        apply hiter.trans
        have hp := power_contraction_bound hρ0 hρ1 (by norm_num : (0 : ℝ) < 2)
          (2 ^ j) (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hjPow)
        apply hp.trans
        apply Real.exp_le_exp.mpr
        have hc' : c ≤ -Real.log ρ / 2 := min_le_left _ _
        exact mul_le_mul_of_nonneg_right (neg_le_neg hc') (Real.rpow_nonneg (abs_nonneg _) _)
      · let d := m - h
        have hmd : m = h + d := by dsimp [d]; omega
        have hdj : d ≤ j := by dsimp [d]; omega
        have hgd : 0 < γ ^ d := pow_pos hg0 d
        have hs0 : 1 ≤ |t / γ ^ d| := by
          rw [abs_div, abs_of_pos hgd]
          apply (one_le_div hgd).mpr
          exact (pow_le_pow_right₀ hg.le hdj).trans hj0
        have hs1 : |t / γ ^ d| ≤ Real.pi * γ ^ h := by
          rw [abs_div, abs_of_pos hgd]
          apply (div_le_iff₀ hgd).mpr
          have he : Real.pi * γ ^ m = (Real.pi * γ ^ h) * γ ^ d := by rw [hmd, pow_add]; ring
          exact ht.trans_eq he
        have hiter := scaledEnvelope_iterate_bound k (releaseParameter_pos k hk)
          (releaseParameter_spec k hk).2.2 h d t (hb₀ (t / γ ^ d) ⟨hs0, hs1⟩)
        rw [← hmd] at hiter
        have hTP : |t| ^ β ≤ D * (2 : ℝ) ^ d := by
          calc
            _ ≤ (Real.pi * γ ^ m) ^ β := Real.rpow_le_rpow (abs_nonneg _) ht hβ.le
            _ = Real.pi ^ β * (2 : ℝ) ^ m := by
              rw [Real.mul_rpow Real.pi_pos.le (pow_nonneg hg0.le _), scale_pow_rpow_fourierExponent hg]
            _ = _ := by rw [hmd, pow_add]; dsimp [D]; ring
        apply hiter.trans
        have hp := power_contraction_bound hρ₀0 hρ₀1 hD (2 ^ d)
          (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hTP)
        apply hp.trans
        apply Real.exp_le_exp.mpr
        have hc' : c ≤ -Real.log ρ₀ / D := min_le_right _ _
        exact mul_le_mul_of_nonneg_right (neg_le_neg hc') (Real.rpow_nonneg (abs_nonneg _) _)
    exact hlarge.trans (le_mul_of_one_le_left (Real.exp_pos _).le (Real.one_le_exp hc.le))
  · exact (release_scaledEnvelope_le_one k hk m t).trans
      (small_frequency_exponential_bound hc.le hβ.le (by linarith))

end SphericalTreeFailures
