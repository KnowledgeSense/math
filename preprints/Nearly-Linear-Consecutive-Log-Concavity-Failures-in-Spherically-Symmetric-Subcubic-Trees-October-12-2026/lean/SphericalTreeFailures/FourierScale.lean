import SphericalTreeFailures.CensusCharacteristic

/-! # Geometric frequency annuli and the release's Fourier exponent -/
namespace SphericalTreeFailures

noncomputable def fourierExponent (γ : ℝ) : ℝ := Real.log 2 / Real.log γ

theorem fourierExponent_pos {γ : ℝ} (hγ : 1 < γ) : 0 < fourierExponent γ := by
  exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos hγ)

theorem fourierExponent_gt_one {γ : ℝ} (hγ : 1 < γ) (hγ2 : γ < 2) :
    1 < fourierExponent γ := by
  apply (lt_div_iff₀ (Real.log_pos hγ)).mpr
  simpa using Real.log_lt_log (by linarith : 0 < γ) hγ2

theorem scale_rpow_fourierExponent {γ : ℝ} (hγ : 1 < γ) :
    γ ^ fourierExponent γ = (2 : ℝ) := by
  rw [Real.rpow_def_of_pos (by linarith : 0 < γ)]
  unfold fourierExponent
  rw [mul_div_cancel₀ (Real.log 2) (ne_of_gt (Real.log_pos hγ))]
  exact Real.exp_log (by norm_num)

theorem scale_pow_rpow_fourierExponent {γ : ℝ} (hγ : 1 < γ) (n : ℕ) :
    (γ ^ n) ^ fourierExponent γ = (2 : ℝ) ^ n := by
  rw [← Real.rpow_natCast_mul (by linarith : 0 ≤ γ), mul_comm (n : ℝ),
    Real.rpow_mul_natCast (by linarith : 0 ≤ γ), scale_rpow_fourierExponent hγ]

/-- The dyadic exponent dominates half the release power throughout the nth annulus. -/
theorem fourierExponent_annulus_bound {γ t : ℝ} (hγ : 1 < γ) (n : ℕ)
    (ht : |t| ≤ γ ^ (n + 1)) :
    |t| ^ fourierExponent γ ≤ 2 * (2 : ℝ) ^ n := by
  calc
    |t| ^ fourierExponent γ ≤ (γ ^ (n + 1)) ^ fourierExponent γ :=
      Real.rpow_le_rpow (abs_nonneg _) ht (fourierExponent_pos hγ).le
    _ = 2 * (2 : ℝ) ^ n := by rw [scale_pow_rpow_fourierExponent hγ, pow_succ]; ring

theorem exists_fourier_annulus {γ t : ℝ} (hγ : 1 < γ) (ht : 1 ≤ |t|) :
    ∃ n : ℕ, γ ^ n ≤ |t| ∧ |t| < γ ^ (n + 1) ∧
      1 ≤ |t / γ ^ n| ∧ |t / γ ^ n| ≤ γ ∧
      |t| ^ fourierExponent γ ≤ 2 * (2 : ℝ) ^ n := by
  obtain ⟨n, hn0, hn1⟩ := exists_nat_pow_near ht hγ
  have hg : 0 < γ := by linarith
  have hgn := pow_pos hg n
  refine ⟨n, hn0, hn1, ?_, ?_, fourierExponent_annulus_bound hγ n hn1.le⟩
  · rw [abs_div, abs_of_pos hgn]
    exact (one_le_div hgn).mpr hn0
  · rw [abs_div, abs_of_pos hgn]
    apply (div_le_iff₀ hgn).mpr
    simpa only [pow_succ, mul_comm] using hn1.le

end SphericalTreeFailures
