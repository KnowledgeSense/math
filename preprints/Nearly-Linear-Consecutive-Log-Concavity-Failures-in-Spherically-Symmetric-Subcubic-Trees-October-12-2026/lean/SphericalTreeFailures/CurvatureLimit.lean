import SphericalTreeFailures.CurvatureAlgebra

namespace SphericalTreeFailures
open Filter
open scoped Topology

noncomputable def releaseCurvature (k : ℕ) (hk : 16384 ≤ k) (x : ℝ) : ℝ :=
  releaseDensityDerivative k hk 0 x * releaseDensityDerivative k hk 2 x -
    (releaseDensityDerivative k hk 1 x) ^ 2

theorem parity_curvature (k : ℕ) (hk : 16384 ≤ k) (m : ℕ) (x : ℝ) :
    realFourierIntegral (parityCharacteristic k hk m) 0 x *
      realFourierIntegral (parityCharacteristic k hk m) 2 x -
      (realFourierIntegral (parityCharacteristic k hk m) 1 x) ^ 2 =
        releaseCurvature k hk ((-1 : ℝ) ^ m * x) := by
  simp only [parityFourierIntegral, releaseCurvature, releaseDensityDerivative]
  rcases neg_one_pow_eq_or (R := ℝ) m with h | h <;> simp [h]

theorem parity_derivatives_bounded (k : ℕ) (hk : 16384 ≤ k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ m : ℕ, ∀ x : ℝ,
      |realFourierIntegral (parityCharacteristic k hk m) 0 x| ≤ M ∧
      |realFourierIntegral (parityCharacteristic k hk m) 1 x| ≤ M ∧
      |realFourierIntegral (parityCharacteristic k hk m) 2 x| ≤ M := by
  obtain ⟨B0, h0, hb0⟩ := releaseDensityDerivative_bounded k hk 0
  obtain ⟨B1, h1, hb1⟩ := releaseDensityDerivative_bounded k hk 1
  obtain ⟨B2, h2, hb2⟩ := releaseDensityDerivative_bounded k hk 2
  refine ⟨B0 + B1 + B2, by positivity, ?_⟩
  intro m x
  have H0 := hb0 ((-1 : ℝ) ^ m * x)
  have H1 := hb1 ((-1 : ℝ) ^ m * x)
  have H2 := hb2 ((-1 : ℝ) ^ m * x)
  dsimp [releaseDensityDerivative] at H0 H1 H2
  simp only [parityFourierIntegral]
  rcases neg_one_pow_eq_or (R := ℝ) m with h | h <;>
    simp only [h, one_pow, one_mul, neg_one_mul, pow_zero, pow_one, neg_sq, one_pow,
      abs_neg] at * <;> exact ⟨by linarith, by linarith, by linarith⟩

theorem curvature_local_limit_uniform (k : ℕ) (hk : 16384 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ j : ℤ,
      |releaseScale k hk m ^ 4 *
        (releaseMass k hk m (j - 1) * releaseMass k hk m (j + 1) - releaseMass k hk m j ^ 2) -
        releaseCurvature k hk ((-1 : ℝ) ^ m * releaseGrid k hk m j)| < ε := by
  obtain ⟨M, hM, hb⟩ := parity_derivatives_bounded k hk
  let δ := min 1 (ε / (4 * M + 4))
  have hden : 0 < 4 * M + 4 := by positivity
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε hden)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδe : δ ≤ ε / (4 * M + 4) := min_le_right _ _
  have hsmall : 2 * δ * (2 * M + δ) < ε := by
    have hprod : δ * (4 * M + 4) ≤ ε := (le_div_iff₀ hden).mp hδe
    nlinarith
  filter_upwards [local_limit_uniform k hk .value hδ, local_limit_uniform k hk .second hδ,
    local_limit_uniform k hk .forward hδ, local_limit_uniform k hk .backward hδ] with m h0 h2 hf hb'
  intro j
  have bounds := hb m (releaseGrid k hk m j)
  have h := curvature_approximation_bound hM hδ.le (h0 j).le (h2 j).le (hf j).le (hb' j).le
    bounds.1 bounds.2.2 bounds.2.1
  simp only [DifferenceKind.order] at h
  rw [scaledMassDifference_curvature, parity_curvature] at h
  exact h.trans_lt hsmall

end SphericalTreeFailures
