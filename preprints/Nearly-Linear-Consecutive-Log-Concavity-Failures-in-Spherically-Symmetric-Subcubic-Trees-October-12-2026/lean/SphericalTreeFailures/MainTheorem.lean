import SphericalTreeFailures.RunAssembly
import SphericalTreeFailures.DensityEntireExtensions
import SphericalTreeFailures.GenericCurvature

namespace SphericalTreeFailures
open Filter
open scoped Topology

theorem release_positive_curvature_interval (k : ℕ) (hk : 16384 ≤ k) :
    ∃ a b δ : ℝ, a < b ∧ 0 < δ ∧ ∀ x ∈ Set.Icc a b, δ ≤ releaseCurvature k hk x := by
  exact positive_curvature_interval (releaseDensityDerivative_zero_pos k hk)
    (releaseDensityDerivative_hasDerivAt k hk 0)
    (releaseDensityDerivative_hasDerivAt k hk 1)
    (releaseDensityDerivative_continuous k hk 2)
    (releaseDensityDerivative_not_log_concave k hk)

/-- The main theorem for the fixed odd pendant-path length `2*k+1`. -/
theorem nearly_linear_consecutive_failures {η : ℝ} (_hηpos : 0 < η)
    (k : ℕ) (hk : 16384 ≤ k) (hη : (2 : ℝ) ^ (-η) < (k : ℝ) / (k + 2)) :
    ∃ (C q : ℝ) (m0 : ℕ) (R : ℕ → Finset ℤ), 0 < C ∧
      99 / 100 < q ∧ q < 1 - 1 / (3 * ((2 : ℝ) * k + 1) + 7) ∧
      (∀ m ≥ m0, (R m).Nonempty ∧ Consecutive (R m) ∧
        C * (Fintype.card (sphericalTree m (2 * k + 1)).Vertex : ℝ) ^ (1 - η) ≤ ((R m).card : ℝ) ∧
        ∀ j ∈ R m,
          interiorFraction k * independenceNumberOfTree m (2 * k + 1) ≤ (j : ℝ) ∧
          (j : ℝ) ≤ (1 - interiorFraction k) * independenceNumberOfTree m (2 * k + 1) ∧
          0 < j ∧ j < independenceNumberOfTree m (2 * k + 1) ∧
          coefficient m (2 * k + 1) j.toNat ^ 2 <
            coefficient m (2 * k + 1) (j.toNat - 1) * coefficient m (2 * k + 1) (j.toNat + 1)) ∧
      Tendsto (fun m => maxNormalizedError m k (R m) q) atTop (𝓝 0) := by
  obtain ⟨a, b, δ, hab, hδ, hcurv⟩ := release_positive_curvature_interval k hk
  exact release_runs_of_curvature k hk hη hab hδ hcurv

end SphericalTreeFailures
