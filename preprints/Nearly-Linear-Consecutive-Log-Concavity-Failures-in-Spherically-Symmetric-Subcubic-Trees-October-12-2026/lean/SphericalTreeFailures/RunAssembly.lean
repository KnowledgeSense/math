import SphericalTreeFailures.RunCoefficientTransfer
import SphericalTreeFailures.RunGrowth
import SphericalTreeFailures.RunMaximum

namespace SphericalTreeFailures
open Filter
open scoped Topology

def Consecutive (R : Finset ℤ) : Prop :=
  ∀ i ∈ R, ∀ l ∈ R, ∀ j : ℤ, i ≤ j → j ≤ l → j ∈ R

theorem releaseRun_consecutive (k : ℕ) (hk : 16384 ≤ k) (a b : ℝ) (m : ℕ) :
    Consecutive (releaseRun k hk a b m) := by
  intro i hi l hl j hij hjl
  exact latticeInterval_consecutive hi hl hij hjl

theorem sphericalTree_vertexCard_pos (m n : ℕ) : 0 < Fintype.card (sphericalTree m n).Vertex := by
  have h := sphericalTree_card m n
  have hp : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
  nlinarith

theorem release_runs_of_curvature (k : ℕ) (hk : 16384 ≤ k) {η : ℝ}
    (hη : (2 : ℝ) ^ (-η) < (k : ℝ) / (k + 2))
    {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ)
    (hcurv : ∀ x ∈ Set.Icc a b, δ ≤ releaseCurvature k hk x) :
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
  obtain ⟨C, hC, hsize⟩ := releaseRun_card_growth k hk hη hab
  have hf := releaseRun_coefficient_failures k hk hδ hcurv
  have hi := releaseRun_interior k hk a b
  have he : ∀ᶠ m in atTop, ∀ j ∈ releaseRun k hk a b m,
      interiorFraction k * independenceNumberOfTree m (2 * k + 1) ≤ (j : ℝ) ∧
      (j : ℝ) ≤ (1 - interiorFraction k) * independenceNumberOfTree m (2 * k + 1) ∧
      0 < j ∧ j < independenceNumberOfTree m (2 * k + 1) ∧
      coefficient m (2 * k + 1) j.toNat ^ 2 <
        coefficient m (2 * k + 1) (j.toNat - 1) * coefficient m (2 * k + 1) (j.toNat + 1) := by
    filter_upwards [hf, hi] with m hm hmi
    intro j hj
    exact ⟨(hmi j hj).1, (hmi j hj).2, hm j hj⟩
  obtain ⟨m0, hm0⟩ := eventually_atTop.mp (hsize.and he)
  refine ⟨C, locationFraction k (releaseParameter k hk), m0, releaseRun k hk a b, hC,
    (release_location_bounds k hk).1, (release_location_bounds k hk).2, ?_,
    normalizedRunError_tendsto k hk a b⟩
  intro m hm
  have h := hm0 m hm
  have hn : (releaseRun k hk a b m).Nonempty := by
    apply Finset.card_pos.mp
    have hpos : 0 < C * (Fintype.card (sphericalTree m (2 * k + 1)).Vertex : ℝ) ^ (1 - η) :=
      mul_pos hC (Real.rpow_pos_of_pos (by exact_mod_cast sphericalTree_vertexCard_pos m (2 * k + 1)) _)
    have hc : (0 : ℝ) < (releaseRun k hk a b m).card := hpos.trans_le h.1
    exact_mod_cast hc
  exact ⟨hn, releaseRun_consecutive k hk a b m, h.1, h.2⟩

end SphericalTreeFailures
