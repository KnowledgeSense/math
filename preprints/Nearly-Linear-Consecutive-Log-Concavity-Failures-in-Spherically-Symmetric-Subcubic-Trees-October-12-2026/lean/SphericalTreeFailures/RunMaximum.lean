import SphericalTreeFailures.RunLocation

namespace SphericalTreeFailures
open Filter
open scoped Topology NNReal

noncomputable def maxNormalizedError (m k : ℕ) (R : Finset ℤ) (q : ℝ) : ℝ :=
  (R.sup (fun j : ℤ => (⟨|(j : ℝ) / independenceNumberOfTree m (2 * k + 1) - q|,
    abs_nonneg _⟩ : ℝ≥0)) : ℝ≥0)

noncomputable def normalizedRunError (k : ℕ) (hk : 16384 ≤ k) (a b : ℝ) (m : ℕ) : ℝ :=
  maxNormalizedError m k (releaseRun k hk a b m) (locationFraction k (releaseParameter k hk))

theorem normalizedRunError_nonneg (k : ℕ) (hk : 16384 ≤ k) (a b : ℝ) (m : ℕ) :
    0 ≤ normalizedRunError k hk a b m := NNReal.coe_nonneg _

theorem normalizedRunError_tendsto (k : ℕ) (hk : 16384 ≤ k) (a b : ℝ) :
    Tendsto (normalizedRunError k hk a b) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro l hl
    exact Eventually.of_forall fun m => hl.trans_le (normalizedRunError_nonneg k hk a b m)
  · intro ε hε
    filter_upwards [releaseRun_location_uniform k hk a b (half_pos hε)] with m hm
    have h : (releaseRun k hk a b m).sup (fun j => (⟨|(j : ℝ) / independenceNumberOfTree m (2 * k + 1) -
        locationFraction k (releaseParameter k hk)|, abs_nonneg _⟩ : ℝ≥0)) ≤
        (⟨ε / 2, (half_pos hε).le⟩ : ℝ≥0) := by
      apply Finset.sup_le
      intro j hj
      exact (hm j hj).le
    have he : normalizedRunError k hk a b m ≤ ε / 2 := h
    exact he.trans_lt (half_lt_self hε)

theorem normalizedRunError_ge (k : ℕ) (hk : 16384 ≤ k) (a b : ℝ) (m : ℕ)
    {j : ℤ} (hj : j ∈ releaseRun k hk a b m) :
    |(j : ℝ) / independenceNumberOfTree m (2 * k + 1) - locationFraction k (releaseParameter k hk)| ≤
      normalizedRunError k hk a b m := by
  exact Finset.le_sup (s := releaseRun k hk a b m) (f := fun j : ℤ => (⟨|(j : ℝ) / independenceNumberOfTree m (2 * k + 1) -
    locationFraction k (releaseParameter k hk)|, abs_nonneg _⟩ : ℝ≥0)) hj

theorem normalizedRunError_attained (k : ℕ) (hk : 16384 ≤ k) (a b : ℝ) (m : ℕ)
    (hne : (releaseRun k hk a b m).Nonempty) :
    ∃ j ∈ releaseRun k hk a b m, normalizedRunError k hk a b m =
      |(j : ℝ) / independenceNumberOfTree m (2 * k + 1) - locationFraction k (releaseParameter k hk)| := by
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_sup (releaseRun k hk a b m) hne
    (fun j : ℤ => (⟨|(j : ℝ) / independenceNumberOfTree m (2 * k + 1) -
      locationFraction k (releaseParameter k hk)|, abs_nonneg _⟩ : ℝ≥0))
  exact ⟨j, hj, congrArg (fun z : ℝ≥0 => (z : ℝ)) he⟩

end SphericalTreeFailures
