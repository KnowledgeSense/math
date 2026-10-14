import EdgeColoringMixing.RetainedTrickleDown

set_option autoImplicit false

namespace EdgeColoringMixing.WeightedInjection
open Matrix

variable {d q : ℕ}

/-- The retained covariance estimate, uniformly inflated to the original ambient
row bound. This includes zero and one unpinned row. -/
theorem retained_column_covariance_uniform (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (Δ : ℕ) (hΔ : 1 ≤ Δ) (hdΔ : d ≤ Δ)
    (hfirst : 8 * harmonicHeight Δ ≤ s + 1)
    (hsecond : 4 * (22 + 8 * ((q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2)) *
      (Δ : ℝ) * (harmonicHeight Δ)^2 ≤ (s + 1)^2)
    (hthird : columnError (22 + 8 * ((q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2))
      (s + 1) Δ + 1 / (s + 1) ≤ 1 / 5) :
    let μ := law W hW.nonneg (partition_pos W hW)
    let L := 22 + 8 * ((q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2)
    (((1 + columnError L (s + 1) Δ) • diagonal (marginalVector μ)) +
      retainedNegative μ - covariance μ).PosSemidef := by
  let L : ℝ := 22 + 8 * ((q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2)
  have hL : 0 ≤ L := by dsimp [L]; have := hW.positive; positivity
  have hb := columnError_nonneg (t := s + 1) hL hΔ
  by_cases hd0 : d = 0
  · subst d
    dsimp only
    have hz : ((1 + columnError L (s + 1) Δ) •
        diagonal (marginalVector (law W hW.nonneg (partition_pos W hW))) +
        retainedNegative (law W hW.nonneg (partition_pos W hW)) -
        covariance (law W hW.nonneg (partition_pos W hW))) = 0 := by
      ext x y
      exact Fin.elim0 x.1
    rw [hz]
    exact PosSemidef.zero
  by_cases hd1 : d = 1
  · subst d
    exact one_row_retained_covariance W hW hb
  have hd : 2 ≤ d := by omega
  have h := retained_column_covariance W hW Δ hd hdΔ hfirst hsecond hthird
  let μ := law W hW.nonneg (partition_pos W hW)
  have hD : (diagonal (marginalVector μ)).PosSemidef :=
    posSemidef_diagonal_iff.mpr (fun x => mean_nonneg μ x.1 x.2)
  have hmono := columnError_mono (t := s + 1) hL (by omega : 1 ≤ d) hdΔ
  have hslack := hD.smul (sub_nonneg.mpr hmono)
  change (((1 + columnError L (s + 1) d) • diagonal (marginalVector μ)) +
    retainedNegative μ - covariance μ).PosSemidef at h
  change (((1 + columnError L (s + 1) Δ) • diagonal (marginalVector μ)) +
    retainedNegative μ - covariance μ).PosSemidef
  convert h.add hslack using 1
  ext x y
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The original weighted-injection column covariance theorem, with the original
explicit harmonic error and no covariance, induction, or spectral premise. -/
theorem column_covariance_bound (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (Δ : ℕ) (hΔ : 1 ≤ Δ) (hdΔ : d ≤ Δ)
    (hfirst : 8 * harmonicHeight Δ ≤ s + 1)
    (hsecond : 4 * (22 + 8 * ((q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2)) *
      (Δ : ℝ) * (harmonicHeight Δ)^2 ≤ (s + 1)^2)
    (hthird : columnError (22 + 8 * ((q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2))
      (s + 1) Δ + 1 / (s + 1) ≤ 1 / 5) :
    let μ := law W hW.nonneg (partition_pos W hW)
    let L := 22 + 8 * ((q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2)
    let δ := (columnError L (s + 1) Δ + 1 / (s + 1)) * (((Δ : ℝ) + s) / s)
    ((1 + δ) • columnBlock μ - covariance μ).PosSemidef := by
  have hL : 0 ≤ 22 + 8 * ((q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2) := by
    have := hW.positive
    positivity
  exact retained_covariance_to_columnBlock W hW (columnError_nonneg hL hΔ) Δ hdΔ
    (retained_column_covariance_uniform W hW Δ hΔ hdΔ hfirst hsecond hthird)

end EdgeColoringMixing.WeightedInjection
