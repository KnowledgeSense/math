import SphericalTreeFailures.PathMean

namespace SphericalTreeFailures
open Polynomial

theorem pathMean_eq_logarithmic_derivative (n : ℕ) (activity : ℝ) :
    pathMean n activity = activity * (pathPolynomial n).derivative.eval₂ (Nat.castRingHom ℝ) activity /
      pathPartition n activity := by
  simp [pathMean, polynomialMean, eulerPolynomial, pathPartition]

noncomputable def tailShift (k : ℕ) (r : ℝ) : ℝ :=
  pathMean (2 * k) (tunedActivity r) - pathMean (2 * k + 1) (tunedActivity r) +
    fluctuationScale r / (1 + fluctuationScale r)

noncomputable def asymptoticDensity (k : ℕ) (r : ℝ) : ℝ :=
  2 * stationaryDensity r + (1 - stationaryDensity r) * pathMean (2 * k + 1) (tunedActivity r) +
    stationaryDensity r * pathMean (2 * k) (tunedActivity r)

noncomputable def locationFraction (k : ℕ) (r : ℝ) : ℝ := asymptoticDensity k r / (k + 5 / 3)

theorem tuned_tailShift_negative {k : ℕ} {r : ℝ} (hk : 16384 ≤ k)
    (hr : (k : ℝ) / 2 < r) : tailShift k r < -1 / 4 := by
  have hk' : (16384 : ℝ) ≤ k := by exact_mod_cast hk
  have ha := tunedActivity_pos (by linarith : 0 < r)
  obtain ⟨ho0, ho, he0, he, hsmall⟩ := tuned_deficit_bounds hk hr.le
  obtain ⟨_, hgamma, _⟩ := fluctuationScale_bounds hk hr
  have hp := (broadcastParameter_bounds hk hr).2.1
  have hg0 : 0 < fluctuationScale r := by unfold fluctuationScale; linarith
  have heq : tailShift k r = oddDeficit k (1 / tunedActivity r) -
      evenDeficit k (1 / tunedActivity r) - 1 / (1 + fluctuationScale r) := by
    unfold tailShift
    rw [pathMean_even k ha, pathMean_odd k ha]
    field_simp
    ring
  rw [heq]
  exact density_scaling_negative hg0 hgamma (ho.trans hsmall) he0

theorem stationaryDensity_pos {k : ℕ} {r : ℝ} (hk : 16384 ≤ k)
    (hr : (k : ℝ) / 2 < r) : 0 < stationaryDensity r := by
  have hp := (broadcastParameter_bounds hk hr).2.1
  unfold stationaryDensity
  exact div_pos (by linarith) (by linarith)

theorem asymptoticDensity_bounds {k : ℕ} {r : ℝ} (hk : 16384 ≤ k)
    (hr : (k : ℝ) / 2 < r) :
    (k : ℝ) < asymptoticDensity k r ∧ asymptoticDensity k r < k + 3 / 2 := by
  have hk' : (16384 : ℝ) ≤ k := by exact_mod_cast hk
  have ha := tunedActivity_pos (by linarith : 0 < r)
  obtain ⟨ho0, ho, he0, he, hsmall⟩ := tuned_deficit_bounds hk hr.le
  have ht0 := stationaryDensity_pos hk hr
  have ht := stationaryDensity_lt_half hk hr
  have ho' := ho.trans hsmall
  have he' := he.trans hsmall
  unfold asymptoticDensity
  rw [pathMean_odd k ha, pathMean_even k ha]
  have h1 := mul_nonneg (show 0 ≤ 1 - stationaryDensity r by linarith) ho0
  have h2 := mul_nonneg (le_of_lt ht0) he0
  have h3 := mul_le_mul_of_nonneg_left ho' (show 0 ≤ 1 - stationaryDensity r by linarith)
  have h4 := mul_le_mul_of_nonneg_left he' (le_of_lt ht0)
  constructor <;> nlinarith

theorem locationFraction_bounds {k : ℕ} {r : ℝ} (hk : 16384 ≤ k)
    (hr : (k : ℝ) / 2 < r) :
    99 / 100 < locationFraction k r ∧
      locationFraction k r < 1 - 1 / (6 * (k : ℝ) + 10) := by
  have hk' : (16384 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨hlo, hhi⟩ := asymptoticDensity_bounds hk hr
  have hd : (0 : ℝ) < k + 5 / 3 := by positivity
  unfold locationFraction
  constructor
  · apply (lt_div_iff₀ hd).mpr
    linarith
  · apply (div_lt_iff₀ hd).mpr
    have hn : 6 * (k : ℝ) + 10 ≠ 0 := by positivity
    have he : (1 - 1 / (6 * (k : ℝ) + 10)) * (k + 5 / 3) = k + 3 / 2 := by
      field_simp
      ring
    rw [he]
    exact hhi

end SphericalTreeFailures
