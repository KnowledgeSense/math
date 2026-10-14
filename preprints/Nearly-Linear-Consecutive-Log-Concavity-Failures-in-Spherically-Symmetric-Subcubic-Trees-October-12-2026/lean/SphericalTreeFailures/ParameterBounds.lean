import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

import Mathlib.Tactic.Ring
namespace SphericalTreeFailures

noncomputable def broadcastParameter (r : ℝ) : ℝ := r / (1 + r)
noncomputable def fluctuationScale (r : ℝ) : ℝ := 2 * broadcastParameter r
noncomputable def stationaryDensity (r : ℝ) : ℝ := broadcastParameter r / (1 + broadcastParameter r)

theorem broadcastParameter_bounds {k : ℕ} {r : ℝ} (hk : 16384 ≤ k)
    (hr : (k : ℝ) / 2 < r) :
    (k : ℝ) / (k + 2) < broadcastParameter r ∧
    99 / 100 < broadcastParameter r ∧ broadcastParameter r < 1 := by
  have hk' : (16384 : ℝ) ≤ k := by exact_mod_cast hk
  have hr0 : 0 < r := by linarith
  have hd : 0 < 1 + r := by linarith
  have hk2 : 0 < (k : ℝ) + 2 := by positivity
  have h1 : (k : ℝ) / (k + 2) < broadcastParameter r := by
    unfold broadcastParameter
    apply (div_lt_div_iff₀ hk2 hd).mpr
    nlinarith
  have h2 : (99 / 100 : ℝ) < (k : ℝ) / (k + 2) := by
    apply (lt_div_iff₀ hk2).mpr
    linarith
  exact ⟨h1, h2.trans h1, (div_lt_one hd).mpr (by linarith)⟩

theorem fluctuationScale_bounds {k : ℕ} {r : ℝ} (hk : 16384 ≤ k)
    (hr : (k : ℝ) / 2 < r) :
    2 * (k : ℝ) / (k + 2) ≤ fluctuationScale r ∧
    fluctuationScale r < 2 ∧ 2 < fluctuationScale r ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := broadcastParameter_bounds hk hr
  unfold fluctuationScale
  constructor
  · have he : 2 * (k : ℝ) / (k + 2) = 2 * ((k : ℝ) / (k + 2)) := by ring
    rw [he]
    linarith
  constructor <;> nlinarith

theorem stationaryDensity_lt_half {k : ℕ} {r : ℝ} (hk : 16384 ≤ k)
    (hr : (k : ℝ) / 2 < r) : stationaryDensity r < 1 / 2 := by
  obtain ⟨_, h2, h3⟩ := broadcastParameter_bounds hk hr
  unfold stationaryDensity
  apply (div_lt_iff₀ (by linarith : 0 < 1 + broadcastParameter r)).mpr
  linarith

theorem density_scaling_negative {gamma nuo nue : ℝ} (hg0 : 0 < gamma)
    (hg : gamma < 2) (ho : nuo ≤ 1 / 64) (he : 0 ≤ nue) :
    nuo - nue - 1 / (1 + gamma) < -1 / 4 := by
  have hi : (1 / 3 : ℝ) < 1 / (1 + gamma) := by
    apply (lt_div_iff₀ (by linarith : 0 < 1 + gamma)).mpr
    linarith
  linarith

end SphericalTreeFailures
