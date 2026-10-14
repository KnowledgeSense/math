import HardCoreActivityThreshold.HeatBathVariance
import HardCoreActivityThreshold.RestrictedLaw
import HardCoreActivityThreshold.FiniteVariance

/-! A rational leaf-elimination estimate for variance tensorization at small activities. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable

/-- The activity-dependent coefficient used by leaf elimination. -/
noncomputable def leafVarianceWeight (a : ℝ) : ℝ := 6 * (1 + a) / (2 - 3 * a)

theorem leafVarianceWeight_lower {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1 / 2) :
    3 ≤ leafVarianceWeight a := by
  have hd : 0 < 2 - 3 * a := by linarith
  unfold leafVarianceWeight
  apply (le_div_iff₀ hd).mpr
  linarith

theorem leafVarianceWeight_upper {a : ℝ} (_ha : 0 ≤ a) (ha' : a ≤ 1 / 2) :
    leafVarianceWeight a ≤ 18 := by
  have hd : 0 < 2 - 3 * a := by linarith
  unfold leafVarianceWeight
  apply (div_le_iff₀ hd).mpr
  linarith

theorem leaf_activity_pos {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    0 < a / (1 + b) := div_pos ha (by linarith)

theorem leaf_activity_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a / (1 + b) ≤ a := by
  apply (div_le_iff₀ (by linarith : 0 < 1 + b)).mpr
  nlinarith

/-- Exact completion of squares for the three feasible states of an edge. -/
theorem leaf_variance_square_identity {a b : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1 / 2) (hb : 0 ≤ b) (hb' : b ≤ 1 / 2)
    (d e : ℝ) :
    leafVarianceWeight a * a / (1 + a) * d ^ 2 +
        (leafVarianceWeight b - 1) * b / (1 + b) * e ^ 2 -
        leafVarianceWeight (a / (1 + b)) * a * (1 + b) / (1 + a + b) *
          (d - b / (1 + b) * e) ^ 2 =
      2 * b / ((2 - 3 * a) * (2 + 2 * b - 3 * a)) *
          (3 * a * d + (2 - 3 * a) * e) ^ 2 +
        15 * b ^ 2 / ((2 - 3 * b) * (1 + b)) * e ^ 2 := by
  have h₁ : (1 + a) ≠ 0 := by linarith
  have h₂ : (1 + b) ≠ 0 := by linarith
  have h₃ : (1 + a + b) ≠ 0 := by linarith
  have h₄ : (2 - 3 * a) ≠ 0 := by linarith
  have h₅ : (2 - 3 * b) ≠ 0 := by linarith
  have h₆ : (2 + 2 * b - 3 * a) ≠ 0 := by linarith
  have h₇ : (2 - 3 * (a / (1 + b))) ≠ 0 := by
    have hr := leaf_activity_le ha hb
    linarith
  unfold leafVarianceWeight
  field_simp [h₁, h₂, h₃, h₄, h₅, h₆, h₇]
  ring_nf
  field_simp (disch := nlinarith)
  ring

/-- The weighted local variance after removing a leaf is charged only to its two endpoints. -/
theorem leaf_variance_three_state {a b : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1 / 2) (hb : 0 ≤ b) (hb' : b ≤ 1 / 2)
    (A B C : ℝ) :
    leafVarianceWeight (a / (1 + b)) * a * (1 + b) / (1 + a + b) *
        (C - (A + b * B) / (1 + b)) ^ 2 ≤
      leafVarianceWeight a * a / (1 + a) * (C - A) ^ 2 +
        (leafVarianceWeight b - 1) * b / (1 + b) * (B - A) ^ 2 := by
  have he : C - (A + b * B) / (1 + b) =
      (C - A) - b / (1 + b) * (B - A) := by
    field_simp
    ring
  rw [he]
  have h := leaf_variance_square_identity ha ha' hb hb' (C - A) (B - A)
  have h₁ : 0 ≤ 2 * b / ((2 - 3 * a) * (2 + 2 * b - 3 * a)) :=
    div_nonneg (by positivity) (mul_nonneg (by linarith) (by linarith))
  have h₂ : 0 ≤ 15 * b ^ 2 / ((2 - 3 * b) * (1 + b)) :=
    div_nonneg (by positivity) (mul_nonneg (by linarith) (by linarith))
  nlinarith [mul_nonneg h₁ (sq_nonneg (3 * a * (C - A) + (2 - 3 * a) * (B - A))),
    mul_nonneg h₂ (sq_nonneg (B - A))]

end HardCoreActivityThreshold
