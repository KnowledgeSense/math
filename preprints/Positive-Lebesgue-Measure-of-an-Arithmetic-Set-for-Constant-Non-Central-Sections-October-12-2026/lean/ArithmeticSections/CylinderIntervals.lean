import ArithmeticSections.Continuants
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace ArithmeticSections
open MeasureTheory

/-- Irrational points between two images of the continued-fraction cylinder map. -/
noncomputable def cylinderInterval (b : ℕ → ℕ) (n : ℕ) (z : ℝ) : Set ℝ :=
  Set.uIoo (cylinderMap b n 0) (cylinderMap b n z) \ Set.range (fun q : ℚ => (q : ℝ))

theorem measurableSet_cylinderInterval (b : ℕ → ℕ) (n : ℕ) (z : ℝ) :
    MeasurableSet (cylinderInterval b n z) := by
  unfold cylinderInterval
  apply MeasurableSet.diff
  · exact isOpen_Ioo.measurableSet
  · exact (Set.countable_range (fun q : ℚ => (q : ℝ))).measurableSet

theorem volume_cylinderInterval {b : ℕ → ℕ} (hb : ∀ n, 1 ≤ b (n + 1))
    (n : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    volume (cylinderInterval b n z) = ENNReal.ofReal
      (z / ((denominator b (n + 1) : ℝ) *
        ((denominator b (n + 1) : ℝ) + denominator b n * z))) := by
  unfold cylinderInterval
  rw [measure_sdiff_null ((Set.countable_range (fun q : ℚ => (q : ℝ))).measure_zero volume),
    Real.volume_uIoo, cylinderMap_initial_length hb n hz]

theorem volume_cylinderInterval_le {b : ℕ → ℕ} (hb : ∀ n, 1 ≤ b (n + 1))
    (n : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    volume (cylinderInterval b n z) ≤ ENNReal.ofReal (2 * z) * volume (cylinderInterval b n 1) := by
  unfold cylinderInterval
  rw [measure_sdiff_null ((Set.countable_range (fun q : ℚ => (q : ℝ))).measure_zero volume),
    measure_sdiff_null ((Set.countable_range (fun q : ℚ => (q : ℝ))).measure_zero volume),
    Real.volume_uIoo, Real.volume_uIoo, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * z)]
  exact ENNReal.ofReal_le_ofReal (cylinderMap_length_ratio_le hb n hz)

theorem volume_cylinderInterval_pos {b : ℕ → ℕ} (hb : ∀ n, 1 ≤ b (n + 1)) (n : ℕ) :
    0 < volume (cylinderInterval b n 1) := by
  rw [volume_cylinderInterval hb n (by norm_num), ENNReal.ofReal_pos]
  have hq : (0 : ℝ) < denominator b (n + 1) := by exact_mod_cast denominator_pos hb (n + 1)
  positivity

end ArithmeticSections
