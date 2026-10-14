import MeanMaximumForests.Definitions
import Mathlib.Tactic.Ring

namespace MeanMaximumForests

theorem product_comm (v w : ConeVector) : product v w = product w v := by
  ext <;> simp only [product] <;> ring
theorem product_assoc (u v w : ConeVector) :
    product (product u v) w = product u (product v w) := by
  ext <;> simp only [product] <;> ring
theorem product_unit (v : ConeVector) : product v unitVector = v := by
  ext <;> simp [product, unitVector]
theorem unit_product (v : ConeVector) : product unitVector v = v := by
  rw [product_comm, product_unit]

theorem centered_product (c a b p q dp dq : ℝ) :
    dp * q + p * dq - c * (a + b) * (p * q) =
      (dp - c * a * p) * q + p * (dq - c * b * q) := by ring
theorem centered_plant (c a b p q dp dq : ℝ) :
    dp + q + dq - c * (a + b) * (p + q) =
      (dp - c * a * p) + (dq - c * a * q) + (1 - c * b) * q - c * b * p := by ring
theorem centered_root_deleted (c a b p dp : ℝ) :
    dp - c * (a + b) * p = (dp - c * a * p) - c * b * p := by ring

theorem vector_mem {c : ℝ} {C : Bool → Set ConeVector}
    (h : InvariantConditions c C) (F : ForestExpr) : vector c F ∈ C (flag F) := by
  induction F with
  | empty => exact h.empty
  | union a b ha hb => exact h.product _ _ _ _ ha hb
  | root a ha => exact h.plant _ _ ha

theorem root_nonnegative {c : ℝ} {C : Bool → Set ConeVector}
    (h : InvariantConditions c C) (F : ForestExpr) : 0 ≤ (vector c (.root F)).x := by
  exact h.sign _ _ (vector_mem h F)

theorem centered_nonnegative_iff (c a p dp : ℝ) (hp : 0 < p) :
    0 ≤ dp - c * a * p ↔ c * a ≤ dp / p := by
  rw [le_div_iff₀ hp]
  exact sub_nonneg

theorem single_vertex_vector :
    plant (47 / 100 : ℝ) false unitVector = ⟨2, 1, 6 / 100, -(47 / 100)⟩ := by
  ext <;> simp only [plant, Bool.false_eq_true, ↓reduceIte, unitVector] <;> ring

end MeanMaximumForests
