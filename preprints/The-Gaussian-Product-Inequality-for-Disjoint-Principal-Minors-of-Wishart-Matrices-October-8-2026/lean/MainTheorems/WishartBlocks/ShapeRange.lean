import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace ResearchMain.WishartBlocks

theorem residual_shape_range {α : ℝ} {k m r ℓ : ℕ}
    (hα : (k : ℝ) + m - 1 < α) (hr : r ≤ k) (hℓ : ℓ + 1 ≤ m) :
    (m : ℝ) < α - r + 1 ∧ (ℓ : ℝ) + 1 ≤ α - r + 1 := by
  have hr' : (r : ℝ) ≤ k := by exact_mod_cast hr
  have hℓ' : (ℓ : ℝ) + 1 ≤ m := by exact_mod_cast hℓ
  constructor <;> linarith

theorem final_pair_shape_range {α : ℝ} {P k m r : ℕ}
    (hα : (P : ℝ) - 1 < α) (hP : k + m + 1 ≤ P) (hr : r ≤ k) :
    (m : ℝ) < α - r + 1 ∧ (m : ℝ) + 1 ≤ α - r + 1 := by
  have hP' : (k : ℝ) + m + 1 ≤ P := by exact_mod_cast hP
  have hr' : (r : ℝ) ≤ k := by exact_mod_cast hr
  constructor <;> linarith

theorem marginal_shape_range {α : ℝ} {P p : ℕ}
    (hα : (P : ℝ) - 1 < α) (hp : p ≤ P) : (p : ℝ) - 1 < α := by
  have hp' : (p : ℝ) ≤ P := by exact_mod_cast hp
  linarith

theorem central_residual_shape_range {α : ℝ} {k m : ℕ}
    (hα : (k : ℝ) + m - 1 < α) : (m : ℝ) - 1 < α - k := by
  linarith

end ResearchMain.WishartBlocks
