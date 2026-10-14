import MeanMaximumForests.Recursion
namespace MeanMaximumForests

theorem vector_positive (c : ℝ) (F : ForestExpr) :
    0 < (vector c F).p ∧ 0 < (vector c F).q := by
  induction F with
  | empty => exact ⟨zero_lt_one, zero_lt_one⟩
  | union a b ha hb => exact ⟨mul_pos ha.1 hb.1, mul_pos ha.2 hb.2⟩
  | root a ha => exact ⟨add_pos ha.1 ha.2, ha.1⟩

theorem forest_nonnegative {c : ℝ} {C : Bool → Set ConeVector}
    (h : InvariantConditions c C) (F : ForestExpr) : 0 ≤ (vector c F).x := by
  induction F with
  | empty => exact le_refl 0
  | union a b ha hb =>
    exact add_nonneg (mul_nonneg ha (vector_positive c b).1.le)
      (mul_nonneg (vector_positive c a).1.le hb)
  | root a _ => exact root_nonnegative h a
end MeanMaximumForests
