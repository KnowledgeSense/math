import R34.ReducedCorners
import R34.ChargeInterpolation
import R34.ReducedPolynomial
import R34.ReducedTensor

namespace R34.ReducedCharge

open MvPolynomial
open scoped BigOperators Classical
noncomputable section

theorem reducedPolynomial_eq_matrixValue (ch : Chain) (left right : ℝ × ℝ) :
    reducedPolynomial ch left right = matrixValue ch left right := by
  rw [matrixValue_eq_charge_sum]
  unfold reducedPolynomial
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [realValue_eq_affineModel]

theorem reducedPolynomial_schurPositive (ch : Chain) (left right : ℝ × ℝ)
    (hl : Free left) (hr : Free right) (hc : ch.Admissible) :
    SchurPositive (reducedPolynomial ch left right) := by
  change SchurPositive (ChargeInterpolation.affineColorSum ch.sizes ch.sizes_pos
    (optionCoefficient ch left right) (fun o e => (edgeAffine ch o e).1)
      (fun o e => (edgeAffine ch o e).2))
  apply ChargeInterpolation.affineColorSum_schurPositive
  intro ε
  exact affineModel_corner_nonnegative ch left right hl hr hc ε

theorem matrixValue_schurPositive (ch : Chain) (left right : ℝ × ℝ)
    (hl : Free left) (hr : Free right) (hc : ch.Admissible) :
    SchurPositive (matrixValue ch left right) := by
  rw [← reducedPolynomial_eq_matrixValue]
  exact reducedPolynomial_schurPositive ch left right hl hr hc

end
end R34.ReducedCharge
