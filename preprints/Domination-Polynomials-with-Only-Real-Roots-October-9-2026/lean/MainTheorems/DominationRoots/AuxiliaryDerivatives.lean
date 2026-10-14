import MainTheorems.DominationRoots.IntervalBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace ResearchMain.DominationRoots

open Set

def Regular (x : ℝ) : Prop := x ≠ 0 ∧ x ≠ 1 ∧ x ≠ 2 ∧ quadratic 3 1 x ≠ 0

noncomputable def auxiliaryFunction (x : ℝ) : ℝ :=
  x ^ 2 - x - (Real.log x + 2 * Real.log (x - 1) + Real.log (x - 2) +
    Real.log (quadratic 3 1 x))

noncomputable def auxiliaryDerivative (x : ℝ) : ℝ :=
  2 * x - 1 - 1 / x - 2 / (x - 1) - 1 / (x - 2) -
    (2 * x - 3) / quadratic 3 1 x

noncomputable def auxiliarySecondDerivative (x : ℝ) : ℝ :=
  2 + 1 / x ^ 2 + 2 / (x - 1) ^ 2 + 1 / (x - 2) ^ 2 +
    ((2 * x - 3) ^ 2 - 2 * quadratic 3 1 x) / (quadratic 3 1 x) ^ 2

theorem regular_iff_auxiliaryQ_ne_zero (x : ℝ) : Regular x ↔ auxiliaryQ x ≠ 0 := by
  simp [Regular, auxiliaryQ, sub_ne_zero, and_assoc]

theorem quadratic_hasDerivAt (c d x : ℝ) :
    HasDerivAt (quadratic c d) (2 * x - c) x := by
  convert (((hasDerivAt_id x).pow 2).sub ((hasDerivAt_id x).const_mul c)).add_const d using 1
  · rfl
  · dsimp only [id_eq]
    ring

theorem auxiliaryFunction_eq (x : ℝ) (hx : Regular x) :
    auxiliaryFunction x = x ^ 2 - x - Real.log |auxiliaryQ x| := by
  have h1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx.2.1
  have h2 : x - 2 ≠ 0 := sub_ne_zero.mpr hx.2.2.1
  rw [Real.log_abs, auxiliaryQ, Real.log_mul (mul_ne_zero (mul_ne_zero hx.1
    (pow_ne_zero 2 h1)) h2) hx.2.2.2,
    Real.log_mul (mul_ne_zero hx.1 (pow_ne_zero 2 h1)) h2,
    Real.log_mul hx.1 (pow_ne_zero 2 h1), Real.log_pow]
  simp [auxiliaryFunction]

theorem auxiliaryFunction_hasDerivAt (x : ℝ) (hx : Regular x) :
    HasDerivAt auxiliaryFunction (auxiliaryDerivative x) x := by
  have h1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx.2.1
  have h2 : x - 2 ≠ 0 := sub_ne_zero.mpr hx.2.2.1
  have h := (((hasDerivAt_id x).pow 2).sub (hasDerivAt_id x)).sub
    (((((hasDerivAt_id x).log hx.1).add
      ((((hasDerivAt_id x).sub_const 1).log h1).const_mul 2)).add
      (((hasDerivAt_id x).sub_const 2).log h2)).add
      ((quadratic_hasDerivAt 3 1 x).log hx.2.2.2))
  convert h using 1
  · rfl
  · unfold auxiliaryDerivative
    dsimp only [id_eq]
    ring

theorem auxiliaryDerivative_hasDerivAt (x : ℝ) (hx : Regular x) :
    HasDerivAt auxiliaryDerivative (auxiliarySecondDerivative x) x := by
  have h1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx.2.1
  have h2 : x - 2 ≠ 0 := sub_ne_zero.mpr hx.2.2.1
  have hid := hasDerivAt_id x
  have h := ((((((hid.const_mul 2).sub_const 1).sub
      ((hasDerivAt_const x (1 : ℝ)).div hid hx.1)).sub
      ((hasDerivAt_const x (2 : ℝ)).div (hid.sub_const 1) h1)).sub
      ((hasDerivAt_const x (1 : ℝ)).div (hid.sub_const 2) h2)).sub
      (((hid.const_mul 2).sub_const 3).div (quadratic_hasDerivAt 3 1 x) hx.2.2.2))
  convert h using 1
  · rfl
  · unfold auxiliarySecondDerivative
    dsimp only [id_eq]
    ring

theorem auxiliarySecondDerivative_positive (x : ℝ) : 0 < auxiliarySecondDerivative x := by
  have hq : 0 ≤ (2 * x - 3) ^ 2 - 2 * quadratic 3 1 x := by
    unfold quadratic
    nlinarith [sq_nonneg (x - 3 / 2)]
  unfold auxiliarySecondDerivative
  positivity

theorem auxiliaryDerivative_strictMonoOn {S : Set ℝ} (hS : Convex ℝ S)
    (hreg : ∀ x ∈ S, Regular x) : StrictMonoOn auxiliaryDerivative S := by
  apply strictMonoOn_of_deriv_pos hS
  · intro x hx
    exact (auxiliaryDerivative_hasDerivAt x (hreg x hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [(auxiliaryDerivative_hasDerivAt x (hreg x (interior_subset hx))).deriv]
    exact auxiliarySecondDerivative_positive x

end ResearchMain.DominationRoots
