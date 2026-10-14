import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

namespace ResearchMain.DiagonalSchatten

open scoped Topology

theorem quadratic_homogeneous_euler {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : E → ℝ} (x : E) (hd : DifferentiableAt ℝ h x)
    (hh : ∀ t : ℝ, 0 < t → h (t • x) = t ^ 2 * h x) :
    fderiv ℝ h x x = 2 * h x := by
  have hcurve : HasDerivAt (fun t : ℝ => h (t • x)) (fderiv ℝ h x x) 1 := by
    convert! hd.hasFDerivAt.comp_hasDerivAt_of_eq 1
      ((hasDerivAt_id (1 : ℝ)).smul_const x) (by simp)
      using 1
    simp
  have hpoly : HasDerivAt (fun t : ℝ => t ^ 2 * h x) (2 * h x) 1 := by
    simpa using ((hasDerivAt_id (1 : ℝ)).fun_pow 2).mul_const (h x)
  have heq : (fun t : ℝ => h (t • x)) =ᶠ[𝓝 (1 : ℝ)] (fun t => t ^ 2 * h x) := by
    filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)] with t ht
    exact hh t ht
  exact hcurve.unique (hpoly.congr_of_eventuallyEq heq)

theorem quadratic_homogeneous_derivative_scale {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {h : E → ℝ} (x v : E) (t : ℝ)
    (hx : DifferentiableAt ℝ h x) (htx : DifferentiableAt ℝ h (t • x))
    (hh : ∀ y : E, h (t • y) = t ^ 2 * h y) :
    fderiv ℝ h (t • x) (t • v) = t ^ 2 * fderiv ℝ h x v := by
  have hleft : HasFDerivAt (fun y : E => h (t • y))
      ((fderiv ℝ h (t • x)).comp (t • ContinuousLinearMap.id ℝ E)) x := by
    convert! htx.hasFDerivAt.comp x (t • ContinuousLinearMap.id ℝ E).hasFDerivAt using 1
  have hright : HasFDerivAt (fun y : E => t ^ 2 * h y) (t ^ 2 • fderiv ℝ h x) x := by
    convert! hx.hasFDerivAt.const_smul (t ^ 2) using 1
  have heq : (fun y : E => h (t • y)) = (fun y => t ^ 2 * h y) := funext hh
  rw [heq] at hleft
  have he := congrArg (fun L : E →L[ℝ] ℝ => L v) (hleft.unique hright)
  simpa only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul] using he

end ResearchMain.DiagonalSchatten
