import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith

/-! # Positive curvature from failure of log-concavity -/

namespace SphericalTreeFailures

/-- A positive twice differentiable function whose logarithm is not concave has
an interval on which the numerator of its logarithmic second derivative is
uniformly positive. -/
theorem positive_curvature_interval {f f1 f2 : ℝ → ℝ}
    (hf : ∀ x, 0 < f x)
    (hd : ∀ x, HasDerivAt f (f1 x) x)
    (hd1 : ∀ x, HasDerivAt f1 (f2 x) x)
    (hc2 : Continuous f2)
    (hn : ¬ ConcaveOn ℝ Set.univ (fun x => Real.log (f x))) :
    ∃ a b δ : ℝ, a < b ∧ 0 < δ ∧
      ∀ x ∈ Set.Icc a b, δ ≤ f x * f2 x - f1 x ^ 2 := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hc1 : Continuous f1 := continuous_iff_continuousAt.mpr fun x => (hd1 x).continuousAt
  have hdlog : ∀ x, HasDerivAt (fun y => Real.log (f y)) (f1 x / f x) x :=
    fun x => (hd x).log (ne_of_gt (hf x))
  have hdlog1 : ∀ x, HasDerivAt (fun y => f1 y / f y)
      ((f x * f2 x - f1 x ^ 2) / f x ^ 2) x := by
    intro x
    simpa only [mul_comm (f2 x) (f x), pow_two] using
      (hd1 x).fun_div (hd x) (ne_of_gt (hf x))
  have hpos : ∃ x, 0 < f x * f2 x - f1 x ^ 2 := by
    by_contra! h
    apply hn
    apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := fun x => f1 x / f x)
      (f'' := fun x => (f x * f2 x - f1 x ^ 2) / f x ^ 2) convex_univ
    · exact (continuous_iff_continuousAt.mpr fun x => (hdlog x).continuousAt).continuousOn
    · exact fun x _ => (hdlog x).hasDerivWithinAt
    · exact fun x _ => (hdlog1 x).hasDerivWithinAt
    · exact fun x _ => div_nonpos_of_nonpos_of_nonneg (h x) (sq_nonneg (f x))
  obtain ⟨x, hx⟩ := hpos
  have hcurv : Continuous (fun y => f y * f2 y - f1 y ^ 2) :=
    (hc.mul hc2).sub (hc1.pow 2)
  have hevent : ∀ᶠ y in nhds x,
      (f x * f2 x - f1 x ^ 2) / 2 < f y * f2 y - f1 y ^ 2 :=
    hcurv.continuousAt.eventually_const_lt (by linarith)
  obtain ⟨a, b, hax, hsub⟩ := hevent.exists_Ioo_subset
  refine ⟨(a + x) / 2, (x + b) / 2, (f x * f2 x - f1 x ^ 2) / 2,
    ?_, by linarith, ?_⟩
  · linarith [hax.1, hax.2]
  · intro y hy
    exact (hsub ⟨by linarith [hax.1, hy.1], by linarith [hax.2, hy.2]⟩).le

end SphericalTreeFailures
