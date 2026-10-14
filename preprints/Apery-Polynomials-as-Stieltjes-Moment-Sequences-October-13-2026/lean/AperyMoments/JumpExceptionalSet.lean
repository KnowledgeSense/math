import AperyMoments.MomentJumpDensity
import Mathlib.Algebra.Polynomial.Roots

noncomputable section
open Set MeasureTheory Filter Polynomial
open scoped Topology
namespace AperyMoments

theorem reciprocalRadius_level_finite (α B : ℝ) :
    Set.Finite {x : ℝ | 0 < x ∧ reciprocalRadius α x = B} := by
  let p : Polynomial ℝ := X^2 + C (2*α-B^2)*X + C (α^2)
  have hp : p ≠ 0 := by
    intro he
    have hc := congrArg (fun q : Polynomial ℝ => q.coeff 2) he
    simp only [p, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_mul_X, Polynomial.coeff_C] at hc
    norm_num at hc
  apply (Polynomial.finite_setOfPred_isRoot hp).subset
  intro x hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx.1
  have he : B * Real.sqrt x = x + α := by
    rw [← hx.2, reciprocalRadius, add_mul, div_mul_cancel₀ _ (ne_of_gt hs), ← pow_two,
      Real.sq_sqrt hx.1.le]
  have hsq := congrArg (fun t : ℝ => t^2) he
  rw [mul_pow, Real.sq_sqrt hx.1.le] at hsq
  change p.eval x = 0
  simp only [p, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C]
  nlinarith

def jumpExceptionalSet (α : ℝ) : Set ℝ :=
  {0, α} ∪ {x : ℝ | 0 < x ∧ reciprocalRadius α x = 2*Real.sqrt α+4}

theorem jumpExceptionalSet_finite (α : ℝ) : (jumpExceptionalSet α).Finite :=
  (Set.toFinite {0, α}).union (reciprocalRadius_level_finite α (2*Real.sqrt α+4))

theorem momentTransform_im_boundary {α x : ℝ} (hα : 0 < α) (hx : 0 < x)
    (he : x ∉ jumpExceptionalSet α) :
    Tendsto (fun s : ℂ => (momentTransform α s).im)
      (𝓝[{s : ℂ | 0 < s.im}] (x : ℂ)) (𝓝 (-Real.pi * reciprocalMomentDensity α x)) := by
  have hne : x ≠ α := by
    intro heq
    exact he (Or.inl (by simp [heq]))
  have hn : reciprocalRadius α x ≠ 2*Real.sqrt α+4 := by
    intro heq
    exact he (Or.inr ⟨hx,heq⟩)
  rcases lt_or_gt_of_ne hne with h | h
  · exact momentTransform_im_boundary_inner hα hx h hn
  · exact momentTransform_im_boundary_outer hα hx h

theorem momentTransform_im_boundary_ae {α : ℝ} (hα : 0 < α) :
    ∀ᵐ x : ℝ ∂volume, 0 < x →
      Tendsto (fun s : ℂ => (momentTransform α s).im)
        (𝓝[{s : ℂ | 0 < s.im}] (x : ℂ)) (𝓝 (-Real.pi * reciprocalMomentDensity α x)) := by
  have he : ∀ᵐ x : ℝ ∂volume, x ∉ jumpExceptionalSet α := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using (jumpExceptionalSet_finite α).measure_zero volume
  filter_upwards [he] with x hx hp
  exact momentTransform_im_boundary hα hp hx

end AperyMoments
