import MainTheorems.AHOConstants.WeightedFactors
import MainTheorems.AHOConstants.UnitaryTrace

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def interpolationTail (θ : ℝ) (fs : List (WeightedFactor I)) (z : ℂ) :
    Matrix I I ℂ :=
  (fs.map (fun f => f.unitaryMatrix * complexPower f.positiveDefinite
    (z * (f.weight / θ : ℝ)))).prod

noncomputable def factorInterpolant (θ : ℝ) (L : Matrix I I ℂ)
    (f : WeightedFactor I) (fs : List (WeightedFactor I)) (z : ℂ) : ℂ :=
  Matrix.trace (L * f.unitaryMatrix * complexPower f.positiveDefinite (1 - z) *
    interpolationTail θ fs z)

theorem interpolationTail_differentiable (θ : ℝ) (fs : List (WeightedFactor I)) :
    Differentiable ℂ (interpolationTail θ fs) := by
  change Differentiable ℂ (fun z : ℂ => (fs.map (fun f => f.unitaryMatrix *
    complexPower f.positiveDefinite (z * (f.weight / θ : ℝ)))).prod)
  let gs : List (ℂ → Matrix I I ℂ) := fs.map (fun f z =>
    f.unitaryMatrix * complexPower f.positiveDefinite (z * (f.weight / θ : ℝ)))
  have hg : ∀ g ∈ gs, Differentiable ℂ g := by
    intro g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
    exact (differentiable_const (c := f.unitaryMatrix)).mul
      ((complexPower_differentiable f.positiveDefinite).comp
      (differentiable_id.mul_const _))
  simpa only [gs, List.map_map, Function.comp_def] using
    differentiable_list_product gs hg

theorem interpolationTail_stripBounded {θ : ℝ} (hθ : 0 < θ)
    (fs : List (WeightedFactor I))
    (hf : ∀ f ∈ fs, 0 ≤ f.weight ∧ f.weight ≤ θ) :
    StripBounded (interpolationTail θ fs) := by
  change StripBounded (fun z : ℂ => (fs.map (fun f => f.unitaryMatrix *
    complexPower f.positiveDefinite (z * (f.weight / θ : ℝ)))).prod)
  let gs : List (ℂ → Matrix I I ℂ) := fs.map (fun f z =>
    f.unitaryMatrix * complexPower f.positiveDefinite (z * (f.weight / θ : ℝ)))
  have hg : ∀ g ∈ gs, StripBounded g := by
    intro g hg
    obtain ⟨f, hfs, rfl⟩ := List.mem_map.mp hg
    apply (StripBounded.constant f.unitaryMatrix).mul
    apply (complexPower_stripBounded f.positiveDefinite).comp (fun z => z * (f.weight / θ : ℝ))
    intro z hz₀ hz₁
    have hw₀ : 0 ≤ f.weight / θ := div_nonneg (hf f hfs).1 hθ.le
    have hw₁ : f.weight / θ ≤ 1 := (div_le_one hθ).mpr (hf f hfs).2
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact ⟨mul_nonneg hz₀ hw₀, (mul_le_mul_of_nonneg_right hz₁ hw₀).trans
      (by simpa only [one_mul] using hw₁)⟩
  simpa only [gs, List.map_map, Function.comp_def] using
    StripBounded.list_product gs hg

theorem interpolationTail_zero_unitary (θ : ℝ) (fs : List (WeightedFactor I))
    {z : ℂ} (hz : z.re = 0) :
    interpolationTail θ fs z ∈ unitary (Matrix I I ℂ) := by
  apply unitary_list_product
  intro X hX
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hX
  have hr : (z * (f.weight / θ : ℝ)).re = 0 := by simp [hz]
  rw [complexPower_vertical_line, hr,
    spectralPower_zero f.positiveMatrix f.positiveDefinite.posSemidef, Matrix.one_mul]
  exact (unitary (Matrix I I ℂ)).mul_mem f.unitaryMembership
    (complexPower_imaginary_unitary f.positiveDefinite _)

theorem interpolationTail_one {θ : ℝ} (fs : List (WeightedFactor I))
    {z : ℂ} (hz : z.re = 1) :
    interpolationTail θ fs z = weightedProduct (fs.map (normalizedFactor θ z)) := by
  unfold interpolationTail weightedProduct
  rw [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro f hf
  have hr : (z * (f.weight / θ : ℝ)).re = f.weight / θ := by simp [hz]
  rw [complexPower_vertical_line_left, hr]
  simp only [factorValue, normalizedFactor, Function.comp_apply, Matrix.mul_assoc]

theorem interpolationTail_real {θ : ℝ} (hθ : θ ≠ 0) (fs : List (WeightedFactor I)) :
    interpolationTail θ fs (θ : ℂ) = weightedProduct fs := by
  unfold interpolationTail weightedProduct
  apply congrArg List.prod
  apply List.map_congr_left
  intro f hf
  have he : (θ : ℂ) * (f.weight / θ : ℝ) = (f.weight : ℂ) := by
    have hc : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ
    push_cast
    field_simp [hc]
  rw [he, complexPower_real]
  rfl

theorem factorInterpolant_differentiable (θ : ℝ) (L : Matrix I I ℂ)
    (f : WeightedFactor I) (fs : List (WeightedFactor I)) :
    Differentiable ℂ (factorInterpolant θ L f fs) := by
  have hP := (complexPower_differentiable f.positiveDefinite).comp
    ((differentiable_const (c := (1 : ℂ))).sub differentiable_id)
  let T : Matrix I I ℂ →L[ℂ] ℂ :=
    (Matrix.traceLinearMap I ℂ ℂ).toContinuousLinearMap
  exact T.differentiable.comp
    (((differentiable_const (c := L * f.unitaryMatrix)).mul hP).mul
      (interpolationTail_differentiable θ fs))

theorem factorInterpolant_stripBounded {θ : ℝ} (hθ : 0 < θ) (L : Matrix I I ℂ)
    (f : WeightedFactor I) (fs : List (WeightedFactor I))
    (hf : ∀ g ∈ fs, 0 ≤ g.weight ∧ g.weight ≤ θ) :
    StripBounded (factorInterpolant θ L f fs) := by
  have hP := (complexPower_stripBounded f.positiveDefinite).comp (fun z => 1 - z)
    (by intro z hz₀ hz₁; simp only [Complex.sub_re, Complex.one_re]; constructor <;> linarith)
  exact (((StripBounded.constant (L * f.unitaryMatrix)).mul hP).mul
    (interpolationTail_stripBounded hθ fs hf)).trace

theorem factorInterpolant_zero_boundary {θ : ℝ} {L : Matrix I I ℂ}
    (hL : L ∈ unitary (Matrix I I ℂ)) (f : WeightedFactor I)
    (fs : List (WeightedFactor I)) {z : ℂ} (hz : z.re = 0) :
    ‖factorInterpolant θ L f fs z‖ ≤ (Matrix.trace f.positiveMatrix).re := by
  let V := complexPower f.positiveDefinite (((1 - z).im : ℂ) * Complex.I)
  let W := interpolationTail θ fs z
  have hV : V ∈ unitary (Matrix I I ℂ) := complexPower_imaginary_unitary f.positiveDefinite _
  have hW : W ∈ unitary (Matrix I I ℂ) := interpolationTail_zero_unitary θ fs hz
  have hr : (1 - z).re = 1 := by simp [hz]
  have he : factorInterpolant θ L f fs z =
      Matrix.trace (((V * W) * (L * f.unitaryMatrix)) * f.positiveMatrix) := by
    unfold factorInterpolant
    rw [complexPower_vertical_line, hr, spectralPower_one _ f.positiveDefinite.posSemidef]
    change Matrix.trace ((L * f.unitaryMatrix) * (f.positiveMatrix * V) * W) = _
    calc
      _ = Matrix.trace (((L * f.unitaryMatrix) * f.positiveMatrix) * (V * W)) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((V * W) * ((L * f.unitaryMatrix) * f.positiveMatrix)) :=
        Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [he]
  exact unitary_positive_trace_bound ((unitary (Matrix I I ℂ)).mul_mem
    ((unitary (Matrix I I ℂ)).mul_mem hV hW)
    ((unitary (Matrix I I ℂ)).mul_mem hL f.unitaryMembership)) f.positiveDefinite.posSemidef

theorem factorInterpolant_real {θ : ℝ} (hθ : θ ≠ 0) (L : Matrix I I ℂ)
    (f : WeightedFactor I) (fs : List (WeightedFactor I)) (hw : f.weight = 1 - θ) :
    factorInterpolant θ L f fs (θ : ℂ) = Matrix.trace (L * weightedProduct (f :: fs)) := by
  unfold factorInterpolant
  have he : (1 : ℂ) - (θ : ℂ) = ((1 - θ : ℝ) : ℂ) := by push_cast; rfl
  rw [he, complexPower_real, ← hw, interpolationTail_real hθ,
    weightedProduct_cons]
  simp only [factorValue, Matrix.mul_assoc]

end ResearchMain.AHOConstants
