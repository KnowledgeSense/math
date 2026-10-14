import SphericalTreeFailures.TotalCharacteristic

set_option backward.isDefEq.respectTransparency false

namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory

noncomputable def rootSelectedSize (k m : ℕ) (ω : TotalSizeSpace k) : ℝ :=
  sampledTotalSize k m (ω.1 []) ω

theorem measurable_rootSelectedSize (k m : ℕ) : Measurable (rootSelectedSize k m) := by
  have he : rootSelectedSize k m = fun ω => if ω.1 [] then sampledTotalSize k m true ω
      else sampledTotalSize k m false ω := by funext ω; cases hh : ω.1 [] <;> simp [rootSelectedSize, hh]
  rw [he]
  have hm : Measurable (fun ω : TotalSizeSpace k => ω.1 []) :=
    (measurable_pi_apply []).comp measurable_fst
  have hs : MeasurableSet {ω : TotalSizeSpace k | ω.1 [] = true} :=
    hm (measurableSet_singleton true)
  exact Measurable.ite hs
    (measurable_sampledTotalSize k m true) (measurable_sampledTotalSize k m false)

theorem total_root_input_law (p : unitInterval) (k : ℕ) (activity : ℝ) (ha : 0 < activity) :
    HasLaw (fun ω : TotalSizeSpace k => ω.1 []) (bernoulliMeasure true false p)
      (totalSizeMeasure p k activity ha) :=
  (broadcast_input_law p []).comp measurePreserving_fst.hasLaw

theorem integral_root_selector (p : unitInterval) (k : ℕ) (activity : ℝ) (ha : 0 < activity)
    (i : Bool) :
    (∫ ω : TotalSizeSpace k, (if ω.1 [] = i then (1 : ℂ) else 0) ∂totalSizeMeasure p k activity ha) =
      if i then (p : ℂ) else ((1 - (p : ℝ) : ℝ) : ℂ) := by
  have h := (total_root_input_law p k activity ha).integral_comp
    (measurable_of_finite (fun b : Bool => if b = i then (1 : ℂ) else 0)).aestronglyMeasurable
  rw [integral_bernoulliMeasure] at h
  cases i <;> simpa [Complex.real_smul] using h

theorem rootSelected_characteristic (p : unitInterval) (k m : ℕ) (activity : ℝ)
    (ha : 0 < activity) (t : ℝ) :
    (∫ ω, sizeExponential (rootSelectedSize k m ω) t ∂totalSizeMeasure p k activity ha) =
      ((1 - (p : ℝ) : ℝ) : ℂ) * sampledCharacteristic p k m activity ha false t +
        (p : ℂ) * sampledCharacteristic p k m activity ha true t := by
  let sel := fun i (ω : TotalSizeSpace k) => if ω.1 [] = i then (1 : ℂ) else 0
  let exp := fun i (ω : TotalSizeSpace k) => sizeExponential (sampledTotalSize k m i ω) t
  have hm (i : Bool) : Measurable (sel i) :=
    (measurable_of_finite (fun b : Bool => if b = i then (1 : ℂ) else 0)).comp
      ((measurable_pi_apply []).comp measurable_fst)
  have he (i : Bool) : Measurable (exp i) :=
    (measurable_sizeExponential t).comp (measurable_sampledTotalSize k m i)
  have hi (i : Bool) : Integrable (fun ω => sel i ω * exp i ω) (totalSizeMeasure p k activity ha) := by
    apply Integrable.of_bound ((hm i).mul (he i)).aestronglyMeasurable 1
    refine Filter.Eventually.of_forall fun ω => ?_
    dsimp [sel, exp]
    split_ifs <;> simp [sizeExponential_norm]
  have hf (i : Bool) : (∫ ω, sel i ω * exp i ω ∂totalSizeMeasure p k activity ha) =
      (if i then (p : ℂ) else ((1 - (p : ℝ) : ℝ) : ℂ)) * sampledCharacteristic p k m activity ha i t := by
    have hind := (rootInput_sampledTotalSize_independent p k m activity ha i).comp
      (measurable_of_finite (fun b : Bool => if b = i then (1 : ℂ) else 0))
      (measurable_sizeExponential t)
    have h := hind.integral_fun_mul_eq_mul_integral (hm i).aestronglyMeasurable (he i).aestronglyMeasurable
    change (∫ ω, sel i ω * exp i ω ∂totalSizeMeasure p k activity ha) = _ at h
    simp only [Function.comp_apply] at h
    rw [h, integral_root_selector]
    rfl
  have hx (ω : TotalSizeSpace k) : sizeExponential (rootSelectedSize k m ω) t =
      sel false ω * exp false ω + sel true ω * exp true ω := by
    cases hh : ω.1 [] <;> simp [rootSelectedSize, sel, exp, hh]
  simp_rw [hx]
  rw [integral_add (hi false) (hi true), hf false, hf true]
  rfl

end SphericalTreeFailures
