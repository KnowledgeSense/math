import SphericalTreeFailures.TotalBranching

/-! # Independence of the full child subtrees

Independent broadcast arrays and independent tail arrays remain independent
when paired child by child.
-/
namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal ProbabilityTheory Topology

theorem measurePreserving_four_shuffle {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μA : Measure A) (μB : Measure B) (μC : Measure C) (μD : Measure D)
    [IsProbabilityMeasure μA] [IsProbabilityMeasure μB]
    [IsProbabilityMeasure μC] [IsProbabilityMeasure μD] :
    MeasurePreserving (fun z : (A × B) × (C × D) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
      ((μA.prod μB).prod (μC.prod μD)) ((μA.prod μC).prod (μB.prod μD)) := by
  have h1 := measurePreserving_prodAssoc μA μB (μC.prod μD)
  have h2 := (MeasurePreserving.id μA).prod
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μB μC μD))
  have h3 := (MeasurePreserving.id μA).prod
    ((Measure.measurePreserving_swap (μ := μB) (ν := μC)).prod (MeasurePreserving.id μD))
  have h4 := (MeasurePreserving.id μA).prod (measurePreserving_prodAssoc μC μB μD)
  have h5 := MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μA μC (μB.prod μD))
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

theorem independent_pairs_on_product {Ω Ω' A B C D : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f₀ : Ω → A) (f₁ : Ω → B) (g₀ : Ω' → C) (g₁ : Ω' → D)
    (hf₀ : Measurable f₀) (hf₁ : Measurable f₁) (hg₀ : Measurable g₀) (hg₁ : Measurable g₁)
    (hf : IndepFun f₀ f₁ μ) (hg : IndepFun g₀ g₁ ν) :
    IndepFun (fun ω : Ω × Ω' => (f₀ ω.1, g₀ ω.2))
      (fun ω : Ω × Ω' => (f₁ ω.1, g₁ ω.2)) (μ.prod ν) := by
  have hF : MeasurePreserving (fun ω => (f₀ ω, f₁ ω)) μ ((μ.map f₀).prod (μ.map f₁)) :=
    ⟨hf₀.prodMk hf₁, hf.map_prod_eq_prod_map_map hf₀.aemeasurable hf₁.aemeasurable⟩
  have hG : MeasurePreserving (fun ω => (g₀ ω, g₁ ω)) ν ((ν.map g₀).prod (ν.map g₁)) :=
    ⟨hg₀.prodMk hg₁, hg.map_prod_eq_prod_map_map hg₀.aemeasurable hg₁.aemeasurable⟩
  have hFG := (measurePreserving_four_shuffle (μ.map f₀) (μ.map f₁) (ν.map g₀) (ν.map g₁)).comp (hF.prod hG)
  have h₀ : MeasurePreserving (fun ω : Ω × Ω' => (f₀ ω.1, g₀ ω.2))
      (μ.prod ν) ((μ.map f₀).prod (ν.map g₀)) :=
    (show MeasurePreserving f₀ μ (μ.map f₀) from ⟨hf₀, rfl⟩).prod
      (show MeasurePreserving g₀ ν (ν.map g₀) from ⟨hg₀, rfl⟩)
  have h₁ : MeasurePreserving (fun ω : Ω × Ω' => (f₁ ω.1, g₁ ω.2))
      (μ.prod ν) ((μ.map f₁).prod (ν.map g₁)) :=
    (show MeasurePreserving f₁ μ (μ.map f₁) from ⟨hf₁, rfl⟩).prod
      (show MeasurePreserving g₁ ν (ν.map g₁) from ⟨hg₁, rfl⟩)
  apply (indepFun_iff_map_prod_eq_prod_map_map h₀.measurable.aemeasurable h₁.measurable.aemeasurable).mpr
  rw [h₀.map_eq, h₁.map_eq]
  exact hFG.map_eq

theorem totalSubtree_independent (p : unitInterval) (k : ℕ) (activity : ℝ) (ha : 0 < activity) :
    IndepFun (totalSubtree k false) (totalSubtree k true) (totalSizeMeasure p k activity ha) := by
  exact independent_pairs_on_product (broadcastMeasure p) (tailInputMeasure k activity ha)
    (subtreeInput false) (subtreeInput true) (subtreeInput false) (subtreeInput true)
    (measurable_subtreeInput false) (measurable_subtreeInput true)
    (measurable_subtreeInput false) (measurable_subtreeInput true)
    (broadcast_subtreeInput_independent p) (subtreeInput_independent (tailSampleMeasure k activity ha))

/-- Replacing the unused root input leaves the broadcast unchanged. -/
def eraseRootInput (ω : BroadcastSpace) (v : BinaryNode) : Bool :=
  if v = [] then false else ω v

theorem measurable_eraseRootInput : Measurable eraseRootInput := by
  apply Measurable.of_eval
  intro v
  by_cases hv : v = []
  · subst v
    exact measurable_const
  · simpa only [eraseRootInput, hv, ite_false] using measurable_pi_apply v

theorem measurable_eraseRootInput_nonroot :
    @Measurable BroadcastSpace BroadcastSpace (inputSigma {v : BinaryNode | v ≠ []})
      inferInstance eraseRootInput := by
  refine @Measurable.of_eval BroadcastSpace BinaryNode (fun _ => Bool)
    (inputSigma {v : BinaryNode | v ≠ []}) (fun _ => inferInstance) eraseRootInput ?_
  intro v
  by_cases hv : v = []
  · subst v
    exact measurable_const
  · simpa only [eraseRootInput, hv, ite_false] using measurable_input_in (S := {v : BinaryNode | v ≠ []}) hv

theorem rootInput_eraseRootInput_independent (p : unitInterval) :
    IndepFun (fun ω : BroadcastSpace => ω []) eraseRootInput (broadcastMeasure p) := by
  have hi := inputSigma_independent p (S := {[]}) (T := {v : BinaryNode | v ≠ []})
    (by simp : Disjoint _ _)
  have hm : @Measurable BroadcastSpace Bool (inputSigma {[]}) inferInstance (fun ω => ω []) :=
    measurable_input_in (by simp)
  exact (IndepFun_iff_Indep _ _ _).mpr
    (indep_of_indep_of_le hi hm.comap_le measurable_eraseRootInput_nonroot.comap_le)

@[simp] theorem broadcastState_eraseRootInput (i : Bool) (ω : BroadcastSpace) (v : BinaryNode) :
    broadcastState i (eraseRootInput ω) v = broadcastState i ω v := by
  induction v with
  | nil => rfl
  | cons b v ih => simp [broadcastState_child, ih, eraseRootInput]

@[simp] theorem sampledTotalSize_eraseRootInput (k m : ℕ) (i : Bool) (ω : TotalSizeSpace k) :
    sampledTotalSize k m i (eraseRootInput ω.1, ω.2) = sampledTotalSize k m i ω := by
  simp only [sampledTotalSize, broadcastState_eraseRootInput]

theorem measurable_sampledTotalSize (k m : ℕ) (i : Bool) : Measurable (sampledTotalSize k m i) := by
  apply Measurable.add
  · apply Finset.measurable_sum
    intro h hh
    apply Finset.measurable_sum
    intro v hv
    exact measurable_boolIndicator.comp ((measurable_broadcastState i v).comp measurable_fst)
  · apply Finset.measurable_sum
    intro v hv
    exact (measurable_of_finite (fun z : Bool × TailSamples k => selectedTailSize k z.1 z.2)).comp
      (((measurable_broadcastState i v).comp measurable_fst).prodMk
        ((measurable_pi_apply v).comp measurable_snd))

/-- The root Bernoulli input is independent of the full finite sampled size at
any prescribed root state. -/
theorem rootInput_sampledTotalSize_independent (p : unitInterval) (k m : ℕ)
    (activity : ℝ) (ha : 0 < activity) (i : Bool) :
    IndepFun (fun ω : TotalSizeSpace k => ω.1 []) (sampledTotalSize k m i)
      (totalSizeMeasure p k activity ha) := by
  have hi := independent_pairs_on_product (broadcastMeasure p) (tailInputMeasure k activity ha)
    (fun ω : BroadcastSpace => ω []) eraseRootInput
    (fun _ : TailInputSpace k => ()) id
    (measurable_pi_apply []) measurable_eraseRootInput measurable_const measurable_id
    (rootInput_eraseRootInput_independent p) (indepFun_const_left () id)
  have hc := hi.comp measurable_fst (measurable_sampledTotalSize k m i)
  convert hc using 1
  · rfl
  · funext ω
    exact (sampledTotalSize_eraseRootInput k m i ω).symm
  · rfl

end SphericalTreeFailures
