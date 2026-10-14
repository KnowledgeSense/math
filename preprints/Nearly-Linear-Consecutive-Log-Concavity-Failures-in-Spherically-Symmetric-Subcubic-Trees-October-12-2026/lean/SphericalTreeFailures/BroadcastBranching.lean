import SphericalTreeFailures.CensusMoments

/-! # Independent binary subtrees

Appending the first edge to a reversed word identifies each child subtree with
the whole binary tree. This reindexing preserves an iid product measure, for any
coordinate probability space, and the two reindexed arrays are independent.
-/
namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal ProbabilityTheory Topology

/-- Coordinates below child `b`, counted relative to that child. -/
def subtreeInput {A : Type*} (b : Bool) (ω : BinaryNode → A) (v : BinaryNode) : A :=
  ω (v ++ [b])

theorem subtree_address_injective (b : Bool) :
    Function.Injective (fun v : BinaryNode => v ++ [b]) := by
  intro u v h
  exact List.append_cancel_right h

theorem subtree_address_disjoint :
    Disjoint (Set.range (fun v : BinaryNode => v ++ [false]))
      (Set.range (fun v : BinaryNode => v ++ [true])) := by
  rw [Set.disjoint_left]
  rintro v ⟨u, hu⟩ ⟨w, hw⟩
  have hh := congrArg List.reverse (hu.trans hw.symm)
  simp at hh

theorem measurable_subtreeInput {A : Type*} [MeasurableSpace A] (b : Bool) :
    Measurable (subtreeInput (A := A) b) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

theorem subtreeInput_measurePreserving {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (b : Bool) :
    MeasurePreserving (subtreeInput (A := A) b) (Measure.infinitePi (fun _ : BinaryNode => μ))
      (Measure.infinitePi (fun _ : BinaryNode => μ)) := by
  refine ⟨measurable_subtreeInput b, ?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (subtree_address_injective b)

theorem subtreeInput_independent {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] :
    IndepFun (subtreeInput (A := A) false) (subtreeInput (A := A) true)
      (Measure.infinitePi (fun _ : BinaryNode => μ)) := by
  let m (S : Set BinaryNode) : MeasurableSpace (BinaryNode → A) :=
    ⨆ v ∈ S, MeasurableSpace.comap (fun ω : BinaryNode → A => ω v) inferInstance
  have hm (b : Bool) : @Measurable (BinaryNode → A) (BinaryNode → A)
      (m (Set.range (fun v : BinaryNode => v ++ [b]))) inferInstance (subtreeInput b) := by
    exact @Measurable.of_eval (BinaryNode → A) BinaryNode (fun _ => A)
      (m (Set.range (fun v : BinaryNode => v ++ [b]))) (fun _ => inferInstance)
      (subtreeInput b) (fun v => measurable_iff_comap_le.mpr
        (le_iSup_of_le (v ++ [b]) (le_iSup_of_le ⟨v, rfl⟩ le_rfl)))
  have hind : iIndepFun (fun v (ω : BinaryNode → A) => ω v)
      (Measure.infinitePi (fun _ : BinaryNode => μ)) :=
    iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  have hi := indep_iSup_of_disjoint (fun v : BinaryNode =>
    (measurable_pi_apply (X := fun _ : BinaryNode => A) v).comap_le) hind.iIndep subtree_address_disjoint
  apply (IndepFun_iff_Indep _ _ _).mpr
  exact indep_of_indep_of_le hi (hm false).comap_le (hm true).comap_le

theorem broadcast_subtreeInput_preserving (p : unitInterval) (b : Bool) :
    MeasurePreserving (subtreeInput b) (broadcastMeasure p) (broadcastMeasure p) :=
  subtreeInput_measurePreserving _ b

theorem broadcast_subtreeInput_independent (p : unitInterval) :
    IndepFun (subtreeInput false) (subtreeInput true) (broadcastMeasure p) :=
  subtreeInput_independent _

theorem broadcastState_subtree (i : Bool) (ω : BroadcastSpace) (b : Bool) (v : BinaryNode) :
    broadcastState i ω (v ++ [b]) =
      broadcastState (broadcastState i ω [b]) (subtreeInput b ω) v := by
  induction v with
  | nil => rfl
  | cons a v ih => simp only [List.cons_append, broadcastState_child, ih, subtreeInput]

theorem measurable_broadcastState_nonroot (i : Bool) (v : BinaryNode) :
    @Measurable BroadcastSpace Bool (inputSigma {w : BinaryNode | w ≠ []}) inferInstance
      (fun ω => broadcastState i ω v) := by
  induction v with
  | nil => exact measurable_const
  | cons b v ih =>
    exact Measurable.ite (ih (measurableSet_singleton true)) measurable_const
      (measurable_input_in (by simp))

theorem measurable_censusMartingale_nonroot (p : ℝ) (i : Bool) (h : ℕ) :
    @Measurable BroadcastSpace ℝ (inputSigma {w : BinaryNode | w ≠ []}) inferInstance
      (censusMartingale p i h) := by
  apply measurable_const.mul
  exact Finset.measurable_sum _ fun v _ =>
    (measurable_boolIndicator.comp (measurable_broadcastState_nonroot i v)).sub measurable_const

theorem aestronglyMeasurable_censusLimit_nonroot (p : unitInterval)
    (hc : 1 < 2 * (p : ℝ) ^ 2) (i : Bool) :
    AEStronglyMeasurable[inputSigma {w : BinaryNode | w ≠ []}]
      (censusLimit p i) (broadcastMeasure p) := by
  apply (isClosed_aestronglyMeasurable (F := ℝ) (p := (2 : ℝ≥0∞))
    (μ := broadcastMeasure p) (inputSigma_le {w : BinaryNode | w ≠ []})).mem_of_tendsto
      (censusL2_tendsto p hc i)
  exact Eventually.of_forall fun h =>
    (measurable_censusMartingale_nonroot p i h).aestronglyMeasurable.congr
      (memLp_censusMartingale p i h 2).coeFn_toLp.symm

theorem rootInput_censusLimit_independent (p : unitInterval)
    (hc : 1 < 2 * (p : ℝ) ^ 2) (i : Bool) :
    IndepFun (fun ω : BroadcastSpace => ω []) (censusLimit p i) (broadcastMeasure p) := by
  have hw := aestronglyMeasurable_censusLimit_nonroot p hc i
  have hi := inputSigma_independent p
    (S := {[]}) (T := {w : BinaryNode | w ≠ []}) (by simp : Disjoint _ _)
  have hm : @Measurable BroadcastSpace Bool (inputSigma {[]}) inferInstance
      (fun ω => ω []) := measurable_input_in (by simp)
  have hi' : IndepFun (fun ω : BroadcastSpace => ω []) (hw.mk (censusLimit p i))
      (broadcastMeasure p) :=
    (IndepFun_iff_Indep _ _ _).mpr
      (indep_of_indep_of_le hi hm.comap_le hw.measurable_mk.comap_le)
  exact hi'.congr EventuallyEq.rfl hw.ae_eq_mk.symm

end SphericalTreeFailures
