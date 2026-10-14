import SphericalTreeFailures.BroadcastBranching

/-! # Exact finite-dimensional broadcast laws

An admissible finite configuration has the product of its edge-transition
probabilities. This identifies the finite restrictions of the constructed
infinite broadcast without postulating a finite-dimensional law.
-/
namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal ProbabilityTheory

/-- All vertices through height `h`. -/
def binaryBall (h : ℕ) : Finset BinaryNode :=
  (Finset.range (h + 1)).biUnion binaryLevel

@[simp] theorem mem_binaryBall (v : BinaryNode) (h : ℕ) :
    v ∈ binaryBall h ↔ v.length ≤ h := by
  simp [binaryBall]

/-- An admissible configuration on the finite binary core. -/
def BroadcastCompatible (i : Bool) (h : ℕ) (x : BinaryNode → Bool) : Prop :=
  x [] = i ∧ ∀ b v, (b :: v).length ≤ h → x v = true → x (b :: v) = false

def finiteBroadcastEvent (i : Bool) (h : ℕ) (x : BinaryNode → Bool) : Set BroadcastSpace :=
  {ω | ∀ v, v.length ≤ h → broadcastState i ω v = x v}

noncomputable def broadcastTransitionMass (p : unitInterval) (a b : Bool) : ℝ≥0∞ :=
  if a then (if b then 0 else 1)
  else if b then ENNReal.ofReal (p : ℝ) else ENNReal.ofReal (1 - (p : ℝ))

/-- The input constraint associated with a particular vertex of a proposed configuration. -/
def finiteInputEvent (x : BinaryNode → Bool) (v : BinaryNode) : Set BroadcastSpace :=
  if x v.tail then Set.univ else {ω | ω v = x v}

theorem finiteBroadcastEvent_compatible {i : Bool} {h : ℕ} {x : BinaryNode → Bool}
    {ω : BroadcastSpace} (hω : ω ∈ finiteBroadcastEvent i h x) : BroadcastCompatible i h x := by
  constructor
  · exact (hω [] (by simp)).symm
  · intro b v hv hx
    have hv' : v.length ≤ h := by simpa using (Nat.le_trans (Nat.le_succ v.length) hv)
    have hh := broadcast_hardCore i ω b v ((hω v hv').trans hx)
    exact (hω (b :: v) hv).symm.trans hh

theorem finiteBroadcastEvent_empty_of_incompatible {i : Bool} {h : ℕ} {x : BinaryNode → Bool}
    (hx : ¬ BroadcastCompatible i h x) : finiteBroadcastEvent i h x = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  exact fun _ hω => hx (finiteBroadcastEvent_compatible hω)

theorem finiteBroadcastEvent_eq_inputs {i : Bool} {h : ℕ} {x : BinaryNode → Bool}
    (hx : BroadcastCompatible i h x) :
    finiteBroadcastEvent i h x = ⋂ v ∈ (binaryBall h).erase [], finiteInputEvent x v := by
  ext ω
  simp only [Set.mem_iInter]
  constructor
  · intro hω v hv
    have hv0 := (Finset.mem_erase.mp hv).1
    have hvl := (mem_binaryBall v h).mp (Finset.mem_erase.mp hv).2
    cases v with
    | nil => contradiction
    | cons b v =>
      have hpar := hω v (by simpa using (Nat.le_trans (Nat.le_succ v.length) hvl))
      by_cases hh : x v = true
      · simp [finiteInputEvent, hh]
      · have hh' : x v = false := Bool.eq_false_of_not_eq_true hh
        have hchild := hω (b :: v) hvl
        simpa [finiteInputEvent, hh', broadcastState_child, hpar] using hchild
  · intro hω v hv
    induction v with
    | nil => simpa using hx.1.symm
    | cons b v ih =>
      have hp : v.length ≤ h := by simpa using (Nat.le_trans (Nat.le_succ v.length) hv)
      have hi := ih hp
      by_cases hh : x v = true
      · simp only [broadcastState_child, hi, hh, ite_true]
        exact (hx.2 b v hv hh).symm
      · have hh' : x v = false := Bool.eq_false_of_not_eq_true hh
        have hin := hω (b :: v) (Finset.mem_erase.mpr ⟨by simp, (mem_binaryBall _ _).mpr hv⟩)
        simpa [broadcastState_child, hi, hh', finiteInputEvent] using hin

theorem measurable_finiteInputEvent (x : BinaryNode → Bool) (v : BinaryNode) :
    MeasurableSet[MeasurableSpace.comap (fun ω : BroadcastSpace => ω v) inferInstance]
      (finiteInputEvent x v) := by
  by_cases hh : x v.tail = true
  · simp [finiteInputEvent, hh]
  · have hh' : x v.tail = false := Bool.eq_false_of_not_eq_true hh
    simp only [finiteInputEvent, hh', Bool.false_eq_true, ite_false]
    exact (comap_measurable (fun ω : BroadcastSpace => ω v)) (measurableSet_singleton (x v))

theorem input_probability (p : unitInterval) (v : BinaryNode) (b : Bool) :
    broadcastMeasure p {ω : BroadcastSpace | ω v = b} =
      if b then ENNReal.ofReal (p : ℝ) else ENNReal.ofReal (1 - (p : ℝ)) := by
  change broadcastMeasure p ((fun ω : BroadcastSpace => ω v) ⁻¹' {b}) = _
  have he := congrArg (fun μ : Measure Bool => μ {b}) (broadcast_input_law p v).map_eq
  rw [Measure.map_apply (measurable_pi_apply v) (measurableSet_singleton b)] at he
  cases b <;> simpa [bernoulliMeasure_apply, ENNReal.coe_nnreal_eq] using he

theorem finiteInputEvent_probability (p : unitInterval) {i : Bool} {h : ℕ}
    {x : BinaryNode → Bool} (hx : BroadcastCompatible i h x) (v : BinaryNode)
    (hv : v ∈ (binaryBall h).erase []) :
    broadcastMeasure p (finiteInputEvent x v) = broadcastTransitionMass p (x v.tail) (x v) := by
  have hvl := (mem_binaryBall v h).mp (Finset.mem_erase.mp hv).2
  have hv0 := (Finset.mem_erase.mp hv).1
  cases v with
  | nil => contradiction
  | cons b v =>
    by_cases hh : x v = true
    · have hchild := hx.2 b v hvl hh
      simp [finiteInputEvent, broadcastTransitionMass, hh, hchild]
    · have hh' : x v = false := Bool.eq_false_of_not_eq_true hh
      simp only [finiteInputEvent, broadcastTransitionMass, List.tail_cons, hh', Bool.false_eq_true,
        ite_false]
      exact input_probability p (b :: v) (x (b :: v))

/-- Exact joint probability of every admissible finite broadcast configuration. -/
theorem finite_broadcast_probability (p : unitInterval) {i : Bool} {h : ℕ}
    {x : BinaryNode → Bool} (hx : BroadcastCompatible i h x) :
    broadcastMeasure p (finiteBroadcastEvent i h x) =
      ∏ v ∈ (binaryBall h).erase [], broadcastTransitionMass p (x v.tail) (x v) := by
  rw [finiteBroadcastEvent_eq_inputs hx,
    (broadcast_inputs_independent p).meas_biInter (fun v _ => measurable_finiteInputEvent x v)]
  exact Finset.prod_congr rfl fun v hv => finiteInputEvent_probability p hx v hv

end SphericalTreeFailures
