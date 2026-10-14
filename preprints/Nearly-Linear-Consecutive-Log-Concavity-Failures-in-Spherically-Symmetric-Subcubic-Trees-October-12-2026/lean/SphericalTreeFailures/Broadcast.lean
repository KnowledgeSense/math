import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Process.Filtration
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! # Binary broadcast

The vertices are finite binary words, with the first letter removed when taking
parents. Independent Bernoulli inputs at all vertices produce the hard-core
broadcast with a prescribed root. The unused root input is harmless.
-/

namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal ProbabilityTheory

abbrev BinaryNode := List Bool
abbrev BroadcastSpace := BinaryNode → Bool

/-- The Bernoulli product space driving the infinite tree. -/
noncomputable def broadcastMeasure (p : unitInterval) : Measure BroadcastSpace :=
  Measure.infinitePi (fun _ : BinaryNode => bernoulliMeasure true false p)

instance (p : unitInterval) : IsProbabilityMeasure (broadcastMeasure p) := by
  unfold broadcastMeasure
  infer_instance

/-- The occupation state at a vertex, with prescribed root state `i`. -/
def broadcastState (i : Bool) (ω : BroadcastSpace) : BinaryNode → Bool
  | [] => i
  | b :: v => if broadcastState i ω v then false else ω (b :: v)

@[simp] theorem broadcastState_root (i : Bool) (ω : BroadcastSpace) :
    broadcastState i ω [] = i := rfl

@[simp] theorem broadcastState_child (i : Bool) (ω : BroadcastSpace) (b : Bool)
    (v : BinaryNode) :
    broadcastState i ω (b :: v) =
      if broadcastState i ω v then false else ω (b :: v) := rfl

/-- Real-valued occupation indicator. -/
def boolIndicator (b : Bool) : ℝ := if b then 1 else 0

@[simp] theorem boolIndicator_false : boolIndicator false = 0 := rfl
@[simp] theorem boolIndicator_true : boolIndicator true = 1 := rfl

@[simp] theorem boolIndicator_sq (b : Bool) : boolIndicator b ^ 2 = boolIndicator b := by
  cases b <;> norm_num [boolIndicator]

theorem boolIndicator_nonneg (b : Bool) : 0 ≤ boolIndicator b := by
  cases b <;> norm_num [boolIndicator]

theorem boolIndicator_le_one (b : Bool) : boolIndicator b ≤ 1 := by
  cases b <;> norm_num [boolIndicator]

noncomputable def stationaryProbability (p : ℝ) : ℝ := p / (1 + p)
def censusScale (p : ℝ) : ℝ := 2 * p

/-- The transition law from an occupied vertex is deterministic; from a vacant
vertex it is Bernoulli. -/
noncomputable def broadcastKernel (p : unitInterval) (i : Bool) : Measure Bool :=
  if i then Measure.dirac false else bernoulliMeasure true false p

/-- A single generation of the infinite binary tree. -/
def binaryLevel : ℕ → Finset BinaryNode
  | 0 => {[]}
  | h + 1 => (binaryLevel h).map ⟨List.cons false, fun _ _ h => List.cons.inj h |>.2⟩ ∪
      (binaryLevel h).map ⟨List.cons true, fun _ _ h => List.cons.inj h |>.2⟩

@[simp] theorem mem_binaryLevel (v : BinaryNode) (h : ℕ) :
    v ∈ binaryLevel h ↔ v.length = h := by
  induction h generalizing v with
  | zero => simp [binaryLevel]
  | succ h ih =>
    cases v with
    | nil => simp [binaryLevel]
    | cons b v =>
      simp only [binaryLevel, mem_union, mem_map, List.length_cons, Nat.add_right_cancel_iff]
      change ((∃ a, a ∈ binaryLevel h ∧ false :: a = b :: v) ∨
        ∃ a, a ∈ binaryLevel h ∧ true :: a = b :: v) ↔ v.length = h
      cases b <;> simp [ih]

theorem binaryLevel_disjoint (h : ℕ) :
    Disjoint ((binaryLevel h).map ⟨List.cons false, fun _ _ h => List.cons.inj h |>.2⟩)
      ((binaryLevel h).map ⟨List.cons true, fun _ _ h => List.cons.inj h |>.2⟩) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  obtain ⟨x, _, hx⟩ := mem_map.mp ha
  obtain ⟨y, _, hy⟩ := mem_map.mp hb
  have hh := hx.trans hy.symm
  change false :: x = true :: y at hh
  simp at hh

@[simp] theorem card_binaryLevel (h : ℕ) : (binaryLevel h).card = 2 ^ h := by
  induction h with
  | zero => simp [binaryLevel]
  | succ h ih =>
    rw [binaryLevel, card_union_of_disjoint (binaryLevel_disjoint h)]
    simp [ih, pow_succ, Nat.mul_two]

theorem sum_binaryLevel_succ {A : Type*} [AddCommMonoid A] (f : BinaryNode → A) (h : ℕ) :
    ∑ v ∈ binaryLevel (h + 1), f v =
      ∑ v ∈ binaryLevel h, (f (false :: v) + f (true :: v)) := by
  simp only [binaryLevel, sum_union (binaryLevel_disjoint h), sum_map]
  exact (sum_add_distrib).symm

theorem measurable_broadcastState (i : Bool) (v : BinaryNode) :
    Measurable (fun ω : BroadcastSpace => broadcastState i ω v) := by
  induction v with
  | nil => exact measurable_const
  | cons b v ih =>
    simp only [broadcastState]
    exact Measurable.ite (ih (measurableSet_singleton true)) measurable_const (measurable_pi_apply _)

theorem measurable_boolIndicator : Measurable boolIndicator := measurable_of_finite _

theorem broadcast_hardCore (i : Bool) (ω : BroadcastSpace) (b : Bool) (v : BinaryNode)
    (hv : broadcastState i ω v = true) : broadcastState i ω (b :: v) = false := by
  simp [hv]

theorem broadcast_indicator_child (i : Bool) (ω : BroadcastSpace) (b : Bool) (v : BinaryNode) :
    boolIndicator (broadcastState i ω (b :: v)) =
      (1 - boolIndicator (broadcastState i ω v)) * boolIndicator (ω (b :: v)) := by
  cases h : broadcastState i ω v <;> simp [h]

theorem broadcast_inputs_independent (p : unitInterval) :
    iIndepFun (fun v (ω : BroadcastSpace) => ω v) (broadcastMeasure p) :=
  iIndepFun_infinitePi (X := fun _ b => b) (fun _ => measurable_id)

theorem broadcast_input_law (p : unitInterval) (v : BinaryNode) :
    HasLaw (fun ω : BroadcastSpace => ω v) (bernoulliMeasure true false p)
      (broadcastMeasure p) := by
  exact ⟨(measurable_pi_apply v).aemeasurable, Measure.infinitePi_map_eval _ v⟩

/-- Centered sum of the occupations in generation `h`. -/
noncomputable def census (p : ℝ) (i : Bool) (h : ℕ) (ω : BroadcastSpace) : ℝ :=
  ∑ v ∈ binaryLevel h, (boolIndicator (broadcastState i ω v) - stationaryProbability p)

/-- The signed census normalization. -/
noncomputable def censusMartingale (p : ℝ) (i : Bool) (h : ℕ) (ω : BroadcastSpace) : ℝ :=
  ((-censusScale p) ^ h)⁻¹ * census p i h ω

@[simp] theorem census_zero (p : ℝ) (i : Bool) (ω : BroadcastSpace) :
    census p i 0 ω = boolIndicator i - stationaryProbability p := by
  simp [census, binaryLevel]

@[simp] theorem censusMartingale_zero (p : ℝ) (i : Bool) (ω : BroadcastSpace) :
    censusMartingale p i 0 ω = boolIndicator i - stationaryProbability p := by
  simp [censusMartingale]

/-- Inputs revealed through generation `h`. -/
def inputFiltration : Filtration ℕ (inferInstance : MeasurableSpace BroadcastSpace) where
  seq h := ⨆ v : BinaryNode, ⨆ (_ : v.length ≤ h),
    MeasurableSpace.comap (fun ω : BroadcastSpace => ω v) inferInstance
  mono' := by
    intro h k hhk
    exact iSup_le fun v => iSup_le fun hv => le_iSup_of_le v (le_iSup_of_le (hv.trans hhk) le_rfl)
  le' := by
    intro h
    exact iSup_le fun v => iSup_le fun _ => (measurable_pi_apply v).comap_le

theorem measurable_input_at (h : ℕ) (v : BinaryNode) (hv : v.length ≤ h) :
    @Measurable BroadcastSpace Bool (inputFiltration h) inferInstance (fun ω => ω v) := by
  apply measurable_iff_comap_le.mpr
  exact le_iSup_of_le v (le_iSup_of_le hv le_rfl)

theorem measurable_broadcastState_at (i : Bool) (h : ℕ) (v : BinaryNode)
    (hv : v.length ≤ h) :
    @Measurable BroadcastSpace Bool (inputFiltration h) inferInstance
      (fun ω => broadcastState i ω v) := by
  induction v with
  | nil => exact measurable_const
  | cons b v ih =>
    have hp : v.length ≤ h := le_trans (Nat.le_succ _) hv
    exact Measurable.ite ((ih hp) (measurableSet_singleton true))
      measurable_const (measurable_input_at h (b :: v) hv)

theorem fresh_input_independent (p : unitInterval) (h : ℕ) (v : BinaryNode)
    (hv : h < v.length) :
    Indep (MeasurableSpace.comap (fun ω : BroadcastSpace => ω v) inferInstance)
      (inputFiltration h) (broadcastMeasure p) := by
  have hi := indep_iSup_of_disjoint
    (fun v : BinaryNode => (measurable_pi_apply v).comap_le)
    (broadcast_inputs_independent p).iIndep
    (S := {v}) (T := {w : BinaryNode | w.length ≤ h})
    (by simpa using (not_le.mpr hv) : Disjoint ({v} : Set BinaryNode) {w | w.length ≤ h})
  simpa [inputFiltration] using hi

/-- The sigma-field carried by an arbitrary collection of inputs. -/
@[instance_reducible] def inputSigma (S : Set BinaryNode) : MeasurableSpace BroadcastSpace :=
  ⨆ v ∈ S, MeasurableSpace.comap (fun ω : BroadcastSpace => ω v) inferInstance

theorem inputSigma_le (S : Set BinaryNode) :
    inputSigma S ≤ (inferInstance : MeasurableSpace BroadcastSpace) :=
  iSup_le fun v => iSup_le fun _ => (measurable_pi_apply v).comap_le

theorem measurable_input_in {S : Set BinaryNode} {v : BinaryNode} (hv : v ∈ S) :
    @Measurable BroadcastSpace Bool (inputSigma S) inferInstance (fun ω => ω v) :=
  measurable_iff_comap_le.mpr (le_iSup_of_le v (le_iSup_of_le hv le_rfl))

theorem inputSigma_independent (p : unitInterval) {S T : Set BinaryNode} (hST : Disjoint S T) :
    Indep (inputSigma S) (inputSigma T) (broadcastMeasure p) :=
  indep_iSup_of_disjoint (fun v : BinaryNode => (measurable_pi_apply v).comap_le)
    (broadcast_inputs_independent p).iIndep hST

end SphericalTreeFailures
