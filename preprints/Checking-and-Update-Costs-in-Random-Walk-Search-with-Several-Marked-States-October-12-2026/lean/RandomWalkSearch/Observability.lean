import RandomWalkSearch.CanonicalRandomness
import Mathlib.Tactic.DeriveCountable

/-! # Measurability of genuine arbitrary deterministic policies

Every deterministic policy on a countable history space is measurable. This
establishes genuine expectations for the explicitly constructed endpoint
algorithms on the canonical probability space.
-/

namespace RandomWalkSearch
open scoped ENNReal

variable {X : Type*}
deriving instance Countable for Action
deriving instance Countable for Event

theorem action_countable [Countable X] : Countable (Action X) := inferInstance

theorem event_countable [Countable X] : Countable (Event X) := inferInstance

instance actionMeasurableSpace : MeasurableSpace (Action X) := ⊤
instance actionMeasurableSingletonClass : MeasurableSingletonClass (Action X) := ⟨fun _ => trivial⟩

instance historyMeasurableSpace : MeasurableSpace (History X) := ⊤
instance historyMeasurableSingletonClass : MeasurableSingletonClass (History X) := ⟨fun _ => trivial⟩

namespace Cycle
variable {k : ℕ} [NeZero (N k)]
variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_run_fixed_policy (p : Policy (Vertex k))
    (z : Ω → ℕ → Vertex k) (w : Ω → ℕ → ℕ → Fin 4)
    (hz : ∀ i, Measurable fun ω => z ω i)
    (hw : ∀ i j, Measurable fun ω => w ω i j) (o : Oracle (Vertex k)) (n : ℕ) :
    Measurable fun ω => run p (lazyTapes (z ω) (w ω)) o n := by
  have hstep : Measurable fun v : Ω × History (Vertex k) =>
      step p (lazyTapes (z v.1) (w v.1)) o v.2 := by
    apply measurable_from_prod_countable_left
    intro h
    simp only [step]
    split
    · exact measurable_const
    · cases ha : p h with
      | setup =>
        exact (measurable_of_countable (fun x : Vertex k => Event.setup x :: h)).comp (hz h.setups)
      | update i x =>
        exact (measurable_of_countable (fun q : Fin 4 =>
          Event.update i x (x + (increment q).value) :: h)).comp (hw i (h.trajectoryUpdates i))
      | check x =>
        change Measurable (fun _ : Ω => Event.check x (o x) :: h)
        exact measurable_const
      | output x =>
        change Measurable (fun _ : Ω => Event.output x :: h)
        exact measurable_const
      | think =>
        change Measurable (fun _ : Ω => Event.think :: h)
        exact measurable_const
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact hstep.comp (measurable_id.prodMk ih)

/-- Actual success is a countable union of finite, measurable output events. -/
theorem measurable_successScore_fixed_policy (p : Policy (Vertex k))
    (z : Ω → ℕ → Vertex k) (w : Ω → ℕ → ℕ → Fin 4)
    (hz : ∀ i, Measurable fun ω => z ω i)
    (hw : ∀ i j, Measurable fun ω => w ω i j) (o : Oracle (Vertex k)) :
    Measurable fun ω => successScore p (lazyTapes (z ω) (w ω)) o := by
  classical
  let f : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    if ∃x, Event.output (some x) ∈ run p (lazyTapes (z ω) (w ω)) o n ∧ o x=true then 1 else 0
  have hrep : (fun ω => successScore p (lazyTapes (z ω) (w ω)) o) = fun ω => ⨆n, f n ω := by
    funext ω
    by_cases hs : Succeeds p (lazyTapes (z ω) (w ω)) o
    · simp only [successScore,hs,ite_true]
      apply le_antisymm
      · obtain ⟨n,x,hx,ho⟩ := hs
        have hf : f n ω=1 := by simp only [f, show ∃x, Event.output (some x) ∈ run p (lazyTapes (z ω) (w ω)) o n ∧ o x=true from ⟨x,hx,ho⟩, ite_true]
        rw [←hf]
        exact le_iSup (fun j => f j ω) n
      · apply iSup_le
        intro n
        dsimp [f]
        split <;> simp
    · simp only [successScore,hs,ite_false]
      symm
      apply le_antisymm
      · apply iSup_le
        intro n
        have hn : ¬∃x, Event.output (some x) ∈ run p (lazyTapes (z ω) (w ω)) o n ∧ o x=true := by
          rintro ⟨x,hx,ho⟩
          exact hs ⟨n,x,hx,ho⟩
        simp only [f,hn,ite_false,le_refl]
      · exact bot_le
  rw [hrep]
  apply Measurable.iSup
  intro n
  exact (measurable_of_countable (fun h : History (Vertex k) =>
    if ∃x, Event.output (some x) ∈ h ∧ o x=true then (1:ℝ≥0∞) else 0)).comp
      (measurable_run_fixed_policy p z w hz hw o n)

theorem fixed_policy_observable (p : Policy (Vertex k))
    (z : Ω → ℕ → Vertex k) (w : Ω → ℕ → ℕ → Fin 4)
    (hz : ∀ i, Measurable fun ω => z ω i)
    (hw : ∀ i j, Measurable fun ω => w ω i j) :
    (Randomized.mk (fun _ => p) z w).Observable := by
  constructor
  · intro a
    exact measurable_successScore_fixed_policy p z w hz hw (oracle a)
  · intro a
    apply Measurable.iSup
    intro n
    exact (measurable_of_countable (fun h : History (Vertex k) => (h.updates : ℝ≥0∞))).comp
      (measurable_run_fixed_policy p z w hz hw (oracle a) n)
  · intro a
    apply Measurable.iSup
    intro n
    exact (measurable_of_countable (fun h : History (Vertex k) => (h.checks : ℝ≥0∞))).comp
      (measurable_run_fixed_policy p z w hz hw (oracle a) n)

/-- In particular all explicit endpoint policies have measurable true costs
and success events in their concrete uniform-setup/iid-tape model. -/
theorem Canonical.algorithm_observable (p : Policy (Vertex k)) :
    (Canonical.algorithm k p).Observable := by
  apply fixed_policy_observable
  · intro _
    exact measurable_fst
  · intro _ j
    exact (measurable_pi_apply j).comp measurable_snd

/-- The usual measurable private-randomness model: every decision at a fixed
finite history, and every setup/increment coordinate, is a random variable. -/
structure Randomized.MeasurableCoordinates (A : Randomized k Ω) : Prop where
  policy : ∀ h, Measurable fun ω => A.policy ω h
  setups : ∀ i, Measurable fun ω => A.setups ω i
  increments : ∀ i j, Measurable fun ω => A.increments ω i j

theorem Randomized.measurable_run (A : Randomized k Ω)
    (hA : A.MeasurableCoordinates) (o : Oracle (Vertex k)) (n : ℕ) :
    Measurable fun ω => run (A.policy ω) (A.tapes ω) o n := by
  have hresponse (h : History (Vertex k)) :
      Measurable fun v : Ω × Action (Vertex k) => respond (A.tapes v.1) o h v.2 :: h := by
    apply measurable_from_prod_countable_left
    intro a
    cases a with
    | setup =>
      exact (measurable_of_countable (fun x : Vertex k => Event.setup x :: h)).comp (hA.setups h.setups)
    | update i x =>
      exact (measurable_of_countable (fun q : Fin 4 =>
        Event.update i x (x + (increment q).value) :: h)).comp (hA.increments i (h.trajectoryUpdates i))
    | check x =>
      change Measurable (fun _ : Ω => Event.check x (o x) :: h)
      exact measurable_const
    | output x =>
      change Measurable (fun _ : Ω => Event.output x :: h)
      exact measurable_const
    | think =>
      change Measurable (fun _ : Ω => Event.think :: h)
      exact measurable_const
  have hstep : Measurable fun v : Ω × History (Vertex k) =>
      step (A.policy v.1) (A.tapes v.1) o v.2 := by
    apply measurable_from_prod_countable_left
    intro h
    simp only [step]
    split
    · exact measurable_const
    · exact (hresponse h).comp (measurable_id.prodMk (hA.policy h))
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact hstep.comp (measurable_id.prodMk ih)

/-- The observable success and extended costs follow for fully randomized,
fully adaptive policies from coordinate measurability alone. -/
theorem Randomized.MeasurableCoordinates.observable {A : Randomized k Ω}
    (hA : A.MeasurableCoordinates) : A.Observable := by
  classical
  constructor
  · intro a
    let f : ℕ → Ω → ℝ≥0∞ := fun n ω =>
      if ∃x, Event.output (some x) ∈ run (A.policy ω) (A.tapes ω) (oracle a) n ∧ oracle a x=true
        then 1 else 0
    have hrep : (fun ω => successScore (A.policy ω) (A.tapes ω) (oracle a)) = fun ω => ⨆n, f n ω := by
      funext ω
      by_cases hs : Succeeds (A.policy ω) (A.tapes ω) (oracle a)
      · simp only [successScore,hs,ite_true]
        apply le_antisymm
        · obtain ⟨n,x,hx,ho⟩ := hs
          have hf : f n ω=1 := by
            simp only [f, show ∃x, Event.output (some x) ∈ run (A.policy ω) (A.tapes ω) (oracle a) n ∧
              oracle a x=true from ⟨x,hx,ho⟩, ite_true]
          rw [←hf]
          exact le_iSup (fun j => f j ω) n
        · apply iSup_le
          intro n
          dsimp [f]
          split <;> simp
      · simp only [successScore,hs,ite_false]
        symm
        apply le_antisymm
        · apply iSup_le
          intro n
          have hn : ¬∃x, Event.output (some x) ∈ run (A.policy ω) (A.tapes ω) (oracle a) n ∧ oracle a x=true := by
            rintro ⟨x,hx,ho⟩
            exact hs ⟨n,x,hx,ho⟩
          simp only [f,hn,ite_false,le_refl]
        · exact bot_le
    rw [hrep]
    apply Measurable.iSup
    intro n
    exact (measurable_of_countable (fun h : History (Vertex k) =>
      if ∃x, Event.output (some x) ∈ h ∧ oracle a x=true then (1:ℝ≥0∞) else 0)).comp
        (A.measurable_run hA (oracle a) n)
  · intro a
    apply Measurable.iSup
    intro n
    exact (measurable_of_countable (fun h : History (Vertex k) => (h.updates : ℝ≥0∞))).comp
      (A.measurable_run hA (oracle a) n)
  · intro a
    apply Measurable.iSup
    intro n
    exact (measurable_of_countable (fun h : History (Vertex k) => (h.checks : ℝ≥0∞))).comp
      (A.measurable_run hA (oracle a) n)

omit [NeZero (N k)] in
theorem Canonical.algorithm_measurableCoordinates (p : Policy (Vertex k)) :
    (Canonical.algorithm k p).MeasurableCoordinates := by
  constructor
  · intro _
    exact measurable_const
  · intro _
    exact measurable_fst
  · intro _ j
    exact (measurable_pi_apply j).comp measurable_snd

end Cycle
end RandomWalkSearch
