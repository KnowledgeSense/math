import RandomWalkSearch.Probability

/-! # Genuine consecutive-trajectory access

The endpoint table is reconstructed from actual setup and update events.
Each update must start at the current endpoint of an existing trajectory.
-/

namespace RandomWalkSearch

variable {X : Type*}

namespace History

def endpoint : History X → ℕ → Option X
  | [] => fun _ => none
  | .setup x :: h => Function.update (endpoint h) (setups h) (some x)
  | .update i _ y :: h => Function.update (endpoint h) i (some y)
  | _ :: h => endpoint h

@[simp] theorem trajectoryUpdates_cons_setup (i : ℕ) (x : X) (h : History X) :
    trajectoryUpdates (.setup x :: h) i = trajectoryUpdates h i := by
  simp [trajectoryUpdates, Event.isTrajectoryUpdate]

@[simp] theorem trajectoryUpdates_cons_update (i j : ℕ) (x y : X) (h : History X) :
    trajectoryUpdates (.update j x y :: h) i = trajectoryUpdates h i + if i = j then 1 else 0 := by
  simp [trajectoryUpdates, List.countP_cons, Event.isTrajectoryUpdate, Nat.add_comm]

theorem trajectoryUpdates_le_updates (i : ℕ) (h : History X) :
    h.trajectoryUpdates i ≤ h.updates := by
  apply List.countP_mono_left
  intro e _ he
  cases e <;> simp_all [Event.isTrajectoryUpdate, Event.isUpdate]

end History

/-- The trajectory identifier is its setup index, numbered from zero. -/
def Extends (h : History X) : Action X → Prop
  | .update i x => i < h.setups ∧ h.endpoint i = some x
  | _ => True

variable [DecidableEq X]

def Consecutive {A : Type*} (family : A → Oracle X) (b : ℕ)
    (p : Policy X) (r : Tapes X) : Prop :=
  Restoration family b p r ∧
    ∀ a n, (run p r (family a) n).halted = false →
      Extends (run p r (family a) n) (p (run p r (family a) n))

theorem complete_extends {A : Type*} (family : A → Oracle X) (b : ℕ)
    (p : Policy X) (r : Tapes X) (hp : Consecutive family b p r)
    (q : Oracle X) (n : ℕ) (hn : (run (complete family p) r q n).halted = false) :
    Extends (run (complete family p) r q n)
      (complete family p (run (complete family p) r q n)) :=
  complete_operation_safe family p r Extends (fun _ => trivial) hp.2 q n hn

namespace Cycle

variable {k : ℕ}

/-- Actual integer lift of a single update tape. -/
def walkPosition (w : ℕ → Fin 4) : ℕ → ℤ
  | 0 => 0
  | n + 1 => walkPosition w n + (increment (w n)).value

@[simp] theorem walkPosition_zero (w : ℕ → Fin 4) : walkPosition w 0 = 0 := rfl
@[simp] theorem walkPosition_succ (w : ℕ → Fin 4) (n : ℕ) :
    walkPosition w (n + 1) = walkPosition w n + (increment (w n)).value := rfl

/-- No update symbol can be consumed from a trajectory that has not been set up. -/
theorem run_unused_trajectory (p : Policy (Vertex k))
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (o : Oracle (Vertex k))
    (he : ∀ n, (run p (lazyTapes z w) o n).halted = false →
      Extends (run p (lazyTapes z w) o n) (p (run p (lazyTapes z w) o n)))
    (n i : ℕ) (hi : (run p (lazyTapes z w) o n).setups ≤ i) :
    (run p (lazyTapes z w) o n).trajectoryUpdates i = 0 := by
  induction n with
  | zero => simp [History.trajectoryUpdates]
  | succ n ih =>
    simp only [run_succ, step] at hi ⊢
    by_cases hactive : (run p (lazyTapes z w) o n).halted = true
    · simp only [hactive, ite_true] at hi ⊢
      exact ih hi
    · simp only [hactive, Bool.false_eq_true, ite_false] at hi ⊢
      have he' := he n (Bool.eq_false_iff.mpr hactive)
      cases ha : p (run p (lazyTapes z w) o n) with
      | setup =>
        simp only [respond, History.trajectoryUpdates_cons_setup]
        apply ih
        have hi' : (run p (lazyTapes z w) o n).setups + 1 ≤ i := by
          simpa [ha, respond, History.setups, List.countP_cons, Event.isSetup] using hi
        omega
      | update j x =>
        have hj : j < (run p (lazyTapes z w) o n).setups := by
          have h := he'
          rw [ha] at h
          exact h.1
        have hi' : (run p (lazyTapes z w) o n).setups ≤ i := by
          simpa [ha, respond, History.setups, List.countP_cons, Event.isSetup] using hi
        have hij : i ≠ j := by omega
        simp [respond, History.trajectoryUpdates_cons_update, hij, ih hi']
      | check x =>
        simp [ha, respond, History.setups, Event.isSetup] at hi
        simpa [respond, History.trajectoryUpdates, Event.isTrajectoryUpdate] using ih hi
      | output x =>
        simp [ha, respond, History.setups, Event.isSetup] at hi
        simpa [respond, History.trajectoryUpdates, Event.isTrajectoryUpdate] using ih hi
      | think =>
        simp [ha, respond, History.setups, Event.isSetup] at hi
        simpa [respond, History.trajectoryUpdates, Event.isTrajectoryUpdate] using ih hi

/-- The endpoint of each actual trajectory is exactly its setup plus its
private-tape prefix. Adaptive choices only select how long a prefix to use. -/
theorem run_endpoint (p : Policy (Vertex k))
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (o : Oracle (Vertex k))
    (he : ∀ n, (run p (lazyTapes z w) o n).halted = false →
      Extends (run p (lazyTapes z w) o n) (p (run p (lazyTapes z w) o n)))
    (n i : ℕ) (hi : i < (run p (lazyTapes z w) o n).setups) :
    (run p (lazyTapes z w) o n).endpoint i =
      some (z i + (walkPosition (w i) ((run p (lazyTapes z w) o n).trajectoryUpdates i) : ℤ)) := by
  induction n with
  | zero => simp [History.setups] at hi
  | succ n ih =>
    simp only [run_succ, step] at hi ⊢
    by_cases hactive : (run p (lazyTapes z w) o n).halted = true
    · simp only [hactive, ite_true] at hi ⊢
      exact ih hi
    · simp only [hactive, Bool.false_eq_true, ite_false] at hi ⊢
      have he' := he n (Bool.eq_false_iff.mpr hactive)
      cases ha : p (run p (lazyTapes z w) o n) with
      | setup =>
        have hi' : i < (run p (lazyTapes z w) o n).setups + 1 := by
          simpa [ha, respond, History.setups, List.countP_cons, Event.isSetup] using hi
        by_cases heq : i = (run p (lazyTapes z w) o n).setups
        · subst i
          simp only [respond, History.endpoint, Function.update_self,
            History.trajectoryUpdates_cons_setup, run_unused_trajectory p z w o he n _ le_rfl]
          simp [lazyTapes]
        · have hil : i < (run p (lazyTapes z w) o n).setups := by omega
          simpa [respond, History.endpoint, heq] using ih hil
      | update j x =>
        have he'' : j < (run p (lazyTapes z w) o n).setups ∧
            (run p (lazyTapes z w) o n).endpoint j = some x := by
          simpa [ha, Extends] using he'
        have hi' : i < (run p (lazyTapes z w) o n).setups := by
          simpa [ha, respond, History.setups, List.countP_cons, Event.isSetup] using hi
        by_cases hij : i = j
        · subst i
          have hx : x = z j + (walkPosition (w j)
              ((run p (lazyTapes z w) o n).trajectoryUpdates j) : ℤ) := by
            exact Option.some.inj (he''.2.symm.trans (ih he''.1))
          simp [respond, History.endpoint, History.trajectoryUpdates_cons_update,
            lazyTapes, hx, add_assoc]
        · simpa [respond, History.endpoint, History.trajectoryUpdates_cons_update, hij] using ih hi'
      | check x =>
        simp [ha, respond, History.setups, Event.isSetup] at hi
        simpa [respond, History.endpoint, History.trajectoryUpdates, Event.isTrajectoryUpdate] using ih hi
      | output x =>
        simp [ha, respond, History.setups, Event.isSetup] at hi
        simpa [respond, History.endpoint, History.trajectoryUpdates, Event.isTrajectoryUpdate] using ih hi
      | think =>
        simp [ha, respond, History.setups, Event.isSetup] at hi
        simpa [respond, History.endpoint, History.trajectoryUpdates, Event.isTrajectoryUpdate] using ih hi

end Cycle
end RandomWalkSearch
