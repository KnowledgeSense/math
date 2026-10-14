import RandomWalkSearch.EndpointCoverage
import RandomWalkSearch.RightWait

/-! Actual restoration endpoint policies: retry from a stored frontier until a rightward move. -/
noncomputable section
namespace RandomWalkSearch.Cycle
open EndpointPolicy LazyWalk

variable {k : ℕ}

/-- The stored frontier advances only when an update returns its right neighbour. -/
def frontier : History (Vertex k) → Option (Vertex k)
  | [] => none
  | .setup x :: _ => some x
  | .update _ x y :: h => if y = x + 1 then some y else frontier h
  | _ :: h => frontier h

theorem frontier_mem_visited {h : History (Vertex k)} {x : Vertex k}
    (hx : frontier h = some x) : x ∈ h.visited := by
  induction h with
  | nil => cases hx
  | cons e h ih =>
    cases e with
    | setup y =>
      simp only [frontier, Option.some.injEq] at hx
      subst x
      simp
    | update i y z =>
      simp only [frontier] at hx
      split at hx
      · simp only [Option.some.injEq] at hx
        subst x
        simp
      · rw [History.visited_cons_update]
        exact Finset.mem_insert_of_mem (ih hx)
    | check y a => exact ih hx
    | output y => exact ih hx
    | think => exact ih hx

def restorationCollect (cover : Finset (Vertex k) → Prop)
    (tests : Finset (Vertex k) → Finset (Vertex k)) : Policy (Vertex k) := fun h =>
  match collectThenCheck cover tests h with
  | .update _ _ => match frontier h with
    | some x => .update 0 x
    | none => .output none
  | a => a

theorem restorationCollect_cover (cover : Finset (Vertex k) → Prop)
    (tests : Finset (Vertex k) → Finset (Vertex k)) (h : History (Vertex k))
    (hc : cover h.visited) : restorationCollect cover tests h = collectThenCheck cover tests h := by
  unfold restorationCollect
  cases ha : collectThenCheck cover tests h with
  | setup => rfl
  | update i x =>
    unfold collectThenCheck at ha
    split at ha
    · cases ha
    · split at ha
      · cases ha
      · split at ha <;> cases ha
  | check x => rfl
  | output x => rfl
  | think => rfl

theorem restorationCollect_local (cover : Finset (Vertex k) → Prop)
    (tests : Finset (Vertex k) → Finset (Vertex k)) (ht : ∀ v, tests v ⊆ v)
    (h : History (Vertex k)) : Local h (restorationCollect cover tests h) := by
  have hl := collectThenCheck_local cover tests ht h
  unfold restorationCollect
  cases ha : collectThenCheck cover tests h with
  | setup => trivial
  | update i x =>
    change Local h (match frontier h with | some y => .update 0 y | none => .output none)
    cases hy : frontier h with
    | some y => exact frontier_mem_visited hy
    | none => trivial
  | check x => simpa only [ha] using hl
  | output x => trivial
  | think => trivial

theorem restorationCollect_setupBound (cover : Finset (Vertex k) → Prop)
    (tests : Finset (Vertex k) → Finset (Vertex k)) (h : History (Vertex k)) :
    SetupBound 1 h (restorationCollect cover tests h) := by
  have hs := collectThenCheck_setupBound cover tests h
  unfold restorationCollect
  cases ha : collectThenCheck cover tests h with
  | setup => simpa only [ha] using hs
  | update i x =>
    change SetupBound 1 h (match frontier h with | some y => .update 0 y | none => .output none)
    cases frontier h <;> trivial
  | check x => trivial
  | output x => trivial
  | think => trivial

theorem restorationCollect_restoration (cover : Finset (Vertex k) → Prop)
    (tests : Finset (Vertex k) → Finset (Vertex k)) (ht : ∀ v, tests v ⊆ v)
    (r : Tapes (Vertex k)) : Restoration oracle 1 (restorationCollect cover tests) r := by
  intro a n _
  exact ⟨restorationCollect_local cover tests ht _, restorationCollect_setupBound cover tests _⟩

def frontierPosition (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (n : ℕ) : Vertex k :=
  z 0 + (rightCountStream (w 0) n : ℕ)

def frontierTarget (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (n : ℕ) : Vertex k :=
  frontierPosition z w n + (increment (w 0 n)).value

def frontierTrail (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) : ℕ → History (Vertex k)
  | 0 => [.setup (z 0)]
  | n + 1 => .update 0 (frontierPosition z w n) (frontierTarget z w n) :: frontierTrail z w n

theorem frontierTarget_right (hN : 2 < N k) (z : ℕ → Vertex k)
    (w : ℕ → ℕ → Fin 4) (n : ℕ) :
    frontierTarget z w n = frontierPosition z w n + 1 ↔ w 0 n = 1 := by
  have htwo : (2 : Vertex k) ≠ 0 := by
    intro h
    have hd : N k ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (N k)).mp h
    have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
    omega
  have hone : (1 : Vertex k) ≠ 0 := by
    intro h
    have hc := congrArg (fun x : Vertex k => x + x) h
    norm_num at hc
    exact htwo hc
  unfold frontierTarget
  rw [add_right_inj]
  generalize hq : w 0 n = q
  fin_cases q <;> norm_num [increment, Increment.value]
  · intro h
    apply htwo
    calc (2 : Vertex k) = 1 + 1 := by norm_num
         _ = -1 + 1 := by rw [h]
         _ = 0 := neg_add_cancel _
  all_goals exact hone.symm

@[simp] theorem frontierTrail_setups (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (n : ℕ) :
    (frontierTrail z w n).setups = 1 := by
  induction n with
  | zero => simp [frontierTrail, History.setups, Event.isSetup]
  | succ n ih => simpa [frontierTrail, History.setups, Event.isSetup] using ih

@[simp] theorem frontierTrail_updates (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (n : ℕ) :
    (frontierTrail z w n).updates = n := by
  induction n with
  | zero => simp [frontierTrail, History.updates, Event.isUpdate]
  | succ n ih =>
    simp only [frontierTrail, History.updates, List.countP_cons, Event.isUpdate, ite_true]
    exact congrArg (· + 1) ih

@[simp] theorem frontierTrail_trajectoryUpdates (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (n : ℕ) :
    (frontierTrail z w n).trajectoryUpdates 0 = n := by
  induction n with
  | zero => simp [frontierTrail, History.trajectoryUpdates, Event.isTrajectoryUpdate]
  | succ n ih => simpa [frontierTrail, History.trajectoryUpdates, Event.isTrajectoryUpdate] using ih

@[simp] theorem frontierTrail_checks (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (n : ℕ) :
    (frontierTrail z w n).checks = 0 := by
  induction n with
  | zero => simp [frontierTrail, History.checks, Event.isCheck]
  | succ n ih => simpa [frontierTrail, History.checks, Event.isCheck] using ih

@[simp] theorem frontierTrail_checked (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (n : ℕ) :
    (frontierTrail z w n).checked = ∅ := by
  induction n with
  | zero => simp [frontierTrail, History.checked, Event.checkedVertex]
  | succ n ih => simpa [frontierTrail, History.checked, Event.checkedVertex] using ih

@[simp] theorem frontierTrail_positives (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (n : ℕ) :
    positives (frontierTrail z w n) = ∅ := by
  induction n with
  | zero => simp [frontierTrail, positives, positiveVertex]
  | succ n ih => simpa [frontierTrail, positives, positiveVertex] using ih

@[simp] theorem frontierTrail_halted (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (n : ℕ) :
    (frontierTrail z w n).halted = false := by
  induction n with
  | zero => simp [frontierTrail, History.halted, Event.isOutput]
  | succ n ih => simpa [frontierTrail, History.halted, Event.isOutput] using ih

theorem frontierTrail_frontier (hN : 2 < N k) (z : ℕ → Vertex k)
    (w : ℕ → ℕ → Fin 4) (n : ℕ) :
    frontier (frontierTrail z w n) = some (frontierPosition z w n) := by
  induction n with
  | zero => simp [frontierTrail, frontier, frontierPosition, rightCountStream, rightCount]
  | succ n ih =>
    simp only [frontierTrail, frontier, frontierTarget_right hN, ih]
    by_cases hq : w 0 n = 1
    · simp [hq, frontierTarget, frontierPosition, rightCountStream, rightCount, prefixTape,
        increment, Increment.value, add_assoc]
    · simp [hq, frontierPosition, rightCountStream, rightCount, prefixTape]

theorem frontierTrail_current (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (n : ℕ) :
    ∃ x, current (frontierTrail z w n) = some x := by
  cases n with
  | zero => exact ⟨z 0, rfl⟩
  | succ n => exact ⟨frontierTarget z w n, rfl⟩

theorem restorationCollect_update (hN : 2 < N k) (cover : Finset (Vertex k) → Prop)
    (tests : Finset (Vertex k) → Finset (Vertex k))
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (n : ℕ)
    (hc : ¬cover (frontierTrail z w n).visited) :
    restorationCollect cover tests (frontierTrail z w n) = .update 0 (frontierPosition z w n) := by
  obtain ⟨x, hx⟩ := frontierTrail_current z w n
  simp [restorationCollect, collectThenCheck, pick, hc, hx, frontierTrail_frontier hN]

theorem restoration_run_eq_trail (hN : 2 < N k) (cover : Finset (Vertex k) → Prop)
    (tests : Finset (Vertex k) → Finset (Vertex k))
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (o : Oracle (Vertex k)) (n : ℕ)
    (hc : ∀ j < n, ¬cover (frontierTrail z w j).visited) :
    run (restorationCollect cover tests) (lazyTapes z w) o (n + 1) = frontierTrail z w n := by
  induction n with
  | zero => simp [run, step, restorationCollect, collectThenCheck, History.setups,
      History.halted, respond, frontierTrail, lazyTapes]
  | succ n ih =>
    have hi := ih (fun j hj => hc j (by omega))
    rw [run_succ, hi]
    simp [step, restorationCollect_update hN cover tests z w n (hc n (by omega)),
      respond, frontierTrail, lazyTapes, frontierTarget]

end RandomWalkSearch.Cycle
