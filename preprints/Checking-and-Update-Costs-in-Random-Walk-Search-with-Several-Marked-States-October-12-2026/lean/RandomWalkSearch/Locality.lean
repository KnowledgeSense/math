import RandomWalkSearch.Truncation
import Mathlib.Data.Finset.Image

/-! # Local-access legality and visited sets -/

namespace RandomWalkSearch

universe u
variable {X : Type u}

namespace Event

def newVertex : Event X → Option X
  | .setup x => some x
  | .update _ _ y => some y
  | _ => none

def checkedVertex : Event X → Option X
  | .check x _ => some x
  | _ => none

def outputVertex : Event X → Option X
  | .output x => x
  | _ => none

end Event

namespace History

variable [DecidableEq X]

def visited (h : History X) : Finset X := (h.filterMap Event.newVertex).toFinset
def checked (h : History X) : Finset X := (h.filterMap Event.checkedVertex).toFinset
def outputs (h : History X) : Finset X := (h.filterMap Event.outputVertex).toFinset

@[simp] theorem visited_nil : visited ([] : History X) = ∅ := rfl
@[simp] theorem checked_nil : checked ([] : History X) = ∅ := rfl
@[simp] theorem outputs_nil : outputs ([] : History X) = ∅ := rfl

@[simp] theorem visited_cons_setup (x : X) (h : History X) :
    visited (.setup x :: h) = insert x h.visited := by
  simp [visited, Event.newVertex]

@[simp] theorem visited_cons_update (i : ℕ) (x y : X) (h : History X) :
    visited (.update i x y :: h) = insert y h.visited := by
  simp [visited, Event.newVertex]

@[simp] theorem visited_cons_check (x : X) (a : Bool) (h : History X) :
    visited (.check x a :: h) = h.visited := by
  simp [visited, List.filterMap_cons, Event.newVertex]

@[simp] theorem visited_cons_output (x : Option X) (h : History X) :
    visited (.output x :: h) = h.visited := by
  simp [visited, List.filterMap_cons, Event.newVertex]

@[simp] theorem visited_cons_think (h : History X) :
    visited (.think :: h) = h.visited := by
  simp [visited, List.filterMap_cons, Event.newVertex]

@[simp] theorem checked_cons_check (x : X) (a : Bool) (h : History X) :
    checked (.check x a :: h) = insert x h.checked := by
  simp [checked, Event.checkedVertex]

/-- Only setups and updates create visited vertices. -/
theorem card_visited_le (h : History X) : h.visited.card ≤ h.setups + h.updates := by
  induction h with
  | nil => simp [setups, updates]
  | cons e h ih =>
    cases e <;>
      simp only [visited_cons_setup, visited_cons_update, visited_cons_check,
        visited_cons_output, visited_cons_think, setups, updates, List.countP_cons,
        Event.isSetup, Event.isUpdate, Bool.false_eq_true, ite_false, ite_true] at *
    all_goals first | exact ih | omega | exact (Finset.card_insert_le ..).trans (by omega)

theorem visited_mono {h h' : History X} (hs : h ⊆ h') : h.visited ⊆ h'.visited := by
  intro x hx
  simp only [visited, List.mem_toFinset, List.mem_filterMap] at hx ⊢
  obtain ⟨e, he, hx⟩ := hx
  exact ⟨e, hs he, hx⟩

end History

variable [DecidableEq X]

/-- A local operation may only update or check an already visited vertex.
Outputs remain unrestricted. -/
def Local (h : History X) : Action X → Prop
  | .update _ x => x ∈ h.visited
  | .check x => x ∈ h.visited
  | _ => True

/-- The setup limit is imposed before the next setup operation. -/
def SetupBound (b : ℕ) (h : History X) : Action X → Prop
  | .setup => h.setups < b
  | _ => True

/-- Pointwise admissibility on genuine executions, with arbitrary private seed
already fixed in the policy. Randomized admissibility quantifies over that seed. -/
def Restoration {A : Type*} (family : A → Oracle X) (b : ℕ)
    (p : Policy X) (r : Tapes X) : Prop :=
  ∀ a n, (run p r (family a) n).halted = false →
    Local (run p r (family a) n) (p (run p r (family a) n)) ∧
    SetupBound b (run p r (family a) n) (p (run p r (family a) n))

/-- A given completed run is local even when the answers are counterfactual. -/
theorem complete_local {A : Type*} (family : A → Oracle X) (b : ℕ)
    (p : Policy X) (r : Tapes X) (hp : Restoration family b p r)
    (q : Oracle X) (n : ℕ)
    (hn : (run (complete family p) r q n).halted = false) :
    Local (run (complete family p) r q n)
      (complete family p (run (complete family p) r q n)) := by
  exact complete_operation_safe family p r Local (fun _ => trivial)
    (fun a n hn => (hp a n hn).1) q n hn

theorem complete_setupBound {A : Type*} (family : A → Oracle X) (b : ℕ)
    (p : Policy X) (r : Tapes X) (hp : Restoration family b p r)
    (q : Oracle X) (n : ℕ)
    (hn : (run (complete family p) r q n).halted = false) :
    SetupBound b (run (complete family p) r q n)
      (complete family p (run (complete family p) r q n)) := by
  exact complete_operation_safe family p r (SetupBound b) (fun _ => trivial)
    (fun a n hn => (hp a n hn).2) q n hn

/-- Every checked vertex in a local execution was created by a setup or update. -/
theorem checked_subset_visited (p : Policy X) (r : Tapes X) (o : Oracle X)
    (hl : ∀ n, (run p r o n).halted = false →
      Local (run p r o n) (p (run p r o n))) (n : ℕ) :
    (run p r o n).checked ⊆ (run p r o n).visited := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [run_succ, step]
    split
    · exact ih
    · rename_i hn
      have hl' := hl n (Bool.eq_false_iff.mpr hn)
      cases ha : p (run p r o n) with
      | setup =>
        simpa [ha, respond, History.checked, List.filterMap_cons, Event.checkedVertex] using
          ih.trans (Finset.subset_insert (r.setup (run p r o n).setups) _)
      | update i x =>
        simpa [ha, respond, History.checked, List.filterMap_cons, Event.checkedVertex] using
          ih.trans (Finset.subset_insert
            (r.update i ((run p r o n).trajectoryUpdates i) x) _)
      | check x =>
        have hx : x ∈ (run p r o n).visited := by simpa [ha, Local] using hl'
        simpa only [ha, respond, History.checked_cons_check, History.visited_cons_check,
          Finset.insert_subset_iff] using And.intro hx ih
      | output x =>
        simpa [ha, respond, History.checked, List.filterMap_cons, Event.checkedVertex] using ih
      | think => simpa [ha, respond, History.checked, List.filterMap_cons, Event.checkedVertex] using ih

omit [DecidableEq X] in
theorem run_setup_le (b : ℕ) (p : Policy X) (r : Tapes X) (o : Oracle X)
    (hb : ∀ n, (run p r o n).halted = false →
      SetupBound b (run p r o n) (p (run p r o n))) (n : ℕ) :
    (run p r o n).setups ≤ b := by
  induction n with
  | zero => simp [History.setups]
  | succ n ih =>
    simp only [run_succ, step]
    split
    · exact ih
    · rename_i hn
      have hb' := hb n (Bool.eq_false_iff.mpr hn)
      cases ha : p (run p r o n) with
      | setup =>
        have hlt : (run p r o n).setups < b := by simpa [ha, SetupBound] using hb'
        simpa [respond, History.setups, List.countP_cons, Event.isSetup] using Nat.succ_le_of_lt hlt
      | update i x => simpa [respond, History.setups, List.countP_cons, Event.isSetup] using ih
      | check x => simpa [respond, History.setups, List.countP_cons, Event.isSetup] using ih
      | output x => simpa [respond, History.setups, List.countP_cons, Event.isSetup] using ih
      | think => simpa [respond, History.setups, List.countP_cons, Event.isSetup] using ih

namespace History

theorem checked_mono {h h' : History X} (hs : h ⊆ h') : h.checked ⊆ h'.checked := by
  intro x hx
  simp only [checked, List.mem_toFinset, List.mem_filterMap] at hx ⊢
  obtain ⟨e, he, hx⟩ := hx
  exact ⟨e, hs he, hx⟩

theorem outputs_mono {h h' : History X} (hs : h ⊆ h') : h.outputs ⊆ h'.outputs := by
  intro x hx
  simp only [outputs, List.mem_toFinset, List.mem_filterMap] at hx ⊢
  obtain ⟨e, he, hx⟩ := hx
  exact ⟨e, hs he, hx⟩

theorem card_checked_le (h : History X) : h.checked.card ≤ h.checks := by
  induction h with
  | nil => simp [checks]
  | cons e h ih =>
    cases e <;>
      simp [checked, checks, List.filterMap_cons, List.countP_cons, Event.checkedVertex,
        Event.isCheck] at ih ⊢
    all_goals first | exact ih | exact (Finset.card_insert_le ..).trans (by omega)

theorem outputs_empty_of_not_halted (h : History X) (hn : h.halted = false) :
    h.outputs = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  obtain ⟨e, he, hex⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hx)
  have hno : ¬ e.isOutput = true := List.any_eq_false.mp hn e he
  cases e <;> simp_all [Event.outputVertex, Event.isOutput]

end History

theorem run_outputs_card_le (p : Policy X) (r : Tapes X) (o : Oracle X) (n : ℕ) :
    (run p r o n).outputs.card ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [run_succ, step]
    split
    · exact ih
    · rename_i hn
      have hempty := History.outputs_empty_of_not_halted (run p r o n)
        (Bool.eq_false_iff.mpr hn)
      cases ha : p (run p r o n) with
      | setup => simpa [respond, History.outputs, List.filterMap_cons, Event.outputVertex] using ih
      | update i x => simpa [respond, History.outputs, List.filterMap_cons, Event.outputVertex] using ih
      | check x => simpa [respond, History.outputs, List.filterMap_cons, Event.outputVertex] using ih
      | think => simpa [respond, History.outputs, List.filterMap_cons, Event.outputVertex] using ih
      | output x =>
        cases x with
        | none => simpa [respond, History.outputs, List.filterMap_cons, Event.outputVertex] using ih
        | some x =>
          have h : History.outputs (.output (some x) :: run p r o n) = {x} := by
            simpa [History.outputs, Event.outputVertex] using
              congrArg (insert x) hempty
          simp only [respond, h, Finset.card_singleton, le_refl]

end RandomWalkSearch
