import RandomWalkSearch.Infinite
import Mathlib.Data.Finset.SDiff

/-! # Actual collect-then-check endpoint policies

These are history-dependent policies in the same local oracle execution model
as the lower bounds. Collection uses one current trajectory. Once a finite
coverage certificate holds, the policy checks stored representatives and outputs
only a positively checked vertex.
-/

noncomputable section
namespace RandomWalkSearch.EndpointPolicy

universe u
variable {X : Type u} [DecidableEq X]

/-- Latest endpoint in the reverse-chronological transcript. -/
def current : History X → Option X
  | [] => none
  | e :: h => e.newVertex.or (current h)

def positiveVertex : Event X → Option X
  | .check x true => some x
  | _ => none

def positives (h : History X) : Finset X := (h.filterMap positiveVertex).toFinset

def pick (s : Finset X) : Option X :=
  if h : s.Nonempty then some h.choose else none

omit [DecidableEq X] in
theorem pick_some_mem {s : Finset X} {x : X} (h : pick s = some x) : x ∈ s := by
  unfold pick at h
  split at h
  · rename_i hs
    have he : hs.choose = x := Option.some.inj h
    exact he ▸ hs.choose_spec
  · cases h

omit [DecidableEq X] in
theorem pick_eq_none_iff (s : Finset X) : pick s = none ↔ s = ∅ := by
  unfold pick
  split
  · rename_i hs
    simp [hs.ne_empty]
  · rename_i hs
    have he := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]

theorem current_mem_visited {h : History X} {x : X} (hx : current h = some x) :
    x ∈ h.visited := by
  induction h with
  | nil => cases hx
  | cons e h ih =>
    cases e <;> simp only [current, Event.newVertex, Option.or] at hx
    · simp only [Option.some.injEq] at hx
      subst x
      simp
    · simp only [Option.some.injEq] at hx
      subst x
      simp
    · exact ih hx
    · exact ih hx
    · exact ih hx

theorem mem_positives {h : History X} {x : X} :
    x ∈ positives h ↔ Event.check x true ∈ h := by
  simp only [positives, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hx⟩
    cases e with
    | setup y => cases hx
    | update i y z => cases hx
    | check y a =>
      cases a with
      | false => cases hx
      | true =>
        simp only [positiveVertex, Option.some.injEq] at hx
        subst y
        exact he
    | output y => cases hx
    | think => cases hx
  · intro hx
    exact ⟨.check x true, hx, rfl⟩

theorem positive_true {h : History X} {o : Oracle X} (ha : h.Agrees o)
    {x : X} (hx : x ∈ positives h) : o x = true :=
  (ha (.check x true) (mem_positives.mp hx)).symm

/-- A coverage predicate and a finite stored test set determine the policy. -/
def collectThenCheck (cover : Finset X → Prop) (tests : Finset X → Finset X) : Policy X := by
  classical
  exact fun h =>
    if h.setups = 0 then .setup
    else match pick (positives h) with
    | some x => .output (some x)
    | none =>
      if cover h.visited then
        match pick (tests h.visited \ h.checked) with
        | some x => .check x
        | none => .output none
      else match current h with
        | some x => .update 0 x
        | none => .output none

theorem collectThenCheck_local (cover : Finset X → Prop) (tests : Finset X → Finset X)
    (ht : ∀ v, tests v ⊆ v) (h : History X) : Local h (collectThenCheck cover tests h) := by
  unfold collectThenCheck
  split
  · trivial
  · split
    · trivial
    · split
      · split
        · rename_i x hx
          exact ht _ (Finset.mem_sdiff.mp (pick_some_mem hx)).1
        · trivial
      · split
        · rename_i x hx
          exact current_mem_visited hx
        · trivial

theorem collectThenCheck_setupBound (cover : Finset X → Prop) (tests : Finset X → Finset X)
    (h : History X) : SetupBound 1 h (collectThenCheck cover tests h) := by
  unfold collectThenCheck
  split
  · rename_i hh
    simp [SetupBound, hh]
  · split
    · trivial
    · split
      · split <;> trivial
      · split <;> trivial

theorem collectThenCheck_restoration {A : Type*} (family : A → Oracle X)
    (cover : Finset X → Prop) (tests : Finset X → Finset X)
    (ht : ∀ v, tests v ⊆ v) (r : Tapes X) :
    Restoration family 1 (collectThenCheck cover tests) r := by
  intro a n _
  exact ⟨collectThenCheck_local cover tests ht _, collectThenCheck_setupBound cover tests _⟩

/-- The actual trajectory determined by setup zero and update stream zero. -/
def trajectory (r : Tapes X) : ℕ → X
  | 0 => r.setup 0
  | n + 1 => r.update 0 n (trajectory r n)

/-- Complete collection transcript after `n` updates and the one setup. -/
def trail (r : Tapes X) : ℕ → History X
  | 0 => [.setup (r.setup 0)]
  | n + 1 => .update 0 (trajectory r n) (trajectory r (n + 1)) :: trail r n

omit [DecidableEq X] in
@[simp] theorem trail_setups (r : Tapes X) (n : ℕ) : (trail r n).setups = 1 := by
  induction n with
  | zero => simp [trail, History.setups, Event.isSetup]
  | succ n ih => simp [trail, History.setups, Event.isSetup, History.setups] at ih ⊢; exact ih

omit [DecidableEq X] in
@[simp] theorem trail_updates (r : Tapes X) (n : ℕ) : (trail r n).updates = n := by
  induction n with
  | zero => simp [trail, History.updates, Event.isUpdate]
  | succ n ih =>
    simp only [trail, History.updates, List.countP_cons, Event.isUpdate, ite_true]
    exact congrArg (· + 1) ih

omit [DecidableEq X] in
@[simp] theorem trail_trajectoryUpdates (r : Tapes X) (n : ℕ) :
    (trail r n).trajectoryUpdates 0 = n := by
  induction n with
  | zero => simp [trail, History.trajectoryUpdates, Event.isTrajectoryUpdate]
  | succ n ih =>
    simpa [trail, History.trajectoryUpdates, Event.isTrajectoryUpdate] using ih

omit [DecidableEq X] in
@[simp] theorem trail_checks (r : Tapes X) (n : ℕ) : (trail r n).checks = 0 := by
  induction n with
  | zero => simp [trail, History.checks, Event.isCheck]
  | succ n ih => simpa [trail, History.checks, Event.isCheck] using ih

@[simp] theorem trail_checked (r : Tapes X) (n : ℕ) : (trail r n).checked = ∅ := by
  induction n with
  | zero => simp [trail, History.checked, Event.checkedVertex]
  | succ n ih => simpa [trail, History.checked, Event.checkedVertex] using ih

@[simp] theorem trail_positives (r : Tapes X) (n : ℕ) : positives (trail r n) = ∅ := by
  induction n with
  | zero => simp [trail, positives, positiveVertex]
  | succ n ih => simpa [trail, positives, positiveVertex] using ih

omit [DecidableEq X] in
@[simp] theorem trail_halted (r : Tapes X) (n : ℕ) : (trail r n).halted = false := by
  induction n with
  | zero => simp [trail, History.halted, Event.isOutput]
  | succ n ih => simpa [trail, History.halted, Event.isOutput] using ih

omit [DecidableEq X] in
@[simp] theorem trail_current (r : Tapes X) (n : ℕ) :
    current (trail r n) = some (trajectory r n) := by
  cases n <;> simp [trail, current, Event.newVertex, trajectory]

omit [DecidableEq X] in
@[simp] theorem trail_agrees (r : Tapes X) (o : Oracle X) (n : ℕ) : (trail r n).Agrees o := by
  induction n with
  | zero => simp [trail, Event.Agrees]
  | succ n ih => simpa [trail, Event.Agrees] using ih

theorem trail_policy_update (cover : Finset X → Prop) (tests : Finset X → Finset X)
    (r : Tapes X) (n : ℕ) (hc : ¬cover (trail r n).visited) :
    collectThenCheck cover tests (trail r n) = .update 0 (trajectory r n) := by
  simp [collectThenCheck, pick, hc]

/-- Exact simulation of the collection phase, for every tape and oracle. -/
theorem run_eq_trail (cover : Finset X → Prop) (tests : Finset X → Finset X)
    (r : Tapes X) (o : Oracle X) (n : ℕ)
    (hc : ∀ j < n, ¬cover (trail r j).visited) :
    RandomWalkSearch.run (collectThenCheck cover tests) r o (n + 1) = trail r n := by
  induction n with
  | zero => simp [RandomWalkSearch.run, step, collectThenCheck, History.setups,
      History.halted, respond, trail]
  | succ n ih =>
    have hi := ih (fun j hj => hc j (by omega))
    rw [RandomWalkSearch.run_succ, hi]
    simp [step, trail_policy_update cover tests r n (hc n (by omega)), respond, trail, trajectory]

/-- Reachability in the actual oracle execution, with no surrogate run. -/
def Reachable (p : Policy X) (r : Tapes X) (o : Oracle X) (h : History X) : Prop :=
  ∃ n, RandomWalkSearch.run p r o n = h

omit [DecidableEq X] in
theorem reachable_step {p : Policy X} {r : Tapes X} {o : Oracle X} {h : History X}
    (hr : Reachable p r o h) : Reachable p r o (step p r o h) := by
  obtain ⟨n, rfl⟩ := hr
  exact ⟨n + 1, rfl⟩

theorem checked_mark_positive {h : History X} {o : Oracle X} (ha : h.Agrees o)
    {x : X} (hx : x ∈ h.checked) (ho : o x = true) : x ∈ positives h := by
  apply mem_positives.mpr
  simp only [History.checked, List.mem_toFinset, List.mem_filterMap] at hx
  obtain ⟨e, he, hx⟩ := hx
  cases e with
  | setup y => cases hx
  | update i y z => cases hx
  | check y a =>
    simp only [Event.checkedVertex, Option.some.injEq] at hx
    subst y
    have heq : a = true := (ha (.check x a) he).trans ho
    subst a
    exact he
  | output y => cases hx
  | think => cases hx

/-- Once coverage holds, the real policy finishes successfully after at most
one check per remaining stored test vertex. -/
theorem finish_of_cover_with_policy (cover : Finset X → Prop) (tests : Finset X → Finset X)
    (p : Policy X) (hp : ∀ h, cover h.visited → p h = collectThenCheck cover tests h)
    (r : Tapes X) (o : Oracle X) (h : History X)
    (hr : Reachable p r o h)
    (hs : h.setups ≠ 0) (hh : h.halted = false) (hc : cover h.visited)
    (hm : ∃ x ∈ tests h.visited, o x = true) :
    ∃ h', Reachable p r o h' ∧ h'.halted = true ∧
      (∃ x, Event.output (some x) ∈ h' ∧ o x = true) ∧
      h'.setups = h.setups ∧ h'.updates = h.updates ∧
      h'.checks ≤ h.checks + (tests h.visited \ h.checked).card := by
  generalize hn : (tests h.visited \ h.checked).card = n
  induction n using Nat.strong_induction_on generalizing h with
  | h n ih =>
    have hag : h.Agrees o := by
      obtain ⟨j, rfl⟩ := hr
      exact RandomWalkSearch.run_agrees p r o j
    cases hpos : pick (positives h) with
    | some x =>
      have hx := pick_some_mem hpos
      have ho := positive_true hag hx
      have hpol : p h = .output (some x) := by
        rw [hp h hc]
        simp [collectThenCheck, hs, hpos]
      have hstep : step p r o h = .output (some x) :: h := by
        simp [step, hh, hpol, respond]
      refine ⟨.output (some x) :: h, hstep ▸ reachable_step hr, ?_, ?_, ?_, ?_, ?_⟩
      · simp [History.halted, Event.isOutput]
      · exact ⟨x, by simp, ho⟩
      · simp [History.setups, Event.isSetup]
      · simp [History.updates, Event.isUpdate]
      · simp only [History.checks, List.countP_cons, Event.isCheck, Bool.false_eq_true, ite_false]
        omega
    | none =>
      have hpempty := (pick_eq_none_iff _).mp hpos
      have hne : (tests h.visited \ h.checked).Nonempty := by
        obtain ⟨x, hx, ho⟩ := hm
        refine ⟨x, Finset.mem_sdiff.mpr ⟨hx, ?_⟩⟩
        intro hx'
        have := checked_mark_positive hag hx' ho
        rw [hpempty] at this
        exact Finset.notMem_empty _ this
      cases ht : pick (tests h.visited \ h.checked) with
      | none => exact False.elim (hne.ne_empty ((pick_eq_none_iff _).mp ht))
      | some x =>
        have hx := pick_some_mem ht
        let h₁ : History X := .check x (o x) :: h
        have hpol : p h = .check x := by
          rw [hp h hc]
          simp [collectThenCheck, hs, hpos, hc, ht]
        have hstep : step p r o h = h₁ := by
          simp [step, hh, hpol, respond, h₁]
        have hreach : Reachable p r o h₁ := hstep ▸ reachable_step hr
        have hvisited : h₁.visited = h.visited := by simp [h₁]
        have hsetups : h₁.setups = h.setups := by simp [h₁, History.setups, Event.isSetup]
        have hupdates : h₁.updates = h.updates := by simp [h₁, History.updates, Event.isUpdate]
        have hchecks : h₁.checks = h.checks + 1 := by
          simp only [h₁, History.checks, List.countP_cons, Event.isCheck, ite_true]
        have hhalted : h₁.halted = false := by
          simpa [h₁, History.halted, Event.isOutput] using hh
        have hremaining : tests h₁.visited \ h₁.checked = (tests h.visited \ h.checked).erase x := by
          rw [hvisited]
          simp only [h₁, History.checked_cons_check]
          ext y
          simp only [Finset.mem_sdiff, Finset.mem_insert, not_or, Finset.mem_erase]
          tauto
        have hcard : (tests h₁.visited \ h₁.checked).card + 1 = n := by
          rw [hremaining, Finset.card_erase_add_one hx, hn]
        obtain ⟨h', hre, hha, hout, hsu, hup, hch⟩ := ih
          (tests h₁.visited \ h₁.checked).card (by omega) h₁ hreach
          (hsetups ▸ hs) hhalted (hvisited ▸ hc) (hvisited ▸ hm) rfl
        refine ⟨h', hre, hha, hout, hsu.trans hsetups, hup.trans hupdates, ?_⟩
        rw [hchecks] at hch
        omega

theorem finish_of_cover (cover : Finset X → Prop) (tests : Finset X → Finset X)
    (r : Tapes X) (o : Oracle X) (h : History X)
    (hr : Reachable (collectThenCheck cover tests) r o h)
    (hs : h.setups ≠ 0) (hh : h.halted = false) (hc : cover h.visited)
    (hm : ∃ x ∈ tests h.visited, o x = true) :
    ∃ h', Reachable (collectThenCheck cover tests) r o h' ∧ h'.halted = true ∧
      (∃ x, Event.output (some x) ∈ h' ∧ o x = true) ∧
      h'.setups = h.setups ∧ h'.updates = h.updates ∧
      h'.checks ≤ h.checks + (tests h.visited \ h.checked).card :=
  finish_of_cover_with_policy cover tests (collectThenCheck cover tests) (fun _ _ => rfl)
    r o h hr hs hh hc hm

/-- A finite coverage time gives a real successful endpoint execution with
exactly the collection updates and no more than the selected test-set size. -/
theorem collectThenCheck_finishes (cover : Finset X → Prop) (tests : Finset X → Finset X)
    (r : Tapes X) (o : Oracle X) (t Q : ℕ)
    (hc : cover (trail r t).visited)
    (hmark : ∀ v, cover v → ∃ x ∈ tests v, o x = true)
    (hbound : ∀ v, cover v → (tests v).card ≤ Q) :
    ∃ h, Reachable (collectThenCheck cover tests) r o h ∧ h.halted = true ∧
      (∃ x, Event.output (some x) ∈ h ∧ o x = true) ∧
      h.setups = 1 ∧ h.updates ≤ t ∧ h.checks ≤ Q := by
  classical
  have he : ∃ j, cover (trail r j).visited := ⟨t, hc⟩
  let j := Nat.find he
  have hj : j ≤ t := Nat.find_min' he hc
  have hcj : cover (trail r j).visited := Nat.find_spec he
  have hr : Reachable (collectThenCheck cover tests) r o (trail r j) :=
    ⟨j + 1, run_eq_trail cover tests r o j (fun m hm => Nat.find_min he hm)⟩
  obtain ⟨h, hr, hh, ho, hs, hu, hq⟩ := finish_of_cover cover tests r o (trail r j)
    hr (by simp) (by simp) hcj (hmark _ hcj)
  refine ⟨h, hr, hh, ho, by simpa using hs, ?_, ?_⟩
  · simp only [trail_updates] at hu
    exact hu.le.trans hj
  · have hb := hbound _ hcj
    simp only [trail_checks, trail_checked, Finset.sdiff_empty, zero_add] at hq
    exact hq.trans hb

end RandomWalkSearch.EndpointPolicy
