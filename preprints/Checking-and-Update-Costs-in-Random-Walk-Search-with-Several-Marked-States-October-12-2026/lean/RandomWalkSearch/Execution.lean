import Mathlib.Data.List.Count
import Mathlib.Data.Finset.Card
import Mathlib.Data.ENat.Lattice

/-!
# Oracle execution of arbitrary history-dependent local policies

A private random seed selects an arbitrary `Policy`. Random setup and update tapes
are supplied separately. Histories are finite at every finite execution time, but
execution time is unbounded. Output need not be visited. `think` permits a run
with no further oracle operations to diverge. There is no finite-policy bound.
-/

namespace RandomWalkSearch

universe u

inductive Action (X : Type u) where
  | setup
  | update (trajectory : ℕ) (source : X)
  | check (vertex : X)
  | output (vertex : Option X)
  | think
  deriving DecidableEq

inductive Event (X : Type u) where
  | setup (vertex : X)
  | update (trajectory : ℕ) (source target : X)
  | check (vertex : X) (answer : Bool)
  | output (vertex : Option X)
  | think
  deriving DecidableEq

abbrev History (X : Type u) := List (Event X)
abbrev Policy (X : Type u) := History X → Action X
abbrev Oracle (X : Type u) := X → Bool

namespace Event

variable {X : Type u}

def isSetup : Event X → Bool
  | .setup _ => true
  | _ => false

def isUpdate : Event X → Bool
  | .update .. => true
  | _ => false

def isCheck : Event X → Bool
  | .check .. => true
  | _ => false

def isOutput : Event X → Bool
  | .output _ => true
  | _ => false

def isPositive : Event X → Bool
  | .check _ answer => answer
  | _ => false

def isTrajectoryUpdate (i : ℕ) : Event X → Bool
  | .update j _ _ => decide (i = j)
  | _ => false

def Agrees (o : Oracle X) : Event X → Prop
  | .check x a => a = o x
  | _ => True

end Event

namespace History

variable {X : Type u}

def setups (h : History X) : ℕ := h.countP Event.isSetup
def updates (h : History X) : ℕ := h.countP Event.isUpdate
def checks (h : History X) : ℕ := h.countP Event.isCheck
def trajectoryUpdates (h : History X) (i : ℕ) : ℕ :=
  h.countP (Event.isTrajectoryUpdate i)
def halted (h : History X) : Bool := h.any Event.isOutput
def positive (h : History X) : Bool := h.any Event.isPositive

def Agrees (h : History X) (o : Oracle X) : Prop :=
  ∀ e ∈ h, e.Agrees o

@[simp] theorem agrees_nil (o : Oracle X) : Agrees [] o := by
  simp [Agrees]

@[simp] theorem agrees_cons (e : Event X) (h : History X) (o : Oracle X) :
    Agrees (e :: h) o ↔ e.Agrees o ∧ h.Agrees o := by
  simp [Agrees]

end History

/-- For a consecutive policy, stream `i` belongs to trajectory `i`.
For a restoration policy one can use stream zero for every update. -/
structure Tapes (X : Type u) where
  setup : ℕ → X
  update : ℕ → ℕ → X → X

variable {X : Type u}

/-- Evaluation of one chosen operation. Only the check clause uses the oracle. -/
def respond (r : Tapes X) (o : Oracle X) (h : History X) : Action X → Event X
  | .setup => .setup (r.setup h.setups)
  | .update i x => .update i x (r.update i (h.trajectoryUpdates i) x)
  | .check x => .check x (o x)
  | .output x => .output x
  | .think => .think

/-- Histories are stored in reverse chronological order. Halting is absorbing. -/
def step (p : Policy X) (r : Tapes X) (o : Oracle X) (h : History X) : History X :=
  if h.halted then h else respond r o h (p h) :: h

def run (p : Policy X) (r : Tapes X) (o : Oracle X) : ℕ → History X
  | 0 => []
  | n + 1 => step p r o (run p r o n)

@[simp] theorem run_zero (p : Policy X) (r : Tapes X) (o : Oracle X) :
    run p r o 0 = [] := rfl

@[simp] theorem run_succ (p : Policy X) (r : Tapes X) (o : Oracle X) (n : ℕ) :
    run p r o (n + 1) = step p r o (run p r o n) := rfl

@[simp] theorem respond_agrees (r : Tapes X) (o : Oracle X)
    (h : History X) (a : Action X) : (respond r o h a).Agrees o := by
  cases a <;> simp [respond, Event.Agrees]

theorem step_agrees (p : Policy X) (r : Tapes X) (o : Oracle X)
    (h : History X) (hh : h.Agrees o) : (step p r o h).Agrees o := by
  simp only [step]
  split
  · exact hh
  · exact History.agrees_cons _ _ _ |>.mpr ⟨respond_agrees .., hh⟩

/-- Every genuine finite transcript is consistent with its own oracle. -/
theorem run_agrees (p : Policy X) (r : Tapes X) (o : Oracle X) (n : ℕ) :
    (run p r o n).Agrees o := by
  induction n with
  | zero => simp
  | succ n ih => exact step_agrees p r o _ ih

/-- The family of genuine oracles. No injectivity of the indexing is required. -/
def Consistent {A : Type*} (family : A → Oracle X) (h : History X) : Prop :=
  ∃ a, h.Agrees (family a)

/-- Stop at an impossible transcript. This is not a legality hypothesis. -/
noncomputable def complete {A : Type*} (family : A → Oracle X) (p : Policy X) : Policy X :=
  by
    classical
    exact fun h => if Consistent family h then p h else .output none

/-- Completion preserves every operation of every genuine run, for all tapes. -/
theorem run_complete {A : Type*} (family : A → Oracle X) (p : Policy X)
    (r : Tapes X) (a : A) (n : ℕ) :
    run (complete family p) r (family a) n = run p r (family a) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run_succ, ih, step]
    have hc : Consistent family (run p r (family a) n) :=
      ⟨a, run_agrees p r (family a) n⟩
    simp [complete, hc]

/-- Success is a finite output event; divergent executions fail. -/
def Succeeds (p : Policy X) (r : Tapes X) (o : Oracle X) : Prop :=
  ∃ n x, Event.output (some x) ∈ run p r o n ∧ o x = true

/-- Infinite operation counts are suprema of genuine finite-prefix counts. -/
noncomputable def updateCost (p : Policy X) (r : Tapes X) (o : Oracle X) : ℕ∞ :=
  ⨆ n, (run p r o n).updates

noncomputable def checkCost (p : Policy X) (r : Tapes X) (o : Oracle X) : ℕ∞ :=
  ⨆ n, (run p r o n).checks

theorem complete_succeeds_iff {A : Type*} (family : A → Oracle X) (p : Policy X)
    (r : Tapes X) (a : A) :
    Succeeds (complete family p) r (family a) ↔ Succeeds p r (family a) := by
  simp only [Succeeds, run_complete]

theorem complete_updateCost {A : Type*} (family : A → Oracle X) (p : Policy X)
    (r : Tapes X) (a : A) :
    updateCost (complete family p) r (family a) = updateCost p r (family a) := by
  simp only [updateCost, run_complete]

theorem complete_checkCost {A : Type*} (family : A → Oracle X) (p : Policy X)
    (r : Tapes X) (a : A) :
    checkCost (complete family p) r (family a) = checkCost p r (family a) := by
  simp only [checkCost, run_complete]

/-! ## Prefix replay and completion on counterfactual transcripts -/

theorem history_sublist_step (p : Policy X) (r : Tapes X) (o : Oracle X)
    (h : History X) : h.Sublist (step p r o h) := by
  simp only [step]
  split
  · exact List.Sublist.refl _
  · exact List.Sublist.cons _ (List.Sublist.refl _)

theorem run_sublist_succ (p : Policy X) (r : Tapes X) (o : Oracle X) (n : ℕ) :
    (run p r o n).Sublist (run p r o (n + 1)) :=
  history_sublist_step p r o _

theorem run_mono (p : Policy X) (r : Tapes X) (o : Oracle X)
    {m n : ℕ} (hmn : m ≤ n) : (run p r o m).Sublist (run p r o n) := by
  induction n, hmn using Nat.le_induction with
  | base => exact List.Sublist.refl _
  | succ n _ ih => exact ih.trans (run_sublist_succ p r o n)

theorem History.Agrees.of_subset {h h' : History X} {o : Oracle X}
    (hh : h'.Agrees o) (hsub : h ⊆ h') : h.Agrees o := by
  intro e he
  exact hh e (hsub he)

theorem respond_eq_of_agrees (r : Tapes X) (o q : Oracle X)
    (h : History X) (a : Action X) (ha : (respond r q h a).Agrees o) :
    respond r q h a = respond r o h a := by
  cases a <;> simp_all [respond, Event.Agrees]

/-- Any execution prefix whose answers fit another oracle can be replayed there. -/
theorem run_replay (p : Policy X) (r : Tapes X) (o q : Oracle X)
    (n : ℕ) (hfit : (run p r q n).Agrees o) :
    run p r q n = run p r o n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp : (run p r q n).Agrees o :=
      hfit.of_subset (run_sublist_succ p r q n).subset
    have heq := ih hp
    simp only [run_succ, step] at hfit ⊢
    rw [← heq]
    by_cases hh : (run p r q n).halted = true
    · simp only [hh, ite_true]
    · simp only [hh] at hfit ⊢
      have ha := (History.agrees_cons _ _ _).mp hfit
      rw [respond_eq_of_agrees r o q _ _ ha.1]

/-- A consistent prefix of a completed counterfactual run is an actual prefix
of the original policy on one of the genuine instances. -/
theorem complete_prefix_realizable {A : Type*} (family : A → Oracle X)
    (p : Policy X) (r : Tapes X) (q : Oracle X) (n : ℕ)
    (hc : Consistent family (run (complete family p) r q n)) :
    ∃ a, run (complete family p) r q n = run p r (family a) n := by
  obtain ⟨a, ha⟩ := hc
  exact ⟨a, (run_replay _ r (family a) q n ha).trans (run_complete family p r a n)⟩

/-- Any restriction on the next operation that permits halting transfers from
all genuine runs to every run of the completed policy. This includes locality,
setup/update/check hard budgets, and consecutive-trajectory restrictions. -/
theorem complete_operation_safe {A : Type*} (family : A → Oracle X)
    (p : Policy X) (r : Tapes X) (Safe : History X → Action X → Prop)
    (hhalt : ∀ h, Safe h (.output none))
    (hsafe : ∀ a n, (run p r (family a) n).halted = false →
      Safe (run p r (family a) n) (p (run p r (family a) n)))
    (q : Oracle X) (n : ℕ)
    (hactive : (run (complete family p) r q n).halted = false) :
    Safe (run (complete family p) r q n)
      (complete family p (run (complete family p) r q n)) := by
  classical
  by_cases hc : Consistent family (run (complete family p) r q n)
  · obtain ⟨a, ha⟩ := complete_prefix_realizable family p r q n hc
    simp only [complete, hc, ite_true]
    rw [ha]
    exact hsafe a n (ha ▸ hactive)
  · simp only [complete, hc, ite_false]
    exact hhalt _

/-! ## Coupling to the all-negative oracle -/

def negativeOracle : Oracle X := fun _ => false

/-- No positive answer in a genuine prefix implies exact all-negative replay. -/
theorem run_eq_negative_of_no_positive (p : Policy X) (r : Tapes X)
    (o : Oracle X) (n : ℕ) (hn : (run p r o n).positive = false) :
    run p r o n = run p r negativeOracle n := by
  apply run_replay
  intro e he
  have he' : e.isPositive = false := by
    have := List.any_eq_false.mp hn e he
    exact Bool.eq_false_iff.mpr this
  cases e <;> simp_all [Event.Agrees, Event.isPositive, negativeOracle]

/-- A first positive answer is a check made by the all-negative run too.
The all-negative transcript records the same vertex with the negative answer. -/
theorem first_positive_coupling (p : Policy X) (r : Tapes X) (o : Oracle X)
    (n : ℕ) (hn : (run p r o n).positive = false)
    (hn' : (run p r o (n + 1)).positive = true) :
    ∃ x, o x = true ∧ Event.check x false ∈ run p r negativeOracle (n + 1) := by
  have heq := run_eq_negative_of_no_positive p r o n hn
  have hnany : (run p r o n).any Event.isPositive = false := hn
  simp only [run_succ, step] at hn'
  split at hn'
  · simp_all
  · rename_i hactive
    cases hp : p (run p r o n) with
    | setup => simp only [hp, respond, History.positive, List.any_cons, Event.isPositive,
        Bool.false_or, hnany, Bool.false_eq_true] at hn'
    | update i x => simp only [hp, respond, History.positive, List.any_cons, Event.isPositive,
        Bool.false_or, hnany, Bool.false_eq_true] at hn'
    | output x => simp only [hp, respond, History.positive, List.any_cons, Event.isPositive,
        Bool.false_or, hnany, Bool.false_eq_true] at hn'
    | think => simp only [hp, respond, History.positive, List.any_cons, Event.isPositive,
        Bool.false_or, hnany, Bool.false_eq_true] at hn'
    | check x =>
      have hx : o x = true := by
        simpa [hp, respond, History.positive, Event.isPositive,
          show (run p r o n).any Event.isPositive = false from hn] using hn'
      refine ⟨x, hx, ?_⟩
      simp only [run_succ, step, ← heq, hactive, hp, respond, negativeOracle]
      exact List.mem_cons_self

/-- A positive answer at some time has a least positive time, and hence a
corresponding checked vertex in the all-negative execution. -/
theorem positive_coupling (p : Policy X) (r : Tapes X) (o : Oracle X)
    (hpos : ∃ n, (run p r o n).positive = true) :
    ∃ n x, o x = true ∧ Event.check x false ∈ run p r negativeOracle n := by
  classical
  let n := Nat.find hpos
  have hn : (run p r o n).positive = true := Nat.find_spec hpos
  have hn0 : n ≠ 0 := by
    intro hzero
    simp [hzero, History.positive] at hn
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hmneg : (run p r o m).positive = false := by
    have hnot : ¬(run p r o m).positive = true :=
      Nat.find_min hpos (by omega)
    exact Bool.eq_false_iff.mpr hnot
  obtain ⟨x, hx, hmem⟩ := first_positive_coupling p r o m hmneg (by simpa only [hm] using hn)
  exact ⟨m + 1, x, hx, hmem⟩

/-- Success requires an all-negative checked vertex or its eventual output to
be marked. This statement allows unvisited, unchecked output and divergence. -/
theorem success_coupling (p : Policy X) (r : Tapes X) (o : Oracle X)
    (hs : Succeeds p r o) :
    (∃ n x, o x = true ∧ Event.check x false ∈ run p r negativeOracle n) ∨
    (∃ n x, o x = true ∧ Event.output (some x) ∈ run p r negativeOracle n) := by
  classical
  by_cases hp : ∃ n, (run p r o n).positive = true
  · exact Or.inl (positive_coupling p r o hp)
  · obtain ⟨n, x, hx, hmark⟩ := hs
    have hn : (run p r o n).positive = false :=
      Bool.eq_false_iff.mpr (fun hn => hp ⟨n, hn⟩)
    exact Or.inr ⟨n, x, hmark, run_eq_negative_of_no_positive p r o n hn ▸ hx⟩

end RandomWalkSearch
