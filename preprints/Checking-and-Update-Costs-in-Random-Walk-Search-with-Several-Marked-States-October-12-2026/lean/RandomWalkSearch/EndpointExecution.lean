import RandomWalkSearch.EndpointPolicy
import RandomWalkSearch.Consecutive

noncomputable section
namespace RandomWalkSearch.EndpointPolicy

variable {X : Type*} [DecidableEq X]

theorem policy_setup_zero (cover : Finset X → Prop) (tests : Finset X → Finset X)
    (h : History X) (ha : collectThenCheck cover tests h = .setup) : h.setups = 0 := by
  unfold collectThenCheck at ha
  split at ha
  · assumption
  · split at ha
    · cases ha
    · split at ha
      · split at ha <;> cases ha
      · split at ha <;> cases ha

theorem policy_update_zero (cover : Finset X → Prop) (tests : Finset X → Finset X)
    (h : History X) (i : ℕ) (x : X) (ha : collectThenCheck cover tests h = .update i x) : i = 0 := by
  unfold collectThenCheck at ha
  split at ha
  · cases ha
  · split at ha
    · cases ha
    · split at ha
      · split at ha <;> cases ha
      · split at ha
        · cases ha; rfl
        · cases ha

theorem run_current_endpoint_zero (cover : Finset X → Prop) (tests : Finset X → Finset X)
    (r : Tapes X) (o : Oracle X) (n : ℕ) :
    current (run (collectThenCheck cover tests) r o n) =
      (run (collectThenCheck cover tests) r o n).endpoint 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_succ]
    unfold step
    split
    · exact ih
    · cases ha : collectThenCheck cover tests (run (collectThenCheck cover tests) r o n) with
      | setup =>
        have hs := policy_setup_zero cover tests _ ha
        simp [respond, current, Event.newVertex, History.endpoint, hs]
      | update i x =>
        have hi := policy_update_zero cover tests _ i x ha
        subst i
        simp [respond, current, Event.newVertex, History.endpoint]
      | check x => simpa [respond, current, Event.newVertex, History.endpoint] using ih
      | output x => simpa [respond, current, Event.newVertex, History.endpoint] using ih
      | think => simpa [respond, current, Event.newVertex, History.endpoint] using ih

theorem collectThenCheck_extends (cover : Finset X → Prop) (tests : Finset X → Finset X)
    (h : History X) (he : current h = h.endpoint 0) : Extends h (collectThenCheck cover tests h) := by
  unfold collectThenCheck
  split
  · trivial
  · rename_i hs
    split
    · trivial
    · split
      · split <;> trivial
      · split
        · rename_i x hx
          exact ⟨Nat.pos_of_ne_zero hs, he ▸ hx⟩
        · trivial

theorem collectThenCheck_consecutive {A : Type*} (family : A → Oracle X)
    (cover : Finset X → Prop) (tests : Finset X → Finset X)
    (ht : ∀ v, tests v ⊆ v) (r : Tapes X) :
    Consecutive family 1 (collectThenCheck cover tests) r := by
  refine ⟨collectThenCheck_restoration family cover tests ht r, ?_⟩
  intro a n _
  exact collectThenCheck_extends cover tests _ (run_current_endpoint_zero cover tests r (family a) n)

omit [DecidableEq X] in
theorem run_stable_of_halted (p : Policy X) (r : Tapes X) (o : Oracle X)
    {m : ℕ} (hh : (run p r o m).halted = true) (n : ℕ) (hn : m ≤ n) :
    run p r o n = run p r o m := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n _ ih => simp [run_succ, ih, step, hh]

omit [DecidableEq X] in
theorem costs_le_of_halted (p : Policy X) (r : Tapes X) (o : Oracle X)
    (m U Q : ℕ) (hh : (run p r o m).halted = true)
    (hu : (run p r o m).updates ≤ U) (hq : (run p r o m).checks ≤ Q) :
    updateCost p r o ≤ U ∧ checkCost p r o ≤ Q := by
  constructor
  · apply iSup_le
    intro n
    apply ENat.natCast_le_natCast.mpr
    rcases le_total n m with hn | hn
    · exact ((run_mono p r o hn).countP_le (p := Event.isUpdate)).trans hu
    · rw [run_stable_of_halted p r o hh n hn]
      exact hu
  · apply iSup_le
    intro n
    apply ENat.natCast_le_natCast.mpr
    rcases le_total n m with hn | hn
    · exact ((run_mono p r o hn).countP_le (p := Event.isCheck)).trans hq
    · rw [run_stable_of_halted p r o hh n hn]
      exact hq

theorem collectThenCheck_costs (cover : Finset X → Prop) (tests : Finset X → Finset X)
    (r : Tapes X) (o : Oracle X) (t Q : ℕ)
    (hc : cover (trail r t).visited)
    (hmark : ∀ v, cover v → ∃ x ∈ tests v, o x = true)
    (hbound : ∀ v, cover v → (tests v).card ≤ Q) :
    Succeeds (collectThenCheck cover tests) r o ∧
      updateCost (collectThenCheck cover tests) r o ≤ t ∧
      checkCost (collectThenCheck cover tests) r o ≤ Q := by
  obtain ⟨h, ⟨m, hm⟩, hh, ⟨x, hx, ho⟩, _, hu, hq⟩ :=
    collectThenCheck_finishes cover tests r o t Q hc hmark hbound
  subst h
  exact ⟨⟨m, x, hx, ho⟩, costs_le_of_halted _ _ _ m t Q hh hu hq⟩

end RandomWalkSearch.EndpointPolicy
