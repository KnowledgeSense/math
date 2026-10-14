import RandomWalkSearch.Cycle
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-! # Full infinite transcripts on a finite state space

No bound on the running time is imposed. Monotonicity and finiteness of the
vertex space make the union of all observed vertices equal to a finite prefix.
This also covers divergent runs with infinitely many checks or computation steps.
-/

namespace RandomWalkSearch

universe u
variable {X : Type u} [DecidableEq X] [Fintype X]

noncomputable def ever (f : ℕ → Finset X) : Finset X := by
  classical
  exact Finset.univ.filter (fun x => ∃ n, x ∈ f n)

omit [DecidableEq X] in
@[simp] theorem mem_ever (f : ℕ → Finset X) (x : X) :
    x ∈ ever f ↔ ∃ n, x ∈ f n := by
  classical
  simp [ever]

/-- A monotone sequence of finite subsets of a finite space attains its union.
The index depends on the actual transcript and is not a runtime bound. -/
theorem ever_eq_prefix (f : ℕ → Finset X) (hf : Monotone f) :
    ∃ n, ever f = f n := by
  classical
  have h : ∀ s : Finset X, (∀ x ∈ s, ∃ n, x ∈ f n) → ∃ n, s ⊆ f n := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; exact ⟨0, Finset.empty_subset _⟩
    | @insert a s _ ih =>
      intro hs
      obtain ⟨m, hm⟩ := hs a (Finset.mem_insert_self ..)
      obtain ⟨n, hn⟩ := ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))
      refine ⟨max m n, Finset.insert_subset_iff.mpr ⟨?_, ?_⟩⟩
      · exact hf (le_max_left ..) hm
      · exact hn.trans (hf (le_max_right ..))
  obtain ⟨n, hn⟩ := h (ever f) (fun x hx => (mem_ever f x).mp hx)
  refine ⟨n, Finset.Subset.antisymm hn ?_⟩
  intro x hx
  exact (mem_ever f x).mpr ⟨n, hx⟩

noncomputable def visitedEver (p : Policy X) (r : Tapes X) (o : Oracle X) : Finset X :=
  ever (fun n => (run p r o n).visited)
noncomputable def checkedEver (p : Policy X) (r : Tapes X) (o : Oracle X) : Finset X :=
  ever (fun n => (run p r o n).checked)
noncomputable def outputsEver (p : Policy X) (r : Tapes X) (o : Oracle X) : Finset X :=
  ever (fun n => (run p r o n).outputs)

theorem visitedEver_eq_prefix (p : Policy X) (r : Tapes X) (o : Oracle X) :
    ∃ n, visitedEver p r o = (run p r o n).visited :=
  ever_eq_prefix _ (fun _ _ h => History.visited_mono (run_mono p r o h).subset)

theorem checkedEver_eq_prefix (p : Policy X) (r : Tapes X) (o : Oracle X) :
    ∃ n, checkedEver p r o = (run p r o n).checked :=
  ever_eq_prefix _ (fun _ _ h => History.checked_mono (run_mono p r o h).subset)

theorem outputsEver_eq_prefix (p : Policy X) (r : Tapes X) (o : Oracle X) :
    ∃ n, outputsEver p r o = (run p r o n).outputs :=
  ever_eq_prefix _ (fun _ _ h => History.outputs_mono (run_mono p r o h).subset)

theorem outputsEver_card_le (p : Policy X) (r : Tapes X) (o : Oracle X) :
    (outputsEver p r o).card ≤ 1 := by
  obtain ⟨n, hn⟩ := outputsEver_eq_prefix p r o
  rw [hn]
  exact run_outputs_card_le ..

theorem checkedEver_subset_visitedEver (p : Policy X) (r : Tapes X) (o : Oracle X)
    (hl : ∀ n, (run p r o n).halted = false →
      Local (run p r o n) (p (run p r o n))) :
    checkedEver p r o ⊆ visitedEver p r o := by
  intro x hx
  obtain ⟨n, hn⟩ := (mem_ever _ _).mp hx
  exact (mem_ever _ _).mpr ⟨n, checked_subset_visited p r o hl n hn⟩

theorem checkedEver_card_le (Q : ℕ) (p : Policy X) (r : Tapes X) (o : Oracle X)
    (hQ : ∀ n, (run p r o n).checks ≤ Q) :
    (checkedEver p r o).card ≤ Q := by
  obtain ⟨n, hn⟩ := checkedEver_eq_prefix p r o
  rw [hn]
  exact (History.card_checked_le _).trans (hQ n)

theorem visitedEver_card_le (b T : ℕ) (p : Policy X) (r : Tapes X) (o : Oracle X)
    (hb : ∀ n, (run p r o n).setups ≤ b)
    (hT : ∀ n, (run p r o n).updates ≤ T) :
    (visitedEver p r o).card ≤ b + T := by
  obtain ⟨n, hn⟩ := visitedEver_eq_prefix p r o
  rw [hn]
  exact (History.card_visited_le _).trans (Nat.add_le_add (hb n) (hT n))

/-- The coupling theorem for the full, possibly infinite all-negative run. -/
theorem succeeds_mem_negative (p : Policy X) (r : Tapes X) (o : Oracle X)
    (hs : Succeeds p r o) :
    ∃ x ∈ checkedEver p r negativeOracle ∪ outputsEver p r negativeOracle, o x = true := by
  rcases success_coupling p r o hs with ⟨n, x, hx, hm⟩ | ⟨n, x, hx, hm⟩
  · refine ⟨x, Finset.mem_union_left _ ((mem_ever _ _).mpr ⟨n, ?_⟩), hx⟩
    exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨.check x false, hm, rfl⟩)
  · refine ⟨x, Finset.mem_union_right _ ((mem_ever _ _).mpr ⟨n, ?_⟩), hx⟩
    exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨.output (some x), hm, rfl⟩)

namespace Cycle

variable {k : ℕ} [NeZero (N k)]

theorem visitedEver_exposure_le (d b T : ℕ) (p : Policy (Vertex k))
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (o : Oracle (Vertex k))
    (hl : ∀ n, (run p (lazyTapes z w) o n).halted = false →
      Local (run p (lazyTapes z w) o n) (p (run p (lazyTapes z w) o n)))
    (hb : ∀ n, (run p (lazyTapes z w) o n).setups ≤ b)
    (hT : ∀ n, (run p (lazyTapes z w) o n).updates ≤ T) :
    (exposure d (visitedEver p (lazyTapes z w) o)).card ≤ d * b + T := by
  obtain ⟨n, hn⟩ := visitedEver_eq_prefix p (lazyTapes z w) o
  rw [hn]
  exact (run_exposure_le d p z w o hl n).trans
    (Nat.add_le_add (Nat.mul_le_mul_left d (hb n)) (hT n))

end Cycle
end RandomWalkSearch
