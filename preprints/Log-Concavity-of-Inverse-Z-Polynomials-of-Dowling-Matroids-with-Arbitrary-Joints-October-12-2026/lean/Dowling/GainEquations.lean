import Dowling.Definitions

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

@[simp] theorem gainAct_none (g : G) : gainAct G none g = none := rfl
@[simp] theorem gainAct_some (x g : G) : gainAct G (some x) g = some (x*g) := rfl
@[simp] theorem gainAct_one (x : Option G) : gainAct G x 1 = x := by
  cases x <;> simp [gainAct]

theorem gainAct_mul (x : Option G) (g h : G) :
    gainAct G (gainAct G x g) h = gainAct G x (g*h) := by
  cases x <;> simp [gainAct, mul_assoc]

theorem gainAct_reverse (x y : Option G) (g : G) :
    y = gainAct G x g ↔ x = gainAct G y g⁻¹ := by
  constructor
  · intro h
    rw [h, gainAct_mul, mul_inv_cancel, gainAct_one]
  · intro h
    rw [h, gainAct_mul, inv_mul_cancel, gainAct_one]

/-- A nonidentity circle gain forces the adjoined zero; no group element is fixed. -/
theorem gainAct_fixed_iff (x : Option G) (g : G) (hg : g ≠ 1) :
    gainAct G x g = x ↔ x = none := by
  cases x with
  | none => simp
  | some a =>
    simp only [gainAct_some, Option.some.injEq, Option.some_ne_none, iff_false]
    intro h
    exact hg ((mul_left_cancel (show a*g = a*1 by simpa using h)))

theorem zero_satisfies (e : Edge G n) : Satisfies G n (fun _ => none) e := by
  cases e <;> rfl

theorem zero_mem_solutions (S : Set (Edge G n)) : (fun _ => none) ∈ solutions G n S :=
  fun e _ => zero_satisfies e

theorem solutions_antitone {S T : Set (Edge G n)} (h : S ⊆ T) :
    solutions G n T ⊆ solutions G n S := fun _ hx e he => hx e (h he)

/-- Closure by all actual gain-equation solutions, restricted to the chosen ground. -/
def equationClosure (X : Set (Fin n)) (S : Set (Edge G n)) : Set (Edge G n) :=
  {e | e ∈ ground G n X ∧ ∀ x ∈ solutions G n S, Satisfies G n x e}

theorem subset_equationClosure (X : Set (Fin n)) {S : Set (Edge G n)}
    (hS : S ⊆ ground G n X) : S ⊆ equationClosure X S :=
  fun e he => ⟨hS he, fun _ hx => hx e he⟩

theorem equationClosure_mono (X : Set (Fin n)) {S T : Set (Edge G n)} (h : S ⊆ T) :
    equationClosure X S ⊆ equationClosure X T :=
  fun _ he => ⟨he.1, fun x hx => he.2 x (solutions_antitone h hx)⟩

theorem solutions_equationClosure (X : Set (Fin n)) {S : Set (Edge G n)}
    (hS : S ⊆ ground G n X) : solutions G n (equationClosure X S) = solutions G n S := by
  apply Set.Subset.antisymm
  · exact solutions_antitone (subset_equationClosure X hS)
  · exact fun x hx e he => he.2 x hx

theorem equationClosure_idem (X : Set (Fin n)) {S : Set (Edge G n)}
    (hS : S ⊆ ground G n X) : equationClosure X (equationClosure X S) = equationClosure X S := by
  ext e
  change (e ∈ ground G n X ∧ ∀ x ∈ solutions G n (equationClosure X S), Satisfies G n x e) ↔
    (e ∈ ground G n X ∧ ∀ x ∈ solutions G n S, Satisfies G n x e)
  rw [solutions_equationClosure X hS]

end Dowling
