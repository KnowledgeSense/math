import MainTheorems.PreorderReciprocity.LatticeGeometry
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.SetTheory.Cardinal.Finite

namespace ResearchMain.PreorderReciprocity

variable {E : Type*} [Fintype E] [Preorder E]

theorem closedIntegerPoints_finite (r s : ℤ) :
    {x : E → ℤ | ClosedIntegerPoints r s x}.Finite := by
  have hf : {x : E → ℤ | ∀ e, x e ∈ Set.Icc 0 (r * Fintype.card E + s)}.Finite :=
    Set.Finite.pi' fun _ => Set.finite_Icc _ _
  apply hf.subset
  intro x hx e
  exact ⟨hx.1 e, integer_coordinate_bound hx e⟩

theorem strictIntegerPoints_finite (r s : ℤ) :
    {x : E → ℤ | StrictIntegerPoints r s x}.Finite := by
  apply ((closedIntegerPoints_finite (E := E) (r - 1) (s - 1)).image addUnit).subset
  intro x hx
  refine ⟨subUnit x, (subUnit_mem_iff r s x).2 hx, ?_⟩
  funext e
  simp [addUnit, subUnit]

noncomputable def closedCount (r s : ℤ) : ℕ :=
  Nat.card {x : E → ℤ // ClosedIntegerPoints r s x}

noncomputable def strictCount (r s : ℤ) : ℕ :=
  Nat.card {x : E → ℤ // StrictIntegerPoints r s x}

omit [Fintype E] in
theorem strictCount_eq_closedCount (r s : ℤ) :
    strictCount (E := E) r s = closedCount (E := E) (r - 1) (s - 1) := by
  exact (Nat.card_congr (integerPointTranslation (E := E) r s)).symm

noncomputable def latticeCount (r s : ℤ) : ℕ :=
  Nat.card {x : E → ℤ // (fun e => (x e : ℝ)) ∈ polytope (r : ℝ) (s : ℝ)}

noncomputable def interiorLatticeCount (r s : ℤ) : ℕ :=
  Nat.card {x : E → ℤ //
    (fun e => (x e : ℝ)) ∈ interior (polytope (r : ℝ) (s : ℝ))}

theorem latticeCount_eq_closedCount (r s : ℤ) :
    latticeCount (E := E) r s = closedCount (E := E) r s := by
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => integer_mem_polytope r s x)

theorem interiorLatticeCount_eq_strictCount (r s : ℤ) :
    interiorLatticeCount (E := E) r s = strictCount (E := E) r s := by
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => integer_mem_interior r s x)

theorem interior_lattice_shift (r s : ℤ) :
    interiorLatticeCount (E := E) r s = latticeCount (E := E) (r - 1) (s - 1) := by
  rw [interiorLatticeCount_eq_strictCount, strictCount_eq_closedCount,
    latticeCount_eq_closedCount]

end ResearchMain.PreorderReciprocity
