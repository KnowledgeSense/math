import MainTheorems.PreorderGamma.Basic
import MainTheorems.PreorderGamma.Bipartite

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {E : Type*} [Fintype E] [Preorder E]

noncomputable def latticePointEquiv :
    {x : E → ℕ // IsLatticePoint x} ≃
      {x : E → Fin (Fintype.card E + 1) // IsLatticePoint fun a => (x a).val} := by
  classical
  refine
    { toFun := fun x => ⟨fun a => ⟨x.val a,
        Nat.lt_succ_of_le (lattice_coordinate_bound x.property a)⟩, x.property⟩
      invFun := fun x => ⟨fun a => (x.val a).val, x.property⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    rfl
  · intro x
    apply Subtype.ext
    funext a
    exact Fin.ext rfl

theorem preorder_demand_neighbors (s : Finset E) :
    graphNeighbors (fun a b : E => b ≤ a) s = downward s := by
  classical
  ext a
  simp

theorem isLatticePoint_iff_preorderDemand (x : E → ℕ) :
    IsLatticePoint x ↔ IsDemand (fun a b : E => b ≤ a) x := by
  constructor
  · intro hx s
    rw [preorder_demand_neighbors]
    have hsum : (∑ a ∈ s, x a) ≤ ∑ a ∈ downward s, x a :=
      Finset.sum_le_sum_of_subset (subset_downward s)
    exact hsum.trans (hx (downward s) (downward_isIdeal s))
  · intro hx s hs
    have h := hx s
    rwa [preorder_demand_neighbors, downward_eq_of_isIdeal hs] at h

end ResearchMain.PreorderGamma
