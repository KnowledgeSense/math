import MainTheorems.PreorderReciprocity.Basic
import MainTheorems.PreorderGamma.Basic
import MainTheorems.PreorderGamma.DemandMatching
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Prod
import Lean.Elab.Tactic.NormCast

namespace ResearchMain.PreorderReciprocity

variable {E : Type*} [Fintype E] [Preorder E]

def NatIntegerPoints (r s : ℕ) (x : E → ℕ) : Prop :=
  ∀ I : Finset E, I.Nonempty → IsIdeal I → ∑ e ∈ I, x e ≤ r * I.card + s

abbrev CapacityVertices (E : Type*) (r s : ℕ) := (E × Fin r) ⊕ Fin s

def capacityRelation (r s : ℕ) (e : E) : CapacityVertices E r s → Prop
  | Sum.inl p => p.1 ≤ e
  | Sum.inr _ => True

theorem capacity_neighbors (r s : ℕ) (I : Finset E) (hI : I.Nonempty) :
    PreorderGamma.graphNeighbors (capacityRelation r s) I =
      ((PreorderGamma.downward I).product Finset.univ).disjSum Finset.univ := by
  classical
  ext b
  cases b with
  | inl p =>
    simp only [PreorderGamma.mem_graphNeighbors, capacityRelation,
      Finset.inl_mem_disjSum, Finset.mem_product, Finset.mem_univ, and_true,
      Finset.product_eq_sprod, PreorderGamma.mem_downward]
  | inr p =>
    simp only [PreorderGamma.mem_graphNeighbors, capacityRelation,
      Finset.inr_mem_disjSum, Finset.mem_univ, and_true, iff_true]
    exact hI

theorem capacity_neighbors_card (r s : ℕ) (I : Finset E) (hI : I.Nonempty) :
    (PreorderGamma.graphNeighbors (capacityRelation r s) I).card =
      r * (PreorderGamma.downward I).card + s := by
  rw [capacity_neighbors r s I hI]
  simp [Nat.mul_comm]

theorem natIntegerPoints_iff_demand (r s : ℕ) (x : E → ℕ) :
    NatIntegerPoints r s x ↔ PreorderGamma.IsDemand (capacityRelation r s) x := by
  classical
  constructor
  · intro hx I
    by_cases hI : I = ∅
    · subst I
      simp [PreorderGamma.graphNeighbors]
    · have hn : I.Nonempty := Finset.nonempty_iff_ne_empty.mpr hI
      have hd : (PreorderGamma.downward I).Nonempty :=
        hn.mono (PreorderGamma.subset_downward I)
      have hb := hx (PreorderGamma.downward I) hd (PreorderGamma.downward_isIdeal I)
      have hs : (∑ e ∈ I, x e) ≤ ∑ e ∈ PreorderGamma.downward I, x e :=
        Finset.sum_le_sum_of_subset (PreorderGamma.subset_downward I)
      rw [capacity_neighbors_card r s I hn]
      exact hs.trans hb
  · intro hx I hI hIdeal
    have hb := hx I
    rw [capacity_neighbors_card r s I hI,
      PreorderGamma.downward_eq_of_isIdeal hIdeal] at hb
    exact hb

theorem natIntegerPoints_iff_assignment (r s : ℕ) (x : E → ℕ) :
    NatIntegerPoints r s x ↔
      ∃ f : PreorderGamma.DemandCells x → CapacityVertices E r s,
        Function.Injective f ∧ ∀ c, capacityRelation r s c.1 (f c) := by
  rw [natIntegerPoints_iff_demand, PreorderGamma.demand_iff_cell_transversal]
  rfl

omit [Fintype E] in
theorem natIntegerPoints_iff_int (r s : ℕ) (x : E → ℕ) :
    NatIntegerPoints r s x ↔
      ClosedIntegerPoints (r : ℤ) (s : ℤ) (fun e => (x e : ℤ)) := by
  constructor
  · intro hx
    refine ⟨fun e => Int.natCast_nonneg (x e), ?_⟩
    intro I hI hIdeal
    dsimp only
    exact_mod_cast hx I hI hIdeal
  · intro hx I hI hIdeal
    have hb := hx.2 I hI hIdeal
    dsimp only at hb
    exact_mod_cast hb

end ResearchMain.PreorderReciprocity
