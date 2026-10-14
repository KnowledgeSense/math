import MainTheorems.Tuza.PerfectFactors
import Mathlib.Data.ZMod.Basic

namespace ResearchMain.Tuza

def cycleGadget : SimpleGraph (Fin 2 × ZMod 3) where
  Adj x y := (x.1 = 0 ∧ y.1 = 0 ∧ x.2 ≠ y.2) ∨ (x.1 ≠ y.1 ∧ x.2 ≠ y.2)
  symm := ⟨by
    intro x y h
    rcases h with h | h
    · exact Or.inl ⟨h.2.1, h.1, h.2.2.symm⟩
    · exact Or.inr ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h
    · exact h.2.2 rfl
    · exact h.1 rfl⟩

instance : DecidableRel cycleGadget.Adj := fun x y =>
  inferInstanceAs (Decidable ((x.1 = 0 ∧ y.1 = 0 ∧ x.2 ≠ y.2) ∨
    (x.1 ≠ y.1 ∧ x.2 ≠ y.2)))

def cycleGadgetTriangles : Finset (Finset (Fin 2 × ZMod 3)) :=
  {{(0, 0), (0, 1), (1, 2)}, {(0, 1), (0, 2), (1, 0)}, {(0, 2), (0, 0), (1, 1)}}

theorem cycleGadget_packing : Packing cycleGadget cycleGadgetTriangles := by
  constructor
  · decide
  · decide

def cycleGadgetDecomposition : TriangleDecomposition cycleGadget where
  triangles := cycleGadgetTriangles
  packing := cycleGadget_packing
  covers := by
    intro e
    induction e using Sym2.inductionOn with
    | hf x y =>
      revert y x
      decide

def emptyDecomposition (V : Type*) [DecidableEq V] :
    TriangleDecomposition (⊥ : SimpleGraph V) where
  triangles := ∅
  packing := packing_empty _
  covers := by
    intro e he
    simp at he

def fourMatching (i : Fin 3) : SimpleGraph (Fin 4) where
  Adj x y := x ≠ y ∧ Nat.xor x.val y.val = i.val + 1
  symm := ⟨by intro x y h; exact ⟨h.1.symm, by simpa [Nat.xor_comm] using h.2⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

instance (i : Fin 3) : DecidableRel (fourMatching i).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ Nat.xor x.val y.val = i.val + 1))

def fourFactors : PerfectFactors (Fin 4) (Fin 3) where
  graph := fourMatching
  matching := by decide
  separated := by decide
  perfect := by decide

theorem fourFactors_union : fourFactors.unionGraph = ⊤ := by
  ext x y
  change (∃ i, (fourMatching i).Adj x y) ↔ x ≠ y
  revert y x
  decide

def fourFactorDecomposition : FactorDecomposition (Fin 4) (Fin 3) where
  factors := fourFactors
  triangles := by
    rw [fourFactors_union, sdiff_self]
    exact emptyDecomposition _

def sixMatching (i : Fin 5) : SimpleGraph (Fin 6) where
  Adj x y := x ≠ y ∧ ((x.val = 5 ∧ y.val = i.val) ∨ (y.val = 5 ∧ x.val = i.val) ∨
    (x.val < 5 ∧ y.val < 5 ∧ (x.val + y.val) % 5 = (2 * i.val) % 5))
  symm := ⟨by
    intro x y h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨h.2.1, h.1, by simpa [Nat.add_comm] using h.2.2⟩)⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

instance (i : Fin 5) : DecidableRel (sixMatching i).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ ((x.val = 5 ∧ y.val = i.val) ∨
    (y.val = 5 ∧ x.val = i.val) ∨
    (x.val < 5 ∧ y.val < 5 ∧ (x.val + y.val) % 5 = (2 * i.val) % 5))))

def sixFactors : PerfectFactors (Fin 6) (Fin 5) where
  graph := sixMatching
  matching := by decide
  separated := by decide
  perfect := by decide

theorem sixFactors_union : sixFactors.unionGraph = ⊤ := by
  ext x y
  change (∃ i, (sixMatching i).Adj x y) ↔ x ≠ y
  revert y x
  decide

def sixFactorDecomposition : FactorDecomposition (Fin 6) (Fin 5) where
  factors := sixFactors
  triangles := by
    rw [sixFactors_union, sdiff_self]
    exact emptyDecomposition _

end ResearchMain.Tuza
