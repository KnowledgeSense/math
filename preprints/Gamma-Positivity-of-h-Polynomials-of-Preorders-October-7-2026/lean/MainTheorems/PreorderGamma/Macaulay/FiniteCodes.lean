import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fintype.EquivFin

namespace ResearchMain.PreorderGamma.Macaulay

open scoped BigOperators

variable {V : Type*} [Fintype V]

noncomputable def vertexIndex (v : V) : ℕ := (Fintype.equivFin V v).val

theorem vertexIndex_injective : Function.Injective (vertexIndex (V := V)) :=
  Fin.val_injective.comp (Fintype.equivFin V).injective

noncomputable def binaryCode (s : Finset V) : ℕ := ∑ v ∈ s, 2 ^ vertexIndex v

theorem binaryCode_eq_image_sum (s : Finset V) :
    binaryCode s = ∑ i ∈ s.image vertexIndex, 2 ^ i := by
  symm
  exact Finset.sum_image vertexIndex_injective.injOn

theorem binaryCode_injective : Function.Injective (binaryCode (V := V)) := by
  intro s t h
  apply Finset.image_injective vertexIndex_injective
  apply Finset.geomSum_injective (by decide : 2 ≤ (2 : ℕ))
  simpa only [← binaryCode_eq_image_sum] using h

theorem binaryCode_union [DecidableEq V] (s t : Finset V) (h : Disjoint s t) :
    binaryCode (s ∪ t) = binaryCode s + binaryCode t := by
  exact Finset.sum_union h

theorem binaryCode_sdiff_add [DecidableEq V] {s t : Finset V} (h : t ⊆ s) :
    binaryCode (s \ t) + binaryCode t = binaryCode s := by
  rw [← binaryCode_union _ _ disjoint_sdiff_self_left, Finset.sdiff_union_of_subset h]

end ResearchMain.PreorderGamma.Macaulay
