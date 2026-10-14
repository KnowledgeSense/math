import MainTheorems.PreorderGamma.SimplicialRealization.QuotientCuts
import MainTheorems.PreorderGamma.TransportHall

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

def positiveSlice (A : Finset E) (z : E → ℤ) : Finset E := A.filter fun i => 0 < z i

def negativeSlice (A : Finset E) (z : E → ℤ) : Finset E := A.filter fun i => z i < 0

omit [Fintype E] [DecidableEq E] [Preorder E] in
theorem positiveSlice_sum (A : Finset E) (z : E → ℤ) :
    ((∑ i ∈ A, (z i).toNat : ℕ) : ℤ) = ∑ i ∈ positiveSlice A z, z i := by
  classical
  rw [Nat.cast_sum, positiveSlice, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> omega

omit [Fintype E] [DecidableEq E] [Preorder E] in
theorem negativeSlice_sum (A : Finset E) (z : E → ℤ) :
    ((∑ i ∈ A, (-z i).toNat : ℕ) : ℤ) = -(∑ i ∈ negativeSlice A z, z i) := by
  classical
  rw [Nat.cast_sum, ← Finset.sum_neg_distrib, negativeSlice, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> omega

noncomputable def orderNeighbors (A : Finset E) : Finset E :=
  graphNeighbors (fun a b : E => b ≤ a) A

theorem positive_negative_complement_noCut (A : Finset E) (z : E → ℤ) :
    NoCutEdge (positiveSlice A z) (negativeSlice (Finset.univ \ orderNeighbors A) z) := by
  classical
  intro a ha b hb hba
  have haA := (Finset.mem_filter.mp ha).1
  have hbN : b ∉ orderNeighbors A :=
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hb).1).2
  exact hbN (mem_graphNeighbors.mpr ⟨a, haA, hba⟩)

theorem quotientIntegerPoint_hall_cut {t : ℕ} {z : E → ℤ}
    (hz : QuotientIntegerPoint t z) (A : Finset E) :
    (∑ i ∈ A, (z i).toNat) +
      (∑ j ∈ Finset.univ \ orderNeighbors A, (-z j).toNat) ≤ t := by
  classical
  have hc := quotientIntegerPoint_cut (positiveSlice A z)
    (negativeSlice (Finset.univ \ orderNeighbors A) z)
    (positive_negative_complement_noCut A z) hz
  have hp := positiveSlice_sum A z
  have hn := negativeSlice_sum (Finset.univ \ orderNeighbors A) z
  have hn' : (∑ j ∈ negativeSlice (Finset.univ \ orderNeighbors A) z, z j) =
      -((∑ j ∈ Finset.univ \ orderNeighbors A, (-z j).toNat : ℕ) : ℤ) := by linarith
  rw [← hp, hn', sub_neg_eq_add] at hc
  exact_mod_cast hc

omit [DecidableEq E] in
theorem orderNeighbors_univ : orderNeighbors (Finset.univ : Finset E) = Finset.univ := by
  classical
  ext b
  simp only [Finset.mem_univ, iff_true]
  exact mem_graphNeighbors.mpr ⟨b, Finset.mem_univ _, le_rfl⟩

omit [DecidableEq E] in
theorem orderNeighbors_empty : orderNeighbors (∅ : Finset E) = ∅ := by
  classical
  ext b
  simp [orderNeighbors, mem_graphNeighbors]

theorem quotientIntegerPoint_mass_bounds {t : ℕ} {z : E → ℤ}
    (hz : QuotientIntegerPoint t z) : positiveMass z ≤ t ∧ negativeMass z ≤ t := by
  classical
  have hp := quotientIntegerPoint_hall_cut hz Finset.univ
  have hn := quotientIntegerPoint_hall_cut hz ∅
  constructor
  · simpa [positiveMass, orderNeighbors_univ] using hp
  · simpa [negativeMass, orderNeighbors_empty] using hn

end ResearchMain.PreorderGamma.SimplicialRealization
