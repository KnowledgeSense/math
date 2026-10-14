import Dowling.ConfigurationBounds
import Mathlib.Data.Fin.Basic

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

/-- The full zero block. -/
def zeroPartition : GainPartition G n where
  code _ := none
  rooted := by intro i j g h; cases h
  least := by intro i j g h; cases h

@[simp] theorem zeroPartition_roots : (zeroPartition : GainPartition G n).roots = ∅ := by
  ext i
  simp only [GainPartition.roots, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty]
  change ((none : Option (Fin n × G)) = some (i,1)) ↔ False
  simp

theorem zeroPartition_admissible_marked (X : Set (Fin n)) (hX : X.Nonempty) :
    Admissible X (zeroPartition : GainPartition G n) := by
  obtain ⟨j,hj⟩ := hX
  exact fun _ _ => Or.inl ⟨j,hj,rfl⟩

theorem zeroPartition_admissible_nontrivial [Nontrivial G] (X : Set (Fin n)) (hn : 2 ≤ n) :
    Admissible X (zeroPartition : GainPartition G n) := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  intro i _
  obtain ⟨j,hji⟩ := exists_ne i
  exact Or.inr ⟨inferInstance,j,hji,rfl⟩

theorem flatEdges_zeroPartition (X : Set (Fin n)) :
    flatEdges X (zeroPartition : GainPartition G n) = ground G n X := by
  apply Set.Subset.antisymm (flatEdges_subset_ground X _)
  intro e he
  refine ⟨he,?_⟩
  intro x hx
  have hz := ((zeroPartition : GainPartition G n).mem_solutionSet x).mp hx
  cases e with
  | inl i => exact hz.1 i rfl
  | inr e =>
    change x e.head = gainAct G (x e.tail) e.gain
    rw [hz.1 e.head rfl, hz.1 e.tail rfl, gainAct_none]

variable [Finite G]

theorem matroid_eRank_of_zero_admissible (X : Set (Fin n))
    (hX : Admissible X (zeroPartition : GainPartition G n)) : (matroid G n X).eRank = n := by
  rw [Matroid.eRank_def, matroid_ground, ← flatEdges_zeroPartition X, flatEdges_eRk X _ hX,
    zeroPartition_roots, Finset.card_empty, Nat.sub_zero]

theorem matroid_eRank_marked (X : Set (Fin n)) (hX : X.Nonempty) :
    (matroid G n X).eRank = n :=
  matroid_eRank_of_zero_admissible X (zeroPartition_admissible_marked X hX)

theorem matroid_eRank_nontrivial [Nontrivial G] (X : Set (Fin n)) (hn : 2 ≤ n) :
    (matroid G n X).eRank = n :=
  matroid_eRank_of_zero_admissible X (zeroPartition_admissible_nontrivial X hn)

theorem full_matroid_eRank : (matroid G n Set.univ).eRank = n :=
  matroid_eRank_of_zero_admissible Set.univ (admissible_univ _)

end Dowling
