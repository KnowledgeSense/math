import Dowling.Matroid
import Mathlib.Combinatorics.Matroid.Rank.ENat

noncomputable section
namespace Dowling
open Set
open scoped Classical
variable {G : Type*} [Group G] [Finite G] {n : ℕ}

theorem fullMatroid_basis_rank {I S : Set (Edge G n)}
    (hI : (fullMatroid G n).IsBasis I S) : constraintRank S = constraintRank I := by
  apply le_antisymm _ (constraintRank_mono hI.subset)
  apply constraintRank_le_of_implied
  intro e heS
  by_cases heI : e ∈ I
  · rw [Set.insert_eq_of_mem heI]
  · rcases constraintRank_insert I e with h | h
    · exact h
    · exfalso
      apply heI
      apply hI.mem_of_insert_indep heS
      change EquationIndep (insert e I)
      have hi : EquationIndep I := hI.indep
      unfold EquationIndep at *
      rw [h, hi, Set.ncard_insert_of_notMem heI]

/-- Every subset has the rank derived from its actual gain-equation solution space. -/
theorem fullMatroid_eRk (S : Set (Edge G n)) :
    (fullMatroid G n).eRk S = (constraintRank S : ℕ∞) := by
  obtain ⟨I,hI⟩ := (fullMatroid G n).exists_isBasis S (subset_univ _)
  have hi : EquationIndep I := hI.indep
  rw [hI.eRk_eq_encard, fullMatroid_basis_rank hI, hi, I.toFinite.cast_ncard_eq]

theorem fullMatroid_mem_closure (S : Set (Edge G n)) (e : Edge G n) :
    e ∈ (fullMatroid G n).closure S ↔ ∀ x ∈ solutions G n S, Satisfies G n x e := by
  rw [← constraintRank_insert_eq_iff]
  constructor
  · intro he
    have h : (fullMatroid G n).eRk (insert e S) = (fullMatroid G n).eRk S := by
      rw [← Matroid.eRk_closure_eq, Matroid.closure_insert_eq_of_mem_closure he,
        Matroid.eRk_closure_eq]
    rw [fullMatroid_eRk, fullMatroid_eRk] at h
    exact_mod_cast h
  · intro hr
    by_contra he
    have h := (fullMatroid G n).eRk_insert_eq_add_one (e := e) (X := S)
      ⟨by trivial,he⟩
    rw [fullMatroid_eRk, fullMatroid_eRk] at h
    have hn : constraintRank (insert e S) = constraintRank S + 1 := by exact_mod_cast h
    omega

/-- The retained-joint restriction has exactly the same all-subset rank on its ground. -/
theorem matroid_eRk (X : Set (Fin n)) (S : Set (Edge G n)) (hS : S ⊆ ground G n X) :
    (matroid G n X).eRk S = (constraintRank S : ℕ∞) := by
  rw [matroid, Matroid.restrict_eRk_eq _ hS, fullMatroid_eRk]

end Dowling
