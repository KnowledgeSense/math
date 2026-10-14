import Dowling.ConstraintClosure

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] [Finite G] {n : ℕ}

theorem constraintRank_union_finset_le (S : Set (Edge G n)) (T : Finset (Edge G n)) :
    constraintRank (S ∪ (T : Set (Edge G n))) ≤ constraintRank S + T.card := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert e T he ih =>
    have h := constraintRank_insert_le (S ∪ (T : Set (Edge G n))) e
    rw [Finset.coe_insert, Set.union_insert, Finset.card_insert_of_notMem he]
    omega

theorem constraintRank_union_le (S T : Set (Edge G n)) :
    constraintRank (S ∪ T) ≤ constraintRank S + T.ncard := by
  have h := constraintRank_union_finset_le S T.toFinite.toFinset
  simpa only [Set.Finite.coe_toFinset, ← Set.ncard_eq_toFinset_card] using h

theorem constraintRank_le_ncard (S : Set (Edge G n)) : constraintRank S ≤ S.ncard := by
  simpa using constraintRank_union_le (∅ : Set (Edge G n)) S

theorem constraintRank_gap {S T : Set (Edge G n)} (hST : S ⊆ T) :
    constraintRank T ≤ constraintRank S + (T.ncard - S.ncard) := by
  have h := constraintRank_union_le S (T \ S)
  rw [Set.union_sdiff_cancel hST, Set.ncard_sdiff hST] at h
  exact h

/-- Independence is the actual number of nonredundant equations. -/
def EquationIndep (I : Set (Edge G n)) : Prop := constraintRank I = I.ncard

@[simp] theorem equationIndep_empty : EquationIndep (∅ : Set (Edge G n)) := by
  simp [EquationIndep]

theorem EquationIndep.mono {I J : Set (Edge G n)} (hI : EquationIndep I) (hJI : J ⊆ I) :
    EquationIndep J := by
  have hgap := constraintRank_gap hJI
  have hJ := constraintRank_le_ncard J
  have hcard := Set.ncard_le_ncard hJI
  unfold EquationIndep at *
  omega

theorem equationIndep_augment {I J : Set (Edge G n)} (hI : EquationIndep I)
    (hJ : EquationIndep J) (hcard : I.encard < J.encard) :
    ∃ e ∈ J, e ∉ I ∧ EquationIndep (insert e I) := by
  have hc : I.ncard < J.ncard := by
    rw [← I.toFinite.cast_ncard_eq, ← J.toFinite.cast_ncard_eq] at hcard
    exact_mod_cast hcard
  by_contra hno
  have himplied : ∀ e ∈ J, constraintRank (insert e I) = constraintRank I := by
    intro e he
    by_cases hei : e ∈ I
    · rw [Set.insert_eq_of_mem hei]
    · rcases constraintRank_insert I e with hr | hr
      · exact hr
      · exfalso
        apply hno
        refine ⟨e,he,hei,?_⟩
        unfold EquationIndep at *
        rw [hr, hI, Set.ncard_insert_of_notMem hei]
  have h := constraintRank_le_of_implied I J himplied
  unfold EquationIndep at hI hJ
  omega

end Dowling
