import FourGeneratedSemigroups.SecondaryOrdering
import FourGeneratedSemigroups.StaircaseGeneratorBounds
import FourGeneratedSemigroups.BoundaryPresentation
import FourGeneratedSemigroups.MonomialReduction

noncomputable section
namespace FourGeneratedSemigroups

/-- Every minimally four-generated numerical semigroup has a finite presentation
with at most twice its actual pseudo-Frobenius type plus three relations. -/
theorem presentationNumber_le_twice_type_add_three {S : NumericalSemigroup}
    (G : FourGenerated S) : presentationNumber G.generators≤2*S.type+3 := by
  obtain ⟨e,he⟩ := exists_ordering G
  have hre : presentationNumber (G.reindex e).generators=presentationNumber G.generators :=
    presentationNumber_reindex G.generators e
  rw [← hre]
  have hmu := staircaseGeneratorNumber_le_twice_corners_add_one (G.reindex e)
  rcases he with ⟨hprimary,hgood⟩|⟨hsecondary,hdegree⟩
  · have hbound := presentationNumber_le_boundary (G.reindex e)
      (primary_staircase_weight_injective (G.reindex e) hprimary)
    by_cases hA : ((criticalExponent (G.reindex e).generators (G.reindex e).positive 3*
        (G.reindex e).generators 3 : ℕ) : ℤ)∈S.apery ((G.reindex e).generators 0)
    · have hr : fullSupportGeneratorNumber (G.reindex e)=0 := hgood.resolve_right (not_not.mpr hA)
      have ht := primary_topSlice_type_bound (G.reindex e) hprimary hA
      omega
    · have h30 := (criticalDegree_not_apery_iff_arc (G.reindex e) 3 (by decide)).mp hA
      have ht := type_eq_staircaseCorners_of_all_arcs (G.reindex e) hprimary h30
      omega
  · have hbound := presentationNumber_le_boundary (G.reindex e)
      (secondary_staircase_weight_injective (G.reindex e) hsecondary)
    have ht := secondary_topSlice_type_bound (G.reindex e) hsecondary hdegree
    omega

 theorem exists_minimalPresentation_card_le_twice_type_add_three {S : NumericalSemigroup}
    (G : FourGenerated S) : ∃R, IsMinimalPresentation G.generators R ∧ R.card≤2*S.type+3 := by
  obtain ⟨R,hR,hcard⟩ := exists_minimalPresentation_card G.generators
  exact ⟨R,hR,by rw [hcard]; exact presentationNumber_le_twice_type_add_three G⟩

end FourGeneratedSemigroups
