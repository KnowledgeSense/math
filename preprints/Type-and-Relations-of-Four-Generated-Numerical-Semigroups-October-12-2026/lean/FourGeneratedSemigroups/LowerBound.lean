import FourGeneratedSemigroups.RelationLowerBounds
import FourGeneratedSemigroups.UpperBound

noncomputable section
namespace FourGeneratedSemigroups
variable {S : NumericalSemigroup} (G : FourGenerated S)

lemma primary_nonmonomial_presentation_lower_bound (hG : PrimaryOrdering G)
    (hr : fullSupportGeneratorNumber G=0)
    (hA : ((criticalExponent G.generators G.positive 3*G.generators 3 : ℕ) : ℤ)∈S.apery (G.generators 0))
    (R : Finset (Factorization×Factorization)) (hR : IsPresentation G.generators R) :
    S.type+1≤R.card := by
  let n : AperyDegree G := ⟨criticalExponent G.generators G.positive 3*G.generators 3,hA⟩
  let p := aperyRepresentative G n
  have hpT : p∈staircase G := aperyRepresentative_mem G n
  have hp3 : p 3=0 := critical_apery_representative_third_zero G hA
  have hp : factorizationMap G.generators p=criticalExponent G.generators G.positive 3*G.generators 3 :=
    aperyRepresentative_weight G n
  have hp1 := primary_critical_normal_form_first_positive G hG p hpT hp3 hp
  have hp2 := primary_critical_normal_form_second_positive G hG p hpT hp3 hp
  have hm := presentation_card_ge_boundary_sub_one G p hp3 hp
    (primary_staircase_weight_injective G hG)
    (primary_boundaryGenerator_redundant_unique G ℚ hG p hpT hp3 hp1 hp2 hp
      (no_fullSupport_of_number_zero G hr)) R hR
  have hc := corners_add_two_le_staircaseGeneratorNumber_add_fullSupport G
  have ht := type_le_staircaseCorners G (finite_staircase G)
  omega

lemma secondary_presentation_lower_bound (hG : SecondaryCriticalOrdering G)
    (hsecondary : ∀v, incomingDegree (CriticalArc G.generators G.positive) v≤1)
    (R : Finset (Factorization×Factorization)) (hR : IsPresentation G.generators R) :
    S.type+1≤R.card := by
  let p : Factorization := Finsupp.single 2 (criticalExponent G.generators G.positive 2)
  have hp3 : p 3=0 := by simp [p]
  have hp1 : p 1=0 := by simp [p]
  have hp2 : 0<p 2 := by simpa [p] using (criticalExponent_spec G.generators G.positive 2).1
  have hp : factorizationMap G.generators p=criticalExponent G.generators G.positive 3*G.generators 3 :=
    by simpa [p] using hG.2
  have hpT : p∈staircase G := by
    refine ⟨by simp [p],?_,?_⟩
    · simpa [hp3] using (criticalExponent_spec G.generators G.positive 3).1
    · rw [hp]
      exact secondary_critical_degree_mem_apery G hG hsecondary
  have hr := secondary_fullSupportGeneratorNumber_zero G hsecondary
  have hm := presentation_card_ge_boundary_sub_one G p hp3 hp
    (secondary_staircase_weight_injective G hG)
    (secondary_boundaryGenerator_redundant_unique G ℚ
      (criticalArc_unique_of_secondary G.generators G.positive hsecondary) hG.1
      p hpT hp1 hp3 hp2 hp (no_fullSupport_of_number_zero G hr)) R hR
  have hc := corners_add_two_le_staircaseGeneratorNumber_add_fullSupport G
  have ht := type_le_staircaseCorners G (finite_staircase G)
  omega

/-- The lower relation bound for every actual minimally four-generated numerical semigroup. -/
theorem type_add_one_le_presentationNumber : S.type+1≤presentationNumber G.generators := by
  obtain ⟨e,he⟩ := exists_ordering G
  have hre : presentationNumber (G.reindex e).generators=presentationNumber G.generators :=
    presentationNumber_reindex G.generators e
  rw [← hre]
  obtain ⟨R,hR,hcard⟩ := exists_minimalPresentation_card (G.reindex e).generators
  rw [← hcard]
  rcases he with ⟨hprimary,hgood⟩|⟨hsecondary,hdegree⟩
  · by_cases hA : ((criticalExponent (G.reindex e).generators (G.reindex e).positive 3*
        (G.reindex e).generators 3 : ℕ) : ℤ)∈S.apery ((G.reindex e).generators 0)
    · exact primary_nonmonomial_presentation_lower_bound (G.reindex e) hprimary
        (hgood.resolve_right (not_not.mpr hA)) hA R hR.1
    · have h30 := (criticalDegree_not_apery_iff_arc (G.reindex e) 3 (by decide)).mp hA
      have hm := presentation_card_ge_boundary_monomial (G.reindex e) hprimary h30 R hR.1
      have ht := type_eq_staircaseCorners_of_all_arcs (G.reindex e) hprimary h30
      have hc := corners_add_two_le_staircaseGeneratorNumber_add_fullSupport (G.reindex e)
      have hr := primary_fullSupportGeneratorNumber_le_one (G.reindex e) hprimary
      omega
  · exact secondary_presentation_lower_bound (G.reindex e) hsecondary hdegree R hR.1

end FourGeneratedSemigroups
