import FourGeneratedSemigroups.TopSliceTypeBound
import FourGeneratedSemigroups.MonomialReduction

noncomputable section
namespace FourGeneratedSemigroups
variable {S : NumericalSemigroup} (G : FourGenerated S)

lemma primary_critical_normal_form_second_positive (hG : PrimaryOrdering G)
    (p : Factorization) (hpT : p∈staircase G) (hp3 : p 3=0)
    (hp : factorizationMap G.generators p=
      criticalExponent G.generators G.positive 3*G.generators 3) : 0<p 2 := by
  by_contra hn
  have hp2 : p 2=0 := by omega
  have hshape : p=Finsupp.single 1 (p 1) := by
    ext i
    fin_cases i <;> simp_all [hpT.1]
  have hw : p 1*G.generators 1=
      criticalExponent G.generators G.positive 3*G.generators 3 := by
    rw [hshape,factorizationMap_single] at hp
    exact hp
  have hpos : 0<p 1 := by
    have := (criticalExponent_spec G.generators G.positive 3).1
    have := G.positive 3
    nlinarith
  have hmin := criticalExponent_le G.generators G.positive 1 (p 1)
    ⟨hpos,Finsupp.single 3 (criticalExponent G.generators G.positive 3),by simp,
      by simpa using hw.symm⟩
  have hbound := apery_coordinate_lt_of_criticalArc G 1 hG.1 p hpT.2.2
  omega

theorem primary_topSlice_type_bound (hG : PrimaryOrdering G)
    (ha : ((criticalExponent G.generators G.positive 3*G.generators 3 : ℕ) : ℤ)∈
      S.apery (G.generators 0)) :
    Nat.card (staircaseCorners G)≤S.type+fullSupportGeneratorNumber G+1 := by
  let n : AperyDegree G := ⟨criticalExponent G.generators G.positive 3*G.generators 3,ha⟩
  let p := aperyRepresentative G n
  have hpT : p∈staircase G := aperyRepresentative_mem G n
  have hp3 : p 3=0 := critical_apery_representative_third_zero G ha
  have hp : factorizationMap G.generators p=
      criticalExponent G.generators G.positive 3*G.generators 3 := aperyRepresentative_weight G n
  exact staircaseCorners_card_le_type_add_fullSupport G p hpT.1 hp3
    (primary_critical_normal_form_second_positive G hG p hpT hp3 hp) hp
    (primary_staircase_weight_injective G hG)

theorem secondary_fullSupportGeneratorNumber_zero
    (hsecondary : ∀ v,incomingDegree (CriticalArc G.generators G.positive) v≤1) :
    fullSupportGeneratorNumber G=0 := by
  let : IsEmpty {a : Factorization // a∈staircaseBoundary G ∧ a 0=0 ∧
      0<a 1 ∧ 0<a 2 ∧ 0<a 3} :=
    ⟨fun a => secondary_no_fullSupport G hsecondary a.val
      ((fullSupportBoundary_iff G a.val).mpr a.property)⟩
  simp [fullSupportGeneratorNumber]

/-- The secondary paired relation has the second pure power as its normal form. -/
theorem secondary_topSlice_type_bound (hG : SecondaryCriticalOrdering G)
    (hsecondary : ∀ v,incomingDegree (CriticalArc G.generators G.positive) v≤1) :
    Nat.card (staircaseCorners G)≤S.type+1 := by
  let p : Factorization := Finsupp.single 2 (criticalExponent G.generators G.positive 2)
  have hp : factorizationMap G.generators p=
      criticalExponent G.generators G.positive 3*G.generators 3 := by
    simpa [p] using hG.2
  have hh := staircaseCorners_card_le_type_add_fullSupport G p (by simp [p]) (by simp [p])
    (by simpa [p] using (criticalExponent_spec G.generators G.positive 2).1) hp
    (secondary_staircase_weight_injective G hG)
  simpa only [secondary_fullSupportGeneratorNumber_zero G hsecondary,add_zero] using hh

end FourGeneratedSemigroups
