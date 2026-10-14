import FourGeneratedSemigroups.TopSliceGap

noncomputable section
namespace FourGeneratedSemigroups
variable {S : NumericalSemigroup} (G : FourGenerated S)

/-- At most one spurious corner is exceptional; all others inject into actual
full-support boundary generators. -/
theorem spuriousCorners_card_le (p : Factorization) (hp0 : p 0=0) (hp3 : p 3=0)
    (hp2 : 0<p 2)
    (hp : factorizationMap G.generators p=
      criticalExponent G.generators G.positive 3*G.generators 3) :
    Nat.card (spuriousCorners G)≤fullSupportGeneratorNumber G+1 := by
  classical
  by_cases hs : (spuriousCorners G).Nonempty
  swap
  · have he : spuriousCorners G=∅ := Set.not_nonempty_iff_eq_empty.mp hs
    simp [he]
  let C : Set Factorization :=
    {v | v∈staircaseCorners G ∧ v 3+1=criticalExponent G.generators G.positive 3}
  have hCfin : C.Finite := (finite_staircase G).subset (fun _ h => h.1.1)
  obtain ⟨v0,hv0⟩ := hs
  have hCne : C.Nonempty := ⟨v0,hv0.1,spuriousCorner_top G v0 hv0⟩
  obtain ⟨l,hl,hmin⟩ := hCfin.exists_minimalFor (fun v => v 1) C hCne
  have hleft : ∀ v∈C,l 1≤v 1 := by
    intro v hv
    by_cases h : v 1≤l 1
    · exact hmin hv h
    · omega
  let F := {h : Factorization // h∈staircaseBoundary G ∧ h 0=0 ∧ 0<h 1 ∧ 0<h 2 ∧ 0<h 3}
  have hFfin : Finite F :=
    ((finite_staircaseBoundary G (finite_staircase G)).subset
      (fun _ h => h.1)).to_subtype
  let := hFfin
  let := Fintype.ofFinite F
  have hex : ∀ v : spuriousCorners G,v.val≠l → ∃ h : F,h.val 2=v.val 2+1 := by
    intro v hvl
    have hvC : v.val∈C := ⟨v.property.1,spuriousCorner_top G v.val v.property⟩
    have hlv : l 1<v.val 1 := by
      have hle := hleft v.val hvC
      by_contra hn
      have hx : l 1=v.val 1 := by omega
      have hz : l 3=v.val 3 := by have := hl.2; have := hvC.2; omega
      exact hvl (corner_eq_of_first_eq G l v.val hl.1 hvC.1 hz hx).symm
    let D : Set Factorization := {u | u∈C ∧ u 1<v.val 1}
    have hDfin : D.Finite := hCfin.subset (fun _ h => h.1)
    obtain ⟨u,hu,hmax⟩ := hDfin.exists_maximalFor (fun u => u 1) D ⟨l,hl,hlv⟩
    have hprev : ∀ w∈staircaseCorners G,w 3=v.val 3 → w 1<v.val 1 → w 1≤u 1 := by
      intro w hw hw3 hw1
      have hwD : w∈D := ⟨⟨hw,by simpa only [hw3] using hvC.2⟩,hw1⟩
      by_cases h : u 1≤w 1
      · exact hmax hwD h
      · omega
    have huz : u 3=v.val 3 := by have := hu.1.2; have := hvC.2; omega
    obtain ⟨h,hh,hh2⟩ := spurious_gap_fullSupport G p hp0 hp3 hp2 hp u v.val
      hu.1.1 v.property huz hu.2 hprev
    exact ⟨⟨h,(fullSupportBoundary_iff G h).mp hh⟩,hh2⟩
  let f : spuriousCorners G → Option F := fun v =>
    if h : v.val=l then none else some (Classical.choose (hex v h))
  have hf : Function.Injective f := by
    intro a b hab
    by_cases ha : a.val=l <;> by_cases hb : b.val=l
    · exact Subtype.ext (ha.trans hb.symm)
    · simp [f,ha,hb] at hab
    · simp [f,ha,hb] at hab
    · simp only [f,dite_eq_right ha,dite_eq_right hb,Option.some.injEq] at hab
      have hha := Classical.choose_spec (hex a ha)
      have hhb := Classical.choose_spec (hex b hb)
      have hy : a.val 2=b.val 2 := by
        have hh := congrArg (fun h : F => h.val 2) hab
        omega
      have hz : a.val 3=b.val 3 := by
        have := spuriousCorner_top G a.val a.property
        have := spuriousCorner_top G b.val b.property
        omega
      exact Subtype.ext (corner_eq_of_second_eq G a.val b.val a.property.1 b.property.1 hz hy)
  have hcard := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card,Fintype.card_option,fullSupportGeneratorNumber,F] using hcard

end FourGeneratedSemigroups
