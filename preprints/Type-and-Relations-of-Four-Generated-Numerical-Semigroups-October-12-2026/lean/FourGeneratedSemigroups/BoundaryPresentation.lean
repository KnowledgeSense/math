import FourGeneratedSemigroups.StaircasePresentation

noncomputable section
namespace FourGeneratedSemigroups
variable {S : NumericalSemigroup} (G : FourGenerated S)

lemma exists_factorization_using_zero (a : Factorization)
    (ha : (factorizationMap G.generators a : ℤ)∉S.apery (G.generators 0)) :
    ∃ b : Factorization,0<b 0 ∧ factorizationMap G.generators b=factorizationMap G.generators a := by
  have hm : S.memInt ((factorizationMap G.generators a : ℤ)-(G.generators 0 : ℤ)) := by
    by_contra hn
    exact ha ⟨(NumericalSemigroup.memInt_natCast S _).mpr (G.factorization_mem a),hn⟩
  obtain ⟨n,hn,hnS⟩ := hm
  obtain ⟨b,hb⟩ := (G.generates n).mp hnS
  refine ⟨Finsupp.single 0 1+b,by simp,?_⟩
  simp only [map_add,factorizationMap_single,one_mul,hb]
  omega

noncomputable def carryFactorization (a : Factorization) : Factorization := by
  classical
  exact if h : (factorizationMap G.generators a : ℤ)∉S.apery (G.generators 0) then
    Classical.choose (exists_factorization_using_zero G a h) else a

lemma carryFactorization_spec (a : Factorization)
    (ha : (factorizationMap G.generators a : ℤ)∉S.apery (G.generators 0)) :
    0<carryFactorization G a 0 ∧
      factorizationMap G.generators (carryFactorization G a)=factorizationMap G.generators a := by
  classical
  simp only [carryFactorization,dite_eq_left ha]
  exact Classical.choose_spec (exists_factorization_using_zero G a ha)

noncomputable def threeBoundaryFinset : Finset Factorization := by
  classical
  exact (finite_staircaseBoundary G (finite_staircase G)).toFinset.filter (fun a => a 0=0)

@[simp] lemma mem_threeBoundaryFinset (a : Factorization) :
    a∈threeBoundaryFinset G ↔ a∈staircaseBoundary G ∧ a 0=0 := by
  classical
  simp [threeBoundaryFinset]

lemma topPower_mem_threeBoundary : topPower G∈threeBoundaryFinset G := by
  rw [mem_threeBoundaryFinset]
  exact ⟨top_power_mem_boundary G,by simp [topPower]⟩

lemma boundary_not_apery (a : Factorization) (ha : a∈threeBoundaryFinset G)
    (hne : a≠topPower G) :
    (factorizationMap G.generators a : ℤ)∉S.apery (G.generators 0) := by
  intro hA
  have hh := mem_threeBoundaryFinset G a |>.mp ha
  exact hh.1.1 ⟨hh.2,boundary_below_top_unless_pure G a hh.1 hne,hA⟩

noncomputable def boundaryPresentation (p : Factorization) : Finset (Factorization × Factorization) := by
  classical
  exact insert (topPower G,p) (((threeBoundaryFinset G).erase (topPower G)).image
    (fun a => (a,carryFactorization G a)))

/-- The boundary construction gives an actual finite presentation of the numerical semigroup. -/
theorem boundaryPresentation_isPresentation (p : Factorization) (hp3 : p 3=0)
    (hp : factorizationMap G.generators p=
      criticalExponent G.generators G.positive 3*G.generators 3)
    (hinj : Set.InjOn (fun c : Factorization => (factorizationMap G.generators c : ℤ))
      (staircase G)) :
    IsPresentation G.generators (boundaryPresentation G p) := by
  classical
  let C := addConGen (fun a b => (a,b)∈boundaryPresentation G p)
  have hC : C≤factorizationCongruence G.generators := by
    apply AddCon.addConGen_le.mpr
    intro a b hab
    change factorizationMap G.generators a=factorizationMap G.generators b
    simp only [boundaryPresentation,Finset.mem_insert,Finset.mem_image] at hab
    rcases hab with hab|⟨c,hc,he⟩
    · have ha : a=topPower G := congrArg Prod.fst hab
      have hb : b=p := congrArg Prod.snd hab
      simp [ha,hb,topPower,hp]
    · have ha : c=a := congrArg Prod.fst he
      have hb : carryFactorization G c=b := congrArg Prod.snd he
      have hh := carryFactorization_spec G c (boundary_not_apery G c
        (Finset.mem_erase.mp hc).2 (Finset.mem_erase.mp hc).1)
      exact (congrArg (factorizationMap G.generators) ha.symm).trans
        (hh.2.symm.trans (congrArg (factorizationMap G.generators) hb))
  apply boundary_congruence_eq_factorization G C hC p hp3
  · exact AddConGen.Rel.of _ _ (by simp [boundaryPresentation])
  · intro h hh hh0 hne
    refine ⟨carryFactorization G h,?_,?_⟩
    · apply AddConGen.Rel.of
      simp only [boundaryPresentation,Finset.mem_insert,Finset.mem_image]
      right
      exact ⟨h,Finset.mem_erase.mpr ⟨hne,(mem_threeBoundaryFinset G h).mpr ⟨hh,hh0⟩⟩,rfl⟩
    · exact (carryFactorization_spec G h
        (boundary_not_apery G h ((mem_threeBoundaryFinset G h).mpr ⟨hh,hh0⟩) hne)).1
  · exact hinj

theorem boundaryPresentation_card_le (p : Factorization) :
    (boundaryPresentation G p).card≤(threeBoundaryFinset G).card := by
  classical
  calc
    _ ≤ (((threeBoundaryFinset G).erase (topPower G)).image
        (fun a => (a,carryFactorization G a))).card+1 := Finset.card_insert_le _ _
    _ ≤ ((threeBoundaryFinset G).erase (topPower G)).card+1 :=
      Nat.add_le_add_right Finset.card_image_le 1
    _ = _ := Finset.card_erase_add_one (topPower_mem_threeBoundary G)


theorem threeBoundaryFinset_card :
    (threeBoundaryFinset G).card=staircaseGeneratorNumber G := by
  let e : {a : Factorization // a∈staircaseBoundary G ∧ a 0=0} ≃ ↥(threeBoundaryFinset G) :=
    Equiv.subtypeEquivRight (fun a => (mem_threeBoundaryFinset G a).symm)
  change (threeBoundaryFinset G).card=Nat.card {a : Factorization // a∈staircaseBoundary G ∧ a 0=0}
  calc
    _ = Nat.card ↥(threeBoundaryFinset G) := by simp only [Nat.card_eq_fintype_card,Fintype.card_coe]
    _ = _ := (Nat.card_congr e).symm

/-- The attained minimum number of genuine semigroup relations is bounded by
the actual number of three-variable staircase boundary generators. -/
theorem presentationNumber_le_staircaseGeneratorNumber (p : Factorization) (hp3 : p 3=0)
    (hp : factorizationMap G.generators p=
      criticalExponent G.generators G.positive 3*G.generators 3)
    (hinj : Set.InjOn (fun c : Factorization => (factorizationMap G.generators c : ℤ))
      (staircase G)) :
    presentationNumber G.generators≤staircaseGeneratorNumber G := by
  calc
    _ ≤ (boundaryPresentation G p).card := presentationNumber_le _
      (boundaryPresentation G p) (boundaryPresentation_isPresentation G p hp3 hp hinj)
    _ ≤ (threeBoundaryFinset G).card := boundaryPresentation_card_le G p
    _ = _ := threeBoundaryFinset_card G


/-- The boundary bound uses an actual critical factorization, which always exists. -/
theorem presentationNumber_le_boundary
    (hinj : Set.InjOn (fun c : Factorization => (factorizationMap G.generators c : ℤ))
      (staircase G)) :
    presentationNumber G.generators≤staircaseGeneratorNumber G := by
  obtain ⟨p,hp3,hp⟩ := (criticalExponent_spec G.generators G.positive 3).2
  exact presentationNumber_le_staircaseGeneratorNumber G p hp3 hp hinj

end FourGeneratedSemigroups
