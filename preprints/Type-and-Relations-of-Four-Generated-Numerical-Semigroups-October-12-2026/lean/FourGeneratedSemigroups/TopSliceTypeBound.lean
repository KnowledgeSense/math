import FourGeneratedSemigroups.TopSliceCount

noncomputable section
namespace FourGeneratedSemigroups
variable {S : NumericalSemigroup} (G : FourGenerated S)

def genuineCorners : Set Factorization :=
  {c | c∈staircaseCorners G ∧
    (factorizationMap G.generators c : ℤ)∈S.maximalApery (G.generators 0)}

noncomputable def genuineCornersEquivMaximalApery
    (hinj : Set.InjOn (fun c : Factorization => (factorizationMap G.generators c : ℤ))
      (staircase G)) :
    genuineCorners G ≃ S.maximalApery (G.generators 0) :=
  Equiv.ofBijective (fun c => ⟨(factorizationMap G.generators c.val : ℤ),c.property.2⟩) (by
    constructor
    · intro a b hab
      apply Subtype.ext
      exact hinj a.property.1.1 b.property.1.1 (congrArg Subtype.val hab)
    · intro w
      obtain ⟨c,hc,hc0,hc3⟩ := apery_has_bounded_factorization G w.val w.property.1
      have hT : c∈staircase G := ⟨hc0,hc3,by simpa only [hc] using w.property.1⟩
      have hmax : (factorizationMap G.generators c : ℤ)∈S.maximalApery (G.generators 0) := by
        simpa only [hc] using w.property
      exact ⟨⟨c,corner_of_maximalApery G c hT hmax,hmax⟩,Subtype.ext hc⟩)

noncomputable def cornerPartition :
    staircaseCorners G ≃ (genuineCorners G ⊕ spuriousCorners G) := by
  classical
  exact
    { toFun := fun c => if h : (factorizationMap G.generators c.val : ℤ)∈
          S.maximalApery (G.generators 0) then
        Sum.inl ⟨c.val,c.property,h⟩ else Sum.inr ⟨c.val,c.property,h⟩
      invFun := fun c => c.elim (fun a => ⟨a.val,a.property.1⟩) (fun a => ⟨a.val,a.property.1⟩)
      left_inv := by intro c; dsimp only; split_ifs <;> rfl
      right_inv := by
        intro c
        cases c with
        | inl a => simp [a.property.2]
        | inr a => simp [a.property.2] }

theorem corners_card_eq_type_add_spurious
    (hinj : Set.InjOn (fun c : Factorization => (factorizationMap G.generators c : ℤ))
      (staircase G)) :
    Nat.card (staircaseCorners G)=S.type+Nat.card (spuriousCorners G) := by
  have hgen : (genuineCorners G).Finite := (finite_staircase G).subset (fun _ h => h.1.1)
  have hspur : (spuriousCorners G).Finite := (finite_staircase G).subset (fun _ h => h.1.1)
  let := hgen.to_subtype
  let := hspur.to_subtype
  rw [Nat.card_congr (cornerPartition G),Nat.card_sum]
  have hh := Nat.card_congr (genuineCornersEquivMaximalApery G hinj)
  rw [hh,←S.type_eq_card_maximalApery _ (G.generator_mem 0) (Nat.ne_of_gt (G.positive 0))]

/-- The top-slice estimate, proved for the actual staircase and actual semigroup type. -/
theorem staircaseCorners_card_le_type_add_fullSupport (p : Factorization)
    (hp0 : p 0=0) (hp3 : p 3=0) (hp2 : 0<p 2)
    (hp : factorizationMap G.generators p=
      criticalExponent G.generators G.positive 3*G.generators 3)
    (hinj : Set.InjOn (fun c : Factorization => (factorizationMap G.generators c : ℤ))
      (staircase G)) :
    Nat.card (staircaseCorners G)≤S.type+fullSupportGeneratorNumber G+1 := by
  rw [corners_card_eq_type_add_spurious G hinj]
  have hh := spuriousCorners_card_le G p hp0 hp3 hp2 hp
  omega

end FourGeneratedSemigroups
