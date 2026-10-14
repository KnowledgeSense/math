import FourGeneratedSemigroups.CornerOrder
import Mathlib.Basic.Finite.Sum

noncomputable section
namespace FourGeneratedSemigroups
namespace PlaneStaircase

abbrev Point := ℕ × ℕ

def Corners (A : Set Point) : Set Point :=
  {a | a ∈ A ∧ ∀ b ∈ A, a ≤ b → b = a}

def Boundary (A : Set Point) : Set Point :=
  {a | a ∉ A ∧ ∀ b, b < a → b ∈ A}

lemma corner_eq {A : Set Point} {a b : Point}
    (ha : a ∈ Corners A) (hb : b ∈ A) (hab : a ≤ b) : a = b :=
  (ha.2 b hb hab).symm

lemma corner_eq_first {A : Set Point} {a b : Point}
    (ha : a ∈ Corners A) (hb : b ∈ Corners A) (he : a.1 = b.1) : a = b := by
  by_cases h : a.2 ≤ b.2
  · exact corner_eq ha hb.1 ⟨he.le,h⟩
  · exact (corner_eq hb ha.1 ⟨he.ge,by omega⟩).symm

lemma corner_eq_second {A : Set Point} {a b : Point}
    (ha : a ∈ Corners A) (hb : b ∈ Corners A) (he : a.2 = b.2) : a = b := by
  by_cases h : a.1 ≤ b.1
  · exact corner_eq ha hb.1 ⟨h,he.le⟩
  · exact (corner_eq hb ha.1 ⟨by omega,he.ge⟩).symm

lemma boundary_eq {A : Set Point} {a b : Point}
    (ha : a ∈ Boundary A) (hb : b ∈ Boundary A) (hab : a ≤ b) : a = b := by
  by_contra h
  exact ha.1 (hb.2 a (lt_of_le_of_ne hab h))

lemma boundary_eq_first {A : Set Point} {a b : Point}
    (ha : a ∈ Boundary A) (hb : b ∈ Boundary A) (he : a.1 = b.1) : a = b := by
  by_cases h : a.2 ≤ b.2
  · exact boundary_eq ha hb ⟨he.le,h⟩
  · exact (boundary_eq hb ha ⟨he.ge,by omega⟩).symm

lemma exists_corner {A : Set Point} (hf : A.Finite) {a : Point} (ha : a ∈ A) :
    ∃ b ∈ Corners A, a ≤ b := by
  obtain ⟨b,hab,hb,hm⟩ := hf.exists_le_maximal ha
  exact ⟨b,⟨hb,fun c hc hbc => le_antisymm (hm hc hbc) hbc⟩,hab⟩

lemma exists_boundary {A : Set Point} {a : Point} (ha : a ∉ A) :
    ∃ b ∈ Boundary A, b ≤ a := by
  obtain ⟨b,hb,hm⟩ := wellFounded_lt.has_min {b : Point | b ≤ a ∧ b ∉ A} ⟨a,le_rfl,ha⟩
  exact ⟨b,⟨hb.2,fun c hcb => by
    by_contra hc
    exact hm c ⟨hcb.le.trans hb.1,hc⟩ hcb⟩,hb.1⟩

lemma corners_finite {A : Set Point} (hf : A.Finite) : (Corners A).Finite :=
  hf.subset (fun _ h => h.1)

/-- The corner immediately to the left of a nonvertical boundary point. -/
lemma preceding_corner {A : Set Point} (hf : A.Finite) (hl : IsLowerSet A) {g : Point}
    (hg : g ∈ Boundary A) (hx : 0 < g.1) :
    ∃ q ∈ Corners A, q.1 + 1 = g.1 ∧ g.2 ≤ q.2 := by
  have hp : (g.1-1,g.2) < g := by
    apply lt_of_le_of_ne (show (g.1-1,g.2) ≤ g from ⟨by omega,le_rfl⟩)
    intro h
    have := congrArg Prod.fst h
    omega
  obtain ⟨q,hq,hpq⟩ := exists_corner hf (hg.2 _ hp)
  have hqx : q.1 < g.1 := by
    by_contra h
    exact hg.1 (hl ⟨by omega,hpq.2⟩ hq.1)
  exact ⟨q,hq,by have := hpq.1; omega,hpq.2⟩

def Generators (A B : Set Point) : Set Point := Boundary B ∩ A

def LostCorners (A B : Set Point) : Set Point := Corners A \ B

def NewCorners (A B : Set Point) : Set Point := Corners B \ Corners A

def InteriorGenerators (A B : Set Point) : Set Point :=
  {g | g ∈ Generators A B ∧ 0 < g.1 ∧ 0 < g.2}

lemma generators_finite {A B : Set Point} (hf : A.Finite) :
    (Generators A B).Finite := hf.subset (fun _ h => h.2)

lemma lostCorners_finite {A B : Set Point} (hf : A.Finite) :
    (LostCorners A B).Finite := (corners_finite hf).subset (fun _ h => h.1)

lemma newCorners_finite {A B : Set Point} (hf : B.Finite) :
    (NewCorners A B).Finite := (corners_finite hf).subset (fun _ h => h.1)

lemma shared_upper_unique {A B : Set Point} (hfB : B.Finite) (hlB : IsLowerSet B)
    {a b t : Point} (ha : a ∈ Boundary B) (hb : b ∈ Boundary B)
    (ht : t ∈ Corners A) (hat : a ≤ t) (hbt : b ≤ t)
    (haq : ∀ q ∈ Corners B, q.1+1=a.1 → q ∈ Corners A)
    (hbq : ∀ q ∈ Corners B, q.1+1=b.1 → q ∈ Corners A) : a = b := by
  have hnot : ∀ (a b : Point), a ∈ Boundary B → b ∈ Boundary B →
      a ≤ t → b ≤ t →
      (∀ q ∈ Corners B, q.1+1=b.1 → q ∈ Corners A) → ¬a.1 < b.1 := by
    intro a b ha hb hat hbt hbq hab
    obtain ⟨q,hq,hqx,hqy⟩ := preceding_corner hfB hlB hb (by omega)
    have hqA := hbq q hq hqx
    have hqa : q.2 < a.2 := by
      by_contra h
      exact ha.1 (hlB ⟨by omega,by omega⟩ hq.1)
    have hqt : q = t := corner_eq hqA ht.1
      ⟨by have := hbt.1; omega,by have := hat.2; omega⟩
    have := congrArg Prod.fst hqt
    have := hbt.1
    omega
  have h₁ := hnot a b ha hb hat hbt hbq
  have h₂ := hnot b a hb ha hbt hat haq
  exact boundary_eq_first ha hb (by omega)

/-- Every newly exposed generator can be charged injectively to a lost or a new corner. -/
theorem generators_le_lost_add_new {A B : Set Point}
    (hfA : A.Finite) (hfB : B.Finite) (hlB : IsLowerSet B) :
    Nat.card (Generators A B) ≤ Nat.card (LostCorners A B) + Nat.card (NewCorners A B) := by
  classical
  let T := LostCorners A B
  let U := NewCorners A B
  let R (g : Point) : T ⊕ U → Prop
    | Sum.inl t => g ≤ t.val ∧ ∀ q ∈ Corners B, q.1+1=g.1 → q ∈ Corners A
    | Sum.inr u => u.val.1+1=g.1
  have hex : ∀ g : Generators A B, ∃ o, R g.val o := by
    intro g
    by_cases hp : ∃ q ∈ Corners B, q.1+1=g.val.1 ∧ q ∉ Corners A
    · obtain ⟨q,hq,hqx,hqA⟩ := hp
      exact ⟨Sum.inr ⟨q,hq,hqA⟩,hqx⟩
    · obtain ⟨t,ht,hgt⟩ := exists_corner hfA g.property.2
      have htB : t ∉ B := by
        intro htB
        exact g.property.1.1 (hlB hgt htB)
      refine ⟨Sum.inl ⟨t,ht,htB⟩,hgt,?_⟩
      intro q hq hqx
      by_contra hqA
      exact hp ⟨q,hq,hqx,hqA⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro a b hab
    have ha := hf a
    have hb := hf b
    rw [←hab] at hb
    cases ho : f a with
    | inl t =>
      rw [ho] at ha hb
      exact Subtype.ext (shared_upper_unique hfB hlB a.property.1 b.property.1
        t.property.1 ha.1 hb.1 ha.2 hb.2)
    | inr u =>
      rw [ho] at ha hb
      exact Subtype.ext (boundary_eq_first a.property.1 b.property.1 (ha.symm.trans hb))
  let : Finite T := (lostCorners_finite hfA).to_subtype
  let : Finite U := (newCorners_finite hfB).to_subtype
  have h := Nat.card_le_card_of_injective f hinj
  simpa only [Nat.card_sum,T,U] using h

lemma right_step_not_mem {B : Set Point} {q : Point} (hq : q ∈ Corners B) :
    (q.1+1,q.2) ∉ B := by
  intro h
  have he := corner_eq hq h ⟨by omega,le_rfl⟩
  have := congrArg Prod.fst he
  omega

lemma upper_step_not_mem {B : Set Point} {q : Point} (hq : q ∈ Corners B) :
    (q.1,q.2+1) ∉ B := by
  intro h
  have he := corner_eq hq h ⟨le_rfl,by omega⟩
  have := congrArg Prod.snd he
  omega

lemma new_corner_step {A B : Set Point} (hBA : B ⊆ A) (hlA : IsLowerSet A)
    {q : Point} (hq : q ∈ NewCorners A B) :
    (q.1+1,q.2) ∈ A ∨ (q.1,q.2+1) ∈ A := by
  by_contra h
  push Not at h
  apply hq.2
  refine ⟨hBA hq.1.1,?_⟩
  intro b hb hqb
  apply Prod.ext
  · by_contra he
    exact h.1 (hlA ⟨by have := hqb.1; omega,hqb.2⟩ hb)
  · by_contra he
    exact h.2 (hlA ⟨hqb.1,by have := hqb.2; omega⟩ hb)

lemma right_generator {A B : Set Point} (hlA : IsLowerSet A) (hlB : IsLowerSet B)
    {q : Point} (hq : q ∈ Corners B) (hs : (q.1+1,q.2) ∈ A) :
    ∃ g ∈ Generators A B, g.1=q.1+1 := by
  obtain ⟨g,hg,hgq⟩ := exists_boundary (right_step_not_mem hq)
  have hx : g.1=q.1+1 := by
    by_contra hn
    exact hg.1 (hlB (show g ≤ q from ⟨by have := hgq.1; omega,hgq.2⟩) hq.1)
  exact ⟨g,⟨hg,hlA hgq hs⟩,hx⟩

lemma upper_generator {A B : Set Point} (hlA : IsLowerSet A) (hlB : IsLowerSet B)
    {q : Point} (hq : q ∈ Corners B) (hs : (q.1,q.2+1) ∈ A) :
    ∃ g ∈ Generators A B, g.2=q.2+1 := by
  obtain ⟨g,hg,hgq⟩ := exists_boundary (upper_step_not_mem hq)
  have hy : g.2=q.2+1 := by
    by_contra hn
    exact hg.1 (hlB (show g ≤ q from ⟨hgq.1,by have := hgq.2; omega⟩) hq.1)
  exact ⟨g,⟨hg,hlA hgq hs⟩,hy⟩

/-- A changed planar corner charges to a neighboring exposed generator. Only
positive-coordinate generators can receive two charges. -/
theorem new_le_generators_add_interior {A B : Set Point}
    (hfA : A.Finite) (hlA : IsLowerSet A) (hlB : IsLowerSet B) (hBA : B ⊆ A) :
    Nat.card (NewCorners A B) ≤
      Nat.card (Generators A B) + Nat.card (InteriorGenerators A B) := by
  classical
  let G := Generators A B
  let I := InteriorGenerators A B
  let R (q : Point) : G ⊕ I → Prop
    | Sum.inl g => g.val.1=q.1+1 ∨ (g.val.1=0 ∧ g.val.2=q.2+1)
    | Sum.inr g => g.val.2=q.2+1
  have hex : ∀ q : NewCorners A B, ∃ o, R q.val o := by
    intro q
    obtain hs | hs := new_corner_step hBA hlA q.property
    · obtain ⟨g,hg,hgx⟩ := right_generator hlA hlB q.property.1 hs
      exact ⟨Sum.inl ⟨g,hg⟩,Or.inl hgx⟩
    · obtain ⟨g,hg,hgy⟩ := upper_generator hlA hlB q.property.1 hs
      by_cases hx : g.1=0
      · exact ⟨Sum.inl ⟨g,hg⟩,Or.inr ⟨hx,hgy⟩⟩
      · exact ⟨Sum.inr ⟨g,hg,by omega,by omega⟩,hgy⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro a b hab
    have ha := hf a
    have hb := hf b
    rw [←hab] at hb
    cases ho : f a with
    | inl g =>
      rw [ho] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact Subtype.ext (corner_eq_first a.property.1 b.property.1 (by omega))
      · omega
      · omega
      · exact Subtype.ext (corner_eq_second a.property.1 b.property.1 (by omega))
    | inr g =>
      rw [ho] at ha hb
      exact Subtype.ext (corner_eq_second a.property.1 b.property.1 (by omega))
  let : Finite G := (generators_finite hfA).to_subtype
  let : Finite I := ((generators_finite hfA).subset (fun _ h => h.1)).to_subtype
  have h := Nat.card_le_card_of_injective f hinj
  simpa only [Nat.card_sum,G,I] using h

/-- Planar antichains have one more inner than outer corner, including the empty ideal. -/
theorem boundary_card_eq {A : Set Point} (hf : A.Finite) (hl : IsLowerSet A) :
    Nat.card (Boundary A) = Nat.card (Corners A) + 1 := by
  classical
  have hex : ∀ g : Boundary A, g.val.1 ≠ 0 →
      ∃ q : Corners A, q.val.1+1=g.val.1 := by
    intro g hg
    obtain ⟨q,hq,hqx,_⟩ := preceding_corner hf hl g.property (by omega)
    exact ⟨⟨q,hq⟩,hqx⟩
  let f : Boundary A → Option (Corners A) := fun g =>
    if h : g.val.1=0 then none else some (Classical.choose (hex g h))
  have hinj : Function.Injective f := by
    intro a b hab
    by_cases ha : a.val.1=0 <;> by_cases hb : b.val.1=0
    · exact Subtype.ext (boundary_eq_first a.property b.property (ha.trans hb.symm))
    · simp [f,ha,hb] at hab
    · simp [f,ha,hb] at hab
    · simp only [f,dite_eq_right ha,dite_eq_right hb,Option.some.injEq] at hab
      have hqa := Classical.choose_spec (hex a ha)
      have hqb := Classical.choose_spec (hex b hb)
      rw [hab] at hqa
      exact Subtype.ext (boundary_eq_first a.property b.property (hqa.symm.trans hqb))
  have hsurj : Function.Surjective f := by
    intro o
    cases o with
    | none =>
      obtain ⟨m,hm⟩ := hf.bddAbove
      have hnot : (0,m.2+1) ∉ A := by
        intro h
        have := (hm h).2
        omega
      obtain ⟨g,hg,hgm⟩ := exists_boundary hnot
      have hg0 : g.1=0 := by have := hgm.1; omega
      exact ⟨⟨g,hg⟩,by simp [f,hg0]⟩
    | some q =>
      obtain ⟨g,hg,hgx⟩ := right_generator (A := Set.univ) (by intro a b hab hb; trivial)
        hl q.property (Set.mem_univ _)
      have hg0 : g.1≠0 := by omega
      refine ⟨⟨g,hg.1⟩,?_⟩
      simp only [f,dite_eq_right hg0,Option.some.injEq]
      apply Subtype.ext
      apply corner_eq_first (Classical.choose (hex ⟨g,hg.1⟩ hg0)).property q.property
      have hc := Classical.choose_spec (hex ⟨g,hg.1⟩ hg0)
      dsimp only at hc
      omega
  let : Finite (Corners A) := (corners_finite hf).to_subtype
  let := Fintype.ofFinite (Corners A)
  have he := Nat.card_eq_of_bijective f ⟨hinj,hsurj⟩
  simpa only [Nat.card_eq_fintype_card,Fintype.card_option] using he

lemma boundary_finite {A : Set Point} (hf : A.Finite) (hl : IsLowerSet A) :
    (Boundary A).Finite := by
  have hc := boundary_card_eq hf hl
  by_contra h
  have hz : Nat.card (Boundary A)=0 := @Nat.card_eq_zero_of_infinite _ (Set.infinite_coe_iff.mpr h)
  omega

/-- Corner changes satisfy an exact conservation law. -/
theorem corners_balance {A B : Set Point} (hfA : A.Finite) (hfB : B.Finite) (hBA : B ⊆ A) :
    Nat.card (Corners A) + Nat.card (NewCorners A B) =
      Nat.card (Corners B) + Nat.card (LostCorners A B) := by
  have hs : Corners A ∩ B = Corners A ∩ Corners B := by
    ext q
    constructor
    · rintro ⟨hq,hqB⟩
      exact ⟨hq,hqB,fun b hb hqb => hq.2 b (hBA hb) hqb⟩
    · exact fun h => ⟨h.1,h.2.1⟩
  have h₁ := Set.ncard_sdiff_add_ncard_of_subset
    (show Corners A ∩ Corners B ⊆ Corners A from Set.inter_subset_left)
    (corners_finite hfA)
  have h₂ := Set.ncard_sdiff_add_ncard_of_subset
    (show Corners A ∩ Corners B ⊆ Corners B from Set.inter_subset_right)
    (corners_finite hfB)
  have he₁ : Corners A \ (Corners A ∩ Corners B) = LostCorners A B := by
    rw [←hs]
    ext q
    simp [LostCorners]
  have he₂ : Corners B \ (Corners A ∩ Corners B) = NewCorners A B := by
    exact Set.sdiff_inter_self_eq_sdiff
  rw [he₁] at h₁
  rw [he₂] at h₂
  simp only [Nat.card_coe_set_eq]
  omega

@[simp] lemma corners_empty : Corners (∅ : Set Point)=∅ := by
  ext p
  simp [Corners]

@[simp] lemma boundary_empty : Boundary (∅ : Set Point)={(0,0)} := by
  ext p
  constructor
  · intro hp
    have hzero : (0,0) ≤ p := ⟨Nat.zero_le _,Nat.zero_le _⟩
    have he : (0,0)=p := by
      by_contra hn
      exact hp.2 (0,0) (lt_of_le_of_ne hzero hn)
    simpa only [Set.mem_singleton_iff] using he.symm
  · intro hp
    have he : p=(0,0) := hp
    subst p
    refine ⟨Set.notMem_empty _,?_⟩
    intro b hb
    have hx := hb.le.1
    have hy := hb.le.2
    have he : b=(0,0) := Prod.ext (by omega) (by omega)
    exact (hb.ne he).elim

@[simp] lemma newCorners_empty (A : Set Point) : NewCorners A ∅=∅ := by
  simp [NewCorners]

lemma generators_empty {A : Set Point} (hzero : (0,0) ∈ A) :
    Generators A ∅={(0,0)} := by
  simp [Generators,Set.singleton_inter_of_mem hzero]

end PlaneStaircase
end FourGeneratedSemigroups
