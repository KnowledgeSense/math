import SumsetRanges.OrdinaryBasics

open Finset
open scoped Pointwise
namespace SumsetRanges

section
variable {α β : Type*} [AddCommMonoid α] [AddCommMonoid β]
  [DecidableEq α] [DecidableEq β]

theorem ordinarySums_image (A : Finset α) (f : α →+ β) (q : ℕ) :
    ordinarySums (A.image f) q = (ordinarySums A q).image f := by
  ext x
  constructor
  · intro hx
    obtain ⟨v,hv,rfl⟩ := (mem_ordinarySums _ _ _).mp hx
    have he (i : Fin q) : ∃a∈A,f a=v i := Finset.mem_image.mp (hv i)
    choose w hw hwf using he
    refine Finset.mem_image.mpr ⟨∑i,w i,(mem_ordinarySums _ _ _).mpr ⟨w,hw,rfl⟩,?_⟩
    simp only [map_sum,hwf]
  · intro hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := (mem_ordinarySums _ _ _).mp ha
    apply (mem_ordinarySums _ _ _).mpr
    exact ⟨fun i => f (v i),fun i => Finset.mem_image.mpr ⟨v i,hv i,rfl⟩,(map_sum f _ _).symm⟩

theorem ordinarySums_affine_image (A : Finset α) (f : α →+ β) (c : β) (q : ℕ) :
    ordinarySums (A.image (fun a => f a+c)) q =
      (ordinarySums A q).image (fun a => f a+q • c) := by
  ext x
  constructor
  · intro hx
    obtain ⟨v,hv,rfl⟩ := (mem_ordinarySums _ _ _).mp hx
    have he (i : Fin q) : ∃a∈A,f a+c=v i := Finset.mem_image.mp (hv i)
    choose w hw hwf using he
    refine Finset.mem_image.mpr ⟨∑i,w i,(mem_ordinarySums _ _ _).mpr ⟨w,hw,rfl⟩,?_⟩
    simp only [←hwf,Finset.sum_add_distrib,map_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  · intro hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := (mem_ordinarySums _ _ _).mp ha
    apply (mem_ordinarySums _ _ _).mpr
    refine ⟨fun i => f (v i)+c,fun i => Finset.mem_image.mpr ⟨v i,hv i,rfl⟩,?_⟩
    simp [Finset.sum_add_distrib]

theorem mem_ordinarySums_union (A B : Finset α) (q : ℕ) (x : α) :
    x∈ordinarySums (A∪B) q ↔
      ∃p s,p+s=q ∧ ∃a∈ordinarySums A p,∃b∈ordinarySums B s,a+b=x := by
  constructor
  · intro hx
    induction q generalizing x with
    | zero =>
        have hx' : x=0 := by simpa [ordinarySums] using hx
        subst x
        exact ⟨0,0,rfl,0,by simp [ordinarySums],0,by simp [ordinarySums],by simp⟩
    | succ q ih =>
        obtain ⟨v,hv,w,hw,rfl⟩ := Finset.mem_add.mp hx
        obtain ⟨p,s,hps,a,ha,b,hb,rfl⟩ := ih _ hw
        rcases Finset.mem_union.mp hv with hv | hv
        · refine ⟨p+1,s,by omega,v+a,Finset.mem_add.mpr ⟨v,hv,a,ha,rfl⟩,b,hb,?_⟩
          simp [add_assoc]
        · refine ⟨p,s+1,by omega,a,ha,v+b,Finset.mem_add.mpr ⟨v,hv,b,hb,rfl⟩,?_⟩
          simp [add_left_comm]
  · rintro ⟨p,s,rfl,a,ha,b,hb,rfl⟩
    rw [ordinarySums_add]
    exact Finset.mem_add.mpr ⟨a,ordinarySums_mono Finset.subset_union_left p ha,
      b,ordinarySums_mono Finset.subset_union_right s hb,rfl⟩
end
end SumsetRanges
