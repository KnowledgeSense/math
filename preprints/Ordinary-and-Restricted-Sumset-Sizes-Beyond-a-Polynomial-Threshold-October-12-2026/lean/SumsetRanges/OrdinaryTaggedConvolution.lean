import SumsetRanges.OrdinaryImages
import SumsetRanges.TaggedConvolution

open Finset
open scoped Pointwise
namespace SumsetRanges
section
variable {α β : Type*} [AddCommMonoid α] [AddCommMonoid β]
  [DecidableEq α] [DecidableEq β]

def taggedLeftHom : α →+ (ℕ × α) × (ℕ × β) where
  toFun a := ((0,a),(0,0))
  map_zero' := rfl
  map_add' _ _ := by ext <;> simp

def taggedRightHom : β →+ (ℕ × α) × (ℕ × β) where
  toFun b := ((0,0),(0,b))
  map_zero' := rfl
  map_add' _ _ := by ext <;> simp

theorem taggedUnion_eq_images (A : Finset α) (B : Finset β) :
    taggedUnion A B = A.image (fun a => ((1,a),((0:ℕ),(0:β)))) ∪
      B.image (fun b => (((0:ℕ),(0:α)),(1,b))) := by
  ext x
  simp only [taggedUnion,Finset.mem_map,Finset.mem_disjSum,Finset.mem_union,Finset.mem_image]
  constructor
  · rintro ⟨a,ha,rfl⟩
    cases a with
    | inl a => exact Or.inl ⟨a,by simpa using ha,rfl⟩
    | inr b => exact Or.inr ⟨b,by simpa using ha,rfl⟩
  · rintro (⟨a,ha,rfl⟩ | ⟨b,hb,rfl⟩)
    · exact ⟨Sum.inl a,by simpa using ha,rfl⟩
    · exact ⟨Sum.inr b,by simpa using hb,rfl⟩

theorem ordinarySums_leftImage (A : Finset α) (q : ℕ) :
    ordinarySums (A.image (fun a => ((1,a),((0:ℕ),(0:β))))) q =
      (ordinarySums A q).image (fun a => ((q,a),((0:ℕ),(0:β)))) := by
  simpa [taggedLeftHom] using ordinarySums_affine_image A
    (taggedLeftHom (α := α) (β := β)) ((1,0),(0,0)) q

theorem ordinarySums_rightImage (B : Finset β) (q : ℕ) :
    ordinarySums (B.image (fun b => (((0:ℕ),(0:α)),(1,b)))) q =
      (ordinarySums B q).image (fun b => (((0:ℕ),(0:α)),(q,b))) := by
  simpa [taggedRightHom] using ordinarySums_affine_image B
    (taggedRightHom (α := α) (β := β)) ((0,0),(1,0)) q

theorem ordinarySums_taggedUnion (A : Finset α) (B : Finset β) (q : ℕ) :
    ordinarySums (taggedUnion A B) q = (range (q+1)).biUnion (fun p =>
      ((ordinarySums A p) ×ˢ (ordinarySums B (q-p))).image
        (fun ab => ((p,ab.1),(q-p,ab.2)))) := by
  rw [taggedUnion_eq_images]
  ext x
  rw [mem_ordinarySums_union]
  constructor
  · rintro ⟨p,s,hps,a,ha,b,hb,rfl⟩
    rw [ordinarySums_leftImage] at ha
    rw [ordinarySums_rightImage] at hb
    obtain ⟨a',ha',hea⟩ := Finset.mem_image.mp ha
    obtain ⟨b',hb',heb⟩ := Finset.mem_image.mp hb
    subst a; subst b
    have hs : q-p=s := by omega
    refine Finset.mem_biUnion.mpr ⟨p,Finset.mem_range.mpr (by omega),?_⟩
    rw [hs]
    exact Finset.mem_image.mpr ⟨(a',b'),Finset.mem_product.mpr ⟨ha',hb'⟩,by simp⟩
  · intro hx
    obtain ⟨p,hp,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    refine ⟨p,q-p,by have := Finset.mem_range.mp hp; omega,((p,a),(0,0)),?_,((0,0),(q-p,b)),?_,by simp⟩
    · rw [ordinarySums_leftImage]
      exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
    · rw [ordinarySums_rightImage]
      exact Finset.mem_image.mpr ⟨b,hb,rfl⟩

theorem card_ordinarySums_taggedUnion (A : Finset α) (B : Finset β) (q : ℕ) :
    (ordinarySums (taggedUnion A B) q).card =
      ∑ p ∈ range (q+1), (ordinarySums A p).card*(ordinarySums B (q-p)).card := by
  rw [ordinarySums_taggedUnion,Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro p _
    rw [Finset.card_image_of_injective]
    · exact Finset.card_product _ _
    · intro ⟨a,b⟩ ⟨a',b'⟩ he
      simp only [Prod.mk.injEq] at he
      exact Prod.ext he.1.2 he.2.2
  · intro p _ r _ hpr
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨⟨a,b⟩,_,hx⟩ := Finset.mem_image.mp hx
    obtain ⟨⟨a',b'⟩,_,hy⟩ := Finset.mem_image.mp hy
    have hh := congrArg (fun x : (ℕ×α)×(ℕ×β) => x.1.1) (hx.trans hy.symm)
    exact hpr hh

end
end SumsetRanges
