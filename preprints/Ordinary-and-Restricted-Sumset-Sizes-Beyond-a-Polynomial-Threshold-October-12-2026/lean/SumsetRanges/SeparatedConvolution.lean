import SumsetRanges.FreimanImages

open Finset Polynomial
namespace SumsetRanges

@[simp] theorem restrictedSums_one {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) : restrictedSums A 1=A := by
  simp [restrictedSums,Finset.powersetCard_one,Finset.map_eq_image,Finset.image_image,Function.comp_def]

section
variable {α β : Type*} [AddCommMonoid α] [AddCommMonoid β]
  [DecidableEq α] [DecidableEq β]

def eraseTags : ((ℕ×α)×(ℕ×β)) →+ (α×β) where
  toFun x := (x.1.2,x.2.2)
  map_zero' := rfl
  map_add' _ _ := rfl

def separatedUnion (A : Finset α) (B : Finset β) : Finset (α×β) :=
  (taggedUnion A B).image eraseTags

theorem eraseTags_injOn_restrictedSums (A : Finset α) (B : Finset β)
    (δ : α →+ ℤ) (hδ : ∀ a∈A,δ a=1) (q : ℕ) :
    Set.InjOn (eraseTags (α := α) (β := β)) (restrictedSums (taggedUnion A B) q) := by
  intro x hx y hy he
  rw [restrictedSums_taggedUnion] at hx hy
  obtain ⟨p,_,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨r,_,hy⟩ := Finset.mem_biUnion.mp hy
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨⟨a',b'⟩,hab',rfl⟩ := Finset.mem_image.mp hy
  have haa : a=a' := congrArg Prod.fst he
  have hbb : b=b' := congrArg Prod.snd he
  have hp := degree_one_restricted_sum A δ hδ p a (Finset.mem_product.mp hab).1
  have hr := degree_one_restricted_sum A δ hδ r a' (Finset.mem_product.mp hab').1
  have hpr : p=r := by rw [haa] at hp; omega
  subst r; subst a'; subst b'
  rfl

theorem eraseTags_injOn_taggedUnion (A : Finset α) (B : Finset β)
    (δ : α →+ ℤ) (hδ : ∀ a∈A,δ a=1) :
    Set.InjOn (eraseTags (α := α) (β := β)) (taggedUnion A B) := by
  simpa using eraseTags_injOn_restrictedSums A B δ hδ 1

theorem card_separatedUnion (A : Finset α) (B : Finset β)
    (δ : α →+ ℤ) (hδ : ∀ a∈A,δ a=1) :
    (separatedUnion A B).card=A.card+B.card := by
  rw [separatedUnion,Finset.card_image_of_injOn (eraseTags_injOn_taggedUnion A B δ hδ),
    card_taggedUnion]

theorem restrictedPolynomial_separatedUnion (A : Finset α) (B : Finset β)
    (δ : α →+ ℤ) (hδ : ∀ a∈A,δ a=1) :
    restrictedPolynomial (separatedUnion A B) = restrictedPolynomial A * restrictedPolynomial B := by
  rw [← restrictedPolynomial_taggedUnion]
  ext q
  rw [coeff_restrictedPolynomial,coeff_restrictedPolynomial]
  congr 1
  exact card_restrictedSums_image (taggedUnion A B) eraseTags
    (eraseTags_injOn_taggedUnion A B δ hδ) q (eraseTags_injOn_restrictedSums A B δ hδ q)

end
end SumsetRanges
