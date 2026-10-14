import SumsetRanges.OrdinarySeries
import SumsetRanges.SeparatedConvolution

open Finset
namespace SumsetRanges

section
variable {α β : Type*} [AddCommMonoid α] [AddCommMonoid β]
  [DecidableEq α] [DecidableEq β]

theorem degree_one_ordinary_sum (A : Finset α) (δ : α →+ ℤ)
    (hδ : ∀a∈A,δ a=1) (q : ℕ) (x : α) (hx : x∈ordinarySums A q) : δ x=q := by
  obtain ⟨v,hv,rfl⟩ := (mem_ordinarySums _ _ _).mp hx
  simp [map_sum,fun i => hδ (v i) (hv i)]

theorem eraseTags_injOn_ordinarySums (A : Finset α) (B : Finset β)
    (δ : α →+ ℤ) (hδ : ∀a∈A,δ a=1) (q : ℕ) :
    Set.InjOn (eraseTags (α := α) (β := β)) (ordinarySums (taggedUnion A B) q) := by
  intro x hx y hy he
  rw [ordinarySums_taggedUnion] at hx hy
  obtain ⟨p,_,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨r,_,hy⟩ := Finset.mem_biUnion.mp hy
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨⟨a',b'⟩,hab',rfl⟩ := Finset.mem_image.mp hy
  have haa : a=a' := congrArg Prod.fst he
  have hbb : b=b' := congrArg Prod.snd he
  have hp := degree_one_ordinary_sum A δ hδ p a (Finset.mem_product.mp hab).1
  have hr := degree_one_ordinary_sum A δ hδ r a' (Finset.mem_product.mp hab').1
  have hpr : p=r := by rw [haa] at hp; omega
  subst r; subst a'; subst b'
  rfl

theorem ordinarySeries_separatedUnion (A : Finset α) (B : Finset β)
    (δ : α →+ ℤ) (hδ : ∀a∈A,δ a=1) :
    ordinarySeries (separatedUnion A B)=ordinarySeries A*ordinarySeries B := by
  rw [←ordinarySeries_taggedUnion]
  apply PowerSeries.ext
  intro q
  rw [coeff_ordinarySeries,coeff_ordinarySeries,separatedUnion,ordinarySums_image,
    Finset.card_image_of_injOn (eraseTags_injOn_ordinarySums A B δ hδ q)]

def homogenized (A : Finset α) : Finset (α×ℤ) := A.image (fun a => (a,1))

def homogenizingHom : α →+ α×ℤ where
  toFun a := (a,0)
  map_zero' := rfl
  map_add' _ _ := by simp

def homogenizedDegree : α×ℤ →+ ℤ where
  toFun a := a.2
  map_zero' := rfl
  map_add' _ _ := rfl

theorem homogenized_degree (A : Finset α) : ∀a∈homogenized A,homogenizedDegree a=1 := by
  intro a ha
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp ha
  rfl

omit [AddCommMonoid α] in
theorem card_homogenized (A : Finset α) : (homogenized A).card=A.card :=
  Finset.card_image_of_injective _ (fun _a _b he => congrArg Prod.fst he)

theorem ordinarySums_homogenized (A : Finset α) (q : ℕ) :
    ordinarySums (homogenized A) q=(ordinarySums A q).image (fun a => (a,(q:ℤ))) := by
  simpa [homogenized,homogenizingHom] using ordinarySums_affine_image A homogenizingHom (0,1) q

theorem ordinarySeries_homogenized (A : Finset α) : ordinarySeries (homogenized A)=ordinarySeries A := by
  apply PowerSeries.ext
  intro q
  rw [coeff_ordinarySeries,coeff_ordinarySeries,ordinarySums_homogenized,
    Finset.card_image_of_injective _ (fun _a _b he => congrArg Prod.fst he)]

end
end SumsetRanges
