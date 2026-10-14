import SumsetRanges.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

open Finset
namespace SumsetRanges

section
variable {α β : Type*} [AddCommMonoid α] [AddCommMonoid β]
  [DecidableEq α] [DecidableEq β]

def taggedPoint : α ⊕ β → (ℕ × α) × (ℕ × β)
  | Sum.inl a => ((1,a),(0,0))
  | Sum.inr b => ((0,0),(1,b))

omit [DecidableEq α] [DecidableEq β] in
theorem taggedPoint_injective : Function.Injective (taggedPoint (α := α) (β := β)) := by
  rintro (a | b) (a' | b') he <;> simp [taggedPoint] at he
  · exact congrArg Sum.inl he
  · exact congrArg Sum.inr he

def taggedUnion (A : Finset α) (B : Finset β) : Finset ((ℕ × α) × (ℕ × β)) :=
  (A.disjSum B).map ⟨taggedPoint,taggedPoint_injective⟩

omit [DecidableEq α] [DecidableEq β] in
@[simp] theorem card_taggedUnion (A : Finset α) (B : Finset β) :
    (taggedUnion A B).card = A.card+B.card := by simp [taggedUnion]

theorem sum_pair {ι A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (s : Finset ι) (f : ι → A) (g : ι → B) :
    (∑ i ∈ s, (f i,g i)) = (∑ i ∈ s,f i, ∑ i ∈ s,g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih => simp [ha,ih]

omit [DecidableEq α] [DecidableEq β] in
theorem sum_taggedPoint (S : Finset (α ⊕ β)) :
    ∑ a ∈ S, taggedPoint a =
      ((S.toLeft.card, ∑ a ∈ S.toLeft, a),(S.toRight.card, ∑ b ∈ S.toRight, b)) := by
  have hl : (∑ a ∈ S.toLeft, ((1:ℕ),a)) = (S.toLeft.card, ∑ a ∈ S.toLeft,a) := by
    simpa using sum_pair S.toLeft (fun _ => (1:ℕ)) (fun a => a)
  have hr : (∑ b ∈ S.toRight, ((1:ℕ),b)) = (S.toRight.card, ∑ b ∈ S.toRight,b) := by
    simpa using sum_pair S.toRight (fun _ => (1:ℕ)) (fun b => b)
  rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight]
  simp only [taggedPoint,
    sum_pair S.toLeft (fun a => ((1:ℕ),a)) (fun _ => ((0:ℕ),(0:β))),
    sum_pair S.toRight (fun _ => ((0:ℕ),(0:α))) (fun b => ((1:ℕ),b)), hl, hr]
  simp

/-- Every restricted tagged sum is determined by a pair of actual component
 sums and the two cardinality tags. -/
theorem restrictedSums_taggedUnion (A : Finset α) (B : Finset β) (q : ℕ) :
    restrictedSums (taggedUnion A B) q = (range (q+1)).biUnion (fun p =>
      ((restrictedSums A p) ×ˢ (restrictedSums B (q-p))).image
        (fun ab => ((p,ab.1),(q-p,ab.2)))) := by
  unfold taggedUnion
  rw [restrictedSums_map]
  ext x
  constructor
  · intro hx
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp hS
    obtain ⟨hA,hB⟩ := Finset.subset_disjSum.mp hsub
    have hs := Finset.card_toLeft_add_card_toRight (u := S)
    refine Finset.mem_biUnion.mpr ⟨S.toLeft.card,mem_range.mpr (by omega),?_⟩
    apply Finset.mem_image.mpr
    refine ⟨(∑ a ∈ S.toLeft,a, ∑ b ∈ S.toRight,b), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      constructor
      · exact mem_restrictedSums.mpr ⟨S.toLeft,hA,rfl,rfl⟩
      · exact mem_restrictedSums.mpr ⟨S.toRight,hB,by omega,rfl⟩
    · change _ = ∑ a ∈ S, taggedPoint a
      rw [sum_taggedPoint]
      congr 2
      omega
  · intro hx
    obtain ⟨p,hp,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    obtain ⟨S,hS,hSc,hSa⟩ := mem_restrictedSums.mp ha
    obtain ⟨T,hT,hTc,hTb⟩ := mem_restrictedSums.mp hb
    apply Finset.mem_image.mpr
    refine ⟨S.disjSum T, Finset.mem_powersetCard.mpr ⟨?_,?_⟩,?_⟩
    · exact Finset.disjSum_mono hS hT
    · rw [Finset.card_disjSum,hSc,hTc]
      have := mem_range.mp hp
      omega
    · change (∑ x ∈ S.disjSum T, taggedPoint x) = _
      rw [sum_taggedPoint]
      simp only [Finset.toLeft_disjSum,Finset.toRight_disjSum,hSc,hTc,hSa,hTb]

/-- Exact convolution of actual restricted-sum cardinalities for a tagged union. -/
theorem card_restrictedSums_taggedUnion (A : Finset α) (B : Finset β) (q : ℕ) :
    (restrictedSums (taggedUnion A B) q).card =
      ∑ p ∈ range (q+1), (restrictedSums A p).card*(restrictedSums B (q-p)).card := by
  rw [restrictedSums_taggedUnion,Finset.card_biUnion]
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
