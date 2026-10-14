import SumsetRanges.LinearBlockSeries
import SumsetRanges.SharedBlockSeries
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Fin

open Finset Polynomial
namespace SumsetRanges

@[simp] theorem mem_separatedUnion {α β : Type*} [AddCommMonoid α] [AddCommMonoid β]
    [DecidableEq α] [DecidableEq β] (A : Finset α) (B : Finset β) (x : α×β) :
    x∈separatedUnion A B ↔ (x.1∈A ∧ x.2=0) ∨ (x.1=0 ∧ x.2∈B) := by
  simp only [separatedUnion,Finset.mem_image,taggedUnion,Finset.mem_map]
  constructor
  · rintro ⟨y,⟨a,ha,rfl⟩,rfl⟩
    rcases a with a | b
    · exact Or.inl ⟨by simpa [eraseTags,taggedPoint] using ha,rfl⟩
    · exact Or.inr ⟨rfl,by simpa [eraseTags,taggedPoint] using ha⟩
  · rintro (⟨ha,hb⟩ | ⟨ha,hb⟩)
    · refine ⟨taggedPoint (Sum.inl x.1),⟨Sum.inl x.1,by simpa [eraseTags,taggedPoint] using ha,rfl⟩,?_⟩
      exact Prod.ext rfl hb.symm
    · refine ⟨taggedPoint (Sum.inr x.2),⟨Sum.inr x.2,by simpa using hb,rfl⟩,?_⟩
      exact Prod.ext ha.symm rfl

def joinCoordinates (ι κ : Type*) : ((ι→ℤ)×(κ→ℤ)) →+ (ι⊕κ→ℤ) where
  toFun v := Sum.elim v.1 v.2
  map_zero' := by ext (i|j) <;> rfl
  map_add' _ _ := by ext (i|j) <;> rfl

theorem joinCoordinates_injective (ι κ : Type*) : Function.Injective (joinCoordinates ι κ) := by
  intro v w he
  apply Prod.ext
  · funext i; exact congrFun he (Sum.inl i)
  · funext j; exact congrFun he (Sum.inr j)

def uncurriedCoordinates (ι κ : Type*) : (ι→κ→ℤ) →+ (ι×κ→ℤ) where
  toFun v p := v p.1 p.2
  map_zero' := rfl
  map_add' _ _ := rfl

theorem uncurriedCoordinates_injective (ι κ : Type*) : Function.Injective (uncurriedCoordinates ι κ) := by
  intro v w he
  funext i j
  exact congrFun he (i,j)

def joinedDegree {ι κ : Type*} (δ : (ι→ℤ) →+ ℤ) (ε : (κ→ℤ) →+ ℤ) :
    (ι⊕κ→ℤ) →+ ℤ where
  toFun v := δ (fun i => v (Sum.inl i))+ε (fun j => v (Sum.inr j))
  map_zero' := by change δ 0+ε 0=0; simp
  map_add' v w := by
    change δ ((fun i => v (Sum.inl i))+(fun i => w (Sum.inl i)))+
      ε ((fun j => v (Sum.inr j))+(fun j => w (Sum.inr j)))=_
    rw [map_add,map_add]
    ring

theorem joinedDegree_points {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Finset (ι→ℤ)) (B : Finset (κ→ℤ))
    (δ : (ι→ℤ) →+ ℤ) (ε : (κ→ℤ) →+ ℤ)
    (hδ : ∀a∈A,δ a=1) (hε : ∀b∈B,ε b=1) :
    ∀v∈(separatedUnion A B).image (joinCoordinates ι κ), joinedDegree δ ε v=1 := by
  classical
  intro v hv
  obtain ⟨⟨a,b⟩,hp,rfl⟩ := Finset.mem_image.mp hv
  rcases (mem_separatedUnion A B (a,b)).mp hp with ⟨ha,rfl⟩ | ⟨rfl,hb⟩
  · change δ a+ε 0=1
    rw [map_zero,add_zero,hδ a ha]
  · change δ 0+ε b=1
    rw [map_zero,zero_add,hε b hb]

def copiedDegree {α : Type*} [AddCommMonoid α] (δ : α →+ ℤ) (r : ℕ) : (Fin r→α) →+ ℤ where
  toFun v := ∑i,δ (v i)
  map_zero' := by simp
  map_add' v w := by simp [Finset.sum_add_distrib]

theorem copiedDegree_points {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) (δ : α →+ ℤ) (hδ : ∀a∈A,δ a=1) (r : ℕ) :
    ∀v∈independentCopies A r,copiedDegree δ r v=1 := by
  induction r with
  | zero => simp [independentCopies]
  | succ r ih =>
      intro v hv
      obtain ⟨⟨a,b⟩,hp,rfl⟩ := Finset.mem_image.mp hv
      rcases (mem_separatedUnion A (independentCopies A r) (a,b)).mp hp with ⟨ha,rfl⟩ | ⟨rfl,hb⟩
      · simpa [copiedDegree,prependHom,Fin.sum_univ_succ] using hδ a ha
      · simpa [copiedDegree,prependHom,Fin.sum_univ_succ] using ih b hb

end SumsetRanges
