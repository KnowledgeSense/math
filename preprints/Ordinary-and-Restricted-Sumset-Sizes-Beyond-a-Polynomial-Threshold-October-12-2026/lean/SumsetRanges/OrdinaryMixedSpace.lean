import SumsetRanges.OrdinaryCopies
import Mathlib.Algebra.BigOperators.Finsupp.Fin

open Finset
namespace SumsetRanges

abbrev OrdinarySpace (ι τ : Type*) := (ι→ℕ) × (τ→ℤ)

def mixedJoinHom (ι κ τ σ : Type*) : OrdinarySpace ι τ × OrdinarySpace κ σ →+
    OrdinarySpace (ι⊕κ) (τ⊕σ) where
  toFun a := (Sum.elim a.1.1 a.2.1,Sum.elim a.1.2 a.2.2)
  map_zero' := by apply Prod.ext <;> funext i <;> cases i <;> rfl
  map_add' a b := by apply Prod.ext <;> funext i <;> cases i <;> rfl

theorem mixedJoinHom_injective (ι κ τ σ : Type*) : Function.Injective (mixedJoinHom ι κ τ σ) := by
  intro a b he
  apply Prod.ext <;> apply Prod.ext
  · funext i; exact congrFun (congrArg Prod.fst he) (Sum.inl i)
  · funext i; exact congrFun (congrArg Prod.snd he) (Sum.inl i)
  · funext i; exact congrFun (congrArg Prod.fst he) (Sum.inr i)
  · funext i; exact congrFun (congrArg Prod.snd he) (Sum.inr i)

noncomputable def mixedJoin {ι κ τ σ : Type*} [Fintype ι] [Fintype κ] [Fintype τ] [Fintype σ]
    (A : Finset (OrdinarySpace ι τ)) (B : Finset (OrdinarySpace κ σ)) :
    Finset (OrdinarySpace (ι⊕κ) (τ⊕σ)) := by
  classical
  exact (separatedUnion A B).image (mixedJoinHom ι κ τ σ)

def mixedDegree (ι τ : Type*) [Fintype τ] : OrdinarySpace ι τ →+ ℤ where
  toFun a := ∑t,a.2 t
  map_zero' := by simp
  map_add' a b := by simp [Finset.sum_add_distrib]

def MixedBound {ι τ : Type*} [Fintype ι] [Fintype τ] (H : ℕ) (a : OrdinarySpace ι τ) : Prop :=
  (∑i,a.1 i)≤H ∧ (∀t,a.2 t=0 ∨ a.2 t=1) ∧ mixedDegree ι τ a=1

theorem mixedJoin_bound {ι κ τ σ : Type*} [Fintype ι] [Fintype κ] [Fintype τ] [Fintype σ]
    (A : Finset (OrdinarySpace ι τ)) (B : Finset (OrdinarySpace κ σ)) (H : ℕ)
    (hA : ∀a∈A,MixedBound H a) (hB : ∀b∈B,MixedBound H b) :
    ∀a∈mixedJoin A B,MixedBound H a := by
  classical
  intro a ha
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
  rcases (mem_separatedUnion A B p).mp hp with ⟨ha,hz⟩ | ⟨hz,hb⟩
  · obtain ⟨hn,ht,hd⟩ := hA p.1 ha
    rcases p with ⟨a,b⟩
    dsimp at hz
    subst b
    refine ⟨?_,?_,?_⟩
    · simpa [mixedJoinHom,Fintype.sum_sum_type] using hn
    · intro t; cases t with
      | inl t => exact ht t
      | inr t => exact Or.inl rfl
    · simpa [mixedDegree,mixedJoinHom,Fintype.sum_sum_type] using hd
  · obtain ⟨hn,ht,hd⟩ := hB p.2 hb
    rcases p with ⟨a,b⟩
    dsimp at hz
    subst a
    refine ⟨?_,?_,?_⟩
    · simpa [mixedJoinHom,Fintype.sum_sum_type] using hn
    · intro t; cases t with
      | inl t => exact Or.inl rfl
      | inr t => exact ht t
    · simpa [mixedDegree,mixedJoinHom,Fintype.sum_sum_type] using hd

theorem card_mixedJoin {ι κ τ σ : Type*} [Fintype ι] [Fintype κ] [Fintype τ] [Fintype σ]
    (A : Finset (OrdinarySpace ι τ)) (B : Finset (OrdinarySpace κ σ))
    (hA : ∀a∈A,mixedDegree ι τ a=1) : (mixedJoin A B).card=A.card+B.card := by
  classical
  rw [mixedJoin,Finset.card_image_of_injective _ (mixedJoinHom_injective _ _ _ _),
    card_separatedUnion A B (mixedDegree ι τ) hA]

theorem ordinarySeries_mixedJoin {ι κ τ σ : Type*} [Fintype ι] [Fintype κ] [Fintype τ] [Fintype σ]
    (A : Finset (OrdinarySpace ι τ)) (B : Finset (OrdinarySpace κ σ))
    (hA : ∀a∈A,mixedDegree ι τ a=1) :
    ordinarySeries (mixedJoin A B)=ordinarySeries A*ordinarySeries B := by
  classical
  rw [mixedJoin,ordinarySeries_image_injective _ _ (mixedJoinHom_injective _ _ _ _),
    ordinarySeries_separatedUnion A B (mixedDegree ι τ) hA]

end SumsetRanges
