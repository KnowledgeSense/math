import SumsetRanges.Definitions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset
open scoped Pointwise
namespace SumsetRanges

@[simp] theorem mem_ordinarySums {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) (q : ℕ) (x : α) :
    x∈ordinarySums A q ↔ ∃v : Fin q → α, (∀i,v i∈A) ∧ ∑i,v i=x := by
  induction q generalizing x with
  | zero => simp [ordinarySums,eq_comm]
  | succ q ih =>
      rw [ordinarySums,Finset.mem_add]
      constructor
      · rintro ⟨a,ha,b,hb,rfl⟩
        obtain ⟨v,hv,rfl⟩ := (ih b).mp hb
        refine ⟨Fin.cons a v,?_,?_⟩
        · intro i; exact Fin.cases ha hv i
        · simp [Fin.sum_univ_succ]
      · rintro ⟨v,hv,rfl⟩
        refine ⟨v 0,hv 0,∑i : Fin q,v i.succ,?_,?_⟩
        · exact (ih _).mpr ⟨fun i => v i.succ,fun i => hv i.succ,rfl⟩
        · simp [Fin.sum_univ_succ]

theorem ordinarySums_mono {α : Type*} [AddCommMonoid α] [DecidableEq α]
    {A B : Finset α} (hAB : A⊆B) (q : ℕ) : ordinarySums A q⊆ordinarySums B q := by
  intro x hx
  obtain ⟨v,hv,rfl⟩ := (mem_ordinarySums A q x).mp hx
  exact (mem_ordinarySums B q _).mpr ⟨v,fun i => hAB (hv i),rfl⟩

theorem ordinarySums_add {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) (p q : ℕ) : ordinarySums A (p+q)=ordinarySums A p+ordinarySums A q := by
  induction p with
  | zero => rw [Nat.zero_add]; change ordinarySums A q=0+ordinarySums A q; rw [zero_add]
  | succ p ih => simp [Nat.succ_add,ordinarySums,ih,add_assoc]

theorem ordinarySums_nat_bound (A : Finset ℕ) (D q : ℕ) (hA : ∀a∈A,a≤D)
    {x : ℕ} (hx : x∈ordinarySums A q) : x≤q*D := by
  obtain ⟨v,hv,rfl⟩ := (mem_ordinarySums A q x).mp hx
  calc
    _ ≤ ∑_i : Fin q,D := Finset.sum_le_sum (fun i _ => hA _ (hv i))
    _ = q*D := by simp

end SumsetRanges
