import SumsetRanges.OrdinarySetOperations
import Mathlib.Data.Nat.ModEq

open Finset
namespace SumsetRanges

def carryLength (m a : ℕ) : ℕ := a/m+a%m

@[simp] theorem carryLength_zero (m : ℕ) : carryLength m 0=0 := by simp [carryLength]

theorem carryLength_add_le (m a b : ℕ) (hm : 1≤m) :
    carryLength m (a+b)≤carryLength m a+carryLength m b := by
  by_cases hr : a%m+b%m<m
  · simp only [carryLength,Nat.add_div_eq_of_add_mod_lt hr,Nat.add_mod_of_add_mod_lt hr]
    omega
  · have hmod := Nat.add_mod_add_of_le_add_mod (by omega : m≤a%m+b%m)
    have hdiv := Nat.add_div_eq_of_le_mod_add_mod (by omega : m≤a%m+b%m) (by omega : 0<m)
    unfold carryLength
    rw [hdiv]
    omega

def carryWeight {r : ℕ} (m : ℕ) (v : Fin r→ℕ) : ℕ := ∑i,carryLength m (v i)

@[simp] theorem carryWeight_zero (m r : ℕ) : carryWeight m (0 : Fin r→ℕ)=0 := by
  simp [carryWeight]

theorem carryWeight_add_le (m r : ℕ) (hm : 1≤m) (v w : Fin r→ℕ) :
    carryWeight m (v+w)≤carryWeight m v+carryWeight m w := by
  unfold carryWeight
  rw [←Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => carryLength_add_le m (v i) (w i) hm)

theorem carryWeight_sum_le {ι : Type*} (s : Finset ι) (m r : ℕ) (hm : 1≤m)
    (v : ι→Fin r→ℕ) : carryWeight m (∑i∈s,v i)≤∑i∈s,carryWeight m (v i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha,Finset.sum_insert ha]
      exact (carryWeight_add_le m r hm _ _).trans (Nat.add_le_add_left ih _)

theorem nsmul_mem_ordinarySums {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) {a : α} (ha : a∈A) (q : ℕ) : q • a∈ordinarySums A q := by
  exact (mem_ordinarySums _ _ _).mpr ⟨fun _ => a,fun _ => ha,by simp⟩

theorem weighted_sum_mem_ordinarySums {ι α : Type*} [AddCommMonoid α] [DecidableEq α]
    (s : Finset ι) (A : Finset α) (v : ι→α) (w : ι→ℕ) (hv : ∀i∈s,v i∈A) :
    (∑i∈s,w i • v i)∈ordinarySums A (∑i∈s,w i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [ordinarySums]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha,Finset.sum_insert ha,ordinarySums_add]
      exact Finset.mem_add.mpr ⟨w a • v a,nsmul_mem_ordinarySums A (hv a (Finset.mem_insert_self _ _)) _,
        _,ih (fun i hi => hv i (Finset.mem_insert_of_mem hi)),rfl⟩

end SumsetRanges
