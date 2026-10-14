import SumsetRanges.OrdinaryBasics
import SumsetRanges.RestrictedIntervals

open Finset
open scoped Pointwise
namespace SumsetRanges

theorem zero_mem_ordinarySums {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) (h0 : 0∈A) (q : ℕ) : 0∈ordinarySums A q := by
  exact (mem_ordinarySums _ _ _).mpr ⟨fun _ => 0,fun _ => h0,by simp⟩

theorem ordinarySums_order_mono {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) (h0 : 0∈A) (p q : ℕ) (hpq : p≤q) : ordinarySums A p⊆ordinarySums A q := by
  induction q, hpq using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ q _ ih =>
      intro x hx
      exact Finset.mem_add.mpr ⟨0,h0,x,ih hx,zero_add x⟩

theorem ordinarySums_translate {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) (a : α) (q : ℕ) :
    ordinarySums (A.image (fun x => a+x)) q=(ordinarySums A q).image (fun x => q • a+x) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨v,hv,rfl⟩ := (mem_ordinarySums _ _ _).mp hx
    have hex (i : Fin q) : ∃b∈A,a+b=v i := Finset.mem_image.mp (hv i)
    let w (i : Fin q) := Classical.choose (hex i)
    have hw (i : Fin q) : w i∈A ∧ a+w i=v i := Classical.choose_spec (hex i)
    refine Finset.mem_image.mpr ⟨∑i,w i,(mem_ordinarySums _ _ _).mpr ⟨w,fun i => (hw i).1,rfl⟩,?_⟩
    calc
      _ = ∑i : Fin q,(a+w i) := by simp [Finset.sum_add_distrib]
      _ = _ := Finset.sum_congr rfl (fun i _ => (hw i).2)
  · intro hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := (mem_ordinarySums _ _ _).mp hy
    refine (mem_ordinarySums _ _ _).mpr ⟨fun i => a+v i,?_,?_⟩
    · intro i
      exact Finset.mem_image.mpr ⟨v i,hv i,rfl⟩
    · simp [Finset.sum_add_distrib]

theorem ordinarySums_int_bounds (A : Finset ℤ) (a b : ℤ)
    (hA : ∀x∈A,a≤x ∧ x≤b) (q : ℕ) {x : ℤ} (hx : x∈ordinarySums A q) :
    (q:ℤ)*a≤x ∧ x≤(q:ℤ)*b := by
  obtain ⟨v,hv,rfl⟩ := (mem_ordinarySums _ _ _).mp hx
  have h1 := Finset.sum_le_sum (s:=univ) (fun i _ => (hA _ (hv i)).1)
  have h2 := Finset.sum_le_sum (s:=univ) (fun i _ => (hA _ (hv i)).2)
  simpa using And.intro h1 h2

end SumsetRanges
