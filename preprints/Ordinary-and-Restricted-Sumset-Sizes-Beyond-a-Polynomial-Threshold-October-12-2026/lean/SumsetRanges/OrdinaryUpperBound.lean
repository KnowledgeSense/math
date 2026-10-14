import SumsetRanges.OrdinaryBasics
import Mathlib.Data.Sym.Card

open Finset
namespace SumsetRanges

theorem card_ordinarySums_le (A : Finset ℤ) (h : ℕ) :
    (ordinarySums A h).card≤(A.card+h-1).choose h := by
  classical
  let f : Sym A h → ℤ := fun s => (s.toMultiset.map Subtype.val).sum
  have hsub : ordinarySums A h⊆Finset.univ.image f := by
    intro x hx
    obtain ⟨v,hv,rfl⟩ := (mem_ordinarySums A h x).mp hx
    let w : Fin h → A := fun i => ⟨v i,hv i⟩
    let s : Sym A h := ⟨Finset.univ.val.map w,by simp⟩
    refine Finset.mem_image.mpr ⟨s,Finset.mem_univ _,?_⟩
    change ((Finset.univ.val.map w).map Subtype.val).sum=∑i,v i
    simp only [Multiset.map_map]
    rfl
  calc
    _ ≤ (Finset.univ.image f).card := Finset.card_le_card hsub
    _ ≤ Fintype.card (Sym A h) := (Finset.card_image_le).trans_eq (Finset.card_univ)
    _ = _ := by rw [Sym.card_sym_eq_choose]; simp

end SumsetRanges
