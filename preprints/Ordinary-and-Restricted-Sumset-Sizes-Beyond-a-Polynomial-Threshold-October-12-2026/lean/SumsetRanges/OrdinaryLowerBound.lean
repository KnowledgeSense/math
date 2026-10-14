import SumsetRanges.OrdinaryBasics

open Finset
open scoped Pointwise
namespace SumsetRanges

theorem integer_sumset_card_lower (A B : Finset ℤ) (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card+B.card≤(A+B).card+1 := by
  let a := A.max' hA
  let b := B.min' hB
  let X := A.image (fun x => x+b)
  let Y := B.image (fun y => a+y)
  have hcX : X.card=A.card := Finset.card_image_of_injective _ (fun _ _ he => add_right_cancel he)
  have hcY : Y.card=B.card := Finset.card_image_of_injective _ (fun _ _ he => add_left_cancel he)
  have hsub : X∪Y⊆A+B := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_add.mpr ⟨x,hx,b,B.min'_mem hB,rfl⟩
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_add.mpr ⟨a,A.max'_mem hA,y,hy,rfl⟩
  have hinter : X∩Y⊆{a+b} := by
    intro z hz
    obtain ⟨hx,hy⟩ := Finset.mem_inter.mp hz
    obtain ⟨x,hx,hxz⟩ := Finset.mem_image.mp hx
    obtain ⟨y,hy,hyz⟩ := Finset.mem_image.mp hy
    have hxa : x≤a := Finset.le_max' A x hx
    have hby : b≤y := Finset.min'_le B y hy
    simp only [Finset.mem_singleton]
    omega
  have hc := Finset.card_le_card hsub
  have hi : (X∩Y).card≤1 := (Finset.card_le_card hinter).trans_eq (Finset.card_singleton _)
  have he := Finset.card_union_add_card_inter X Y
  rw [hcX,hcY] at he
  omega

theorem ordinarySums_nonempty (A : Finset ℤ) (hA : A.Nonempty) (h : ℕ) :
    (ordinarySums A h).Nonempty := by
  obtain ⟨a,ha⟩ := hA
  exact ⟨∑_i : Fin h,a,(mem_ordinarySums A h _).mpr ⟨fun _ => a,fun _ => ha,rfl⟩⟩

theorem card_ordinarySums_lower (A : Finset ℤ) (hA : A.Nonempty) (h : ℕ) :
    h*A.card+1≤(ordinarySums A h).card+h := by
  induction h with
  | zero => simp [ordinarySums]
  | succ h ih =>
    have he := integer_sumset_card_lower A (ordinarySums A h) hA (ordinarySums_nonempty A hA h)
    change (h+1)*A.card+1≤(A+ordinarySums A h).card+(h+1)
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem ordinaryMinimum_le_card (A : Finset ℤ) (hA : A.Nonempty) (h : ℕ) :
    ordinaryMinimum h A.card≤(ordinarySums A h).card := by
  have he := card_ordinarySums_lower A hA h
  have hk : 1≤A.card := Finset.card_pos.mpr hA
  have hh : h≤h*A.card := Nat.le_mul_of_pos_right h hk
  unfold ordinaryMinimum
  omega

end SumsetRanges
