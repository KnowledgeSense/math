import MainTheorems.Laminar.PersistenceOrder
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Interval.Finset.Fin

namespace ResearchMain.Laminar

open Classical

noncomputable def rowKey {R A : Type*} [LinearOrder A] (next : R → R)
    (rows : R → Finset A) (i : R) (a : A) : (OrderDual ℕ∞) ×ₗ A :=
  toLex (persistence next (fun j x => x ∈ rows j) i a, a)

theorem rowKey_injective {R A : Type*} [LinearOrder A] (next : R → R)
    (rows : R → Finset A) (i : R) : Function.Injective (rowKey next rows i) := by
  intro a b h
  exact congrArg (fun x => (ofLex x).2) h

theorem rowKey_lt_iff {R A : Type*} [LinearOrder A] (next : R → R)
    (rows : R → Finset A) (i : R) (a b : A) :
    rowKey next rows i a < rowKey next rows i b ↔
      precedes next (fun j x => x ∈ rows j) i a b := by
  simp only [rowKey, Prod.Lex.toLex_lt_toLex, precedes]
  rfl

noncomputable def rowKeys {R A : Type*} [LinearOrder A] (next : R → R)
    (rows : R → Finset A) (i : R) : Finset ((OrderDual ℕ∞) ×ₗ A) :=
  (rows i).image (rowKey next rows i)

theorem rowKeys_card {R A : Type*} [LinearOrder A] (next : R → R)
    (rows : R → Finset A) (i : R) : (rowKeys next rows i).card = (rows i).card :=
  Finset.card_image_of_injective _ (rowKey_injective next rows i)

noncomputable def rowOrder {R A : Type*} [LinearOrder A] (next : R → R)
    (rows : R → Finset A) (i : R) (j : Fin (rows i).card) : A :=
  (ofLex ((rowKeys next rows i).orderEmbOfFin (rowKeys_card next rows i) j)).2

theorem rowOrder_mem {R A : Type*} [LinearOrder A] (next : R → R)
    (rows : R → Finset A) (i : R) (j : Fin (rows i).card) : rowOrder next rows i j ∈ rows i := by
  have h := (rowKeys next rows i).orderEmbOfFin_mem (rowKeys_card next rows i) j
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp h
  change (ofLex ((rowKeys next rows i).orderEmbOfFin (rowKeys_card next rows i) j)).2 ∈ rows i
  rw [← heq]
  exact ha

theorem rowKey_rowOrder {R A : Type*} [LinearOrder A] (next : R → R)
    (rows : R → Finset A) (i : R) (j : Fin (rows i).card) :
    rowKey next rows i (rowOrder next rows i j) =
      (rowKeys next rows i).orderEmbOfFin (rowKeys_card next rows i) j := by
  have h := (rowKeys next rows i).orderEmbOfFin_mem (rowKeys_card next rows i) j
  obtain ⟨a, _, heq⟩ := Finset.mem_image.mp h
  unfold rowOrder
  rw [← heq]
  rfl

theorem rowOrder_injective {R A : Type*} [LinearOrder A] (next : R → R)
    (rows : R → Finset A) (i : R) : Function.Injective (rowOrder next rows i) := by
  intro a b h
  have hk := congrArg (rowKey next rows i) h
  rw [rowKey_rowOrder, rowKey_rowOrder] at hk
  exact (rowKeys next rows i).orderEmbOfFin (rowKeys_card next rows i) |>.injective hk

theorem rowOrder_surjective {R A : Type*} [LinearOrder A] (next : R → R)
    (rows : R → Finset A) (i : R) (a : A) (ha : a ∈ rows i) :
    ∃ j, rowOrder next rows i j = a := by
  let x : rowKeys next rows i := ⟨rowKey next rows i a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
  let j := ((rowKeys next rows i).orderIsoOfFin (rowKeys_card next rows i)).symm x
  refine ⟨j, rowKey_injective next rows i ?_⟩
  rw [rowKey_rowOrder]
  exact congrArg Subtype.val
    (((rowKeys next rows i).orderIsoOfFin (rowKeys_card next rows i)).apply_symm_apply x)

theorem rowOrder_precedes_iff {R A : Type*} [LinearOrder A] (next : R → R)
    (rows : R → Finset A) (i : R) (j k : Fin (rows i).card) :
    precedes next (fun l x => x ∈ rows l) i (rowOrder next rows i j) (rowOrder next rows i k) ↔
      j < k := by
  rw [← rowKey_lt_iff, rowKey_rowOrder, rowKey_rowOrder]
  exact (rowKeys next rows i).orderEmbOfFin (rowKeys_card next rows i) |>.lt_iff_lt

theorem position_rowOrder {R A : Type*} [LinearOrder A] (next : R → R)
    (rows : R → Finset A) (i : R) (j : Fin (rows i).card) :
    position next rows i (rowOrder next rows i j) = j.val := by
  rw [← Fin.card_Iio]
  symm
  apply Finset.card_bij (fun k _ => rowOrder next rows i k)
  · intro k hk
    exact Finset.mem_filter.mpr ⟨rowOrder_mem next rows i k,
      (rowOrder_precedes_iff next rows i k j).mpr (Finset.mem_Iio.mp hk)⟩
  · intro a _ b _ hab
    exact rowOrder_injective next rows i hab
  · intro a ha
    obtain ⟨hamem, hapred⟩ := Finset.mem_filter.mp ha
    obtain ⟨k, rfl⟩ := rowOrder_surjective next rows i a hamem
    exact ⟨k, Finset.mem_Iio.mpr ((rowOrder_precedes_iff next rows i k j).mp hapred), rfl⟩

noncomputable def sortedRowEquiv {R A : Type*} [LinearOrder A] (next : R → R)
    (rows : R → Finset A) (i : R) : Fin (rows i).card ≃ rows i :=
  Equiv.ofBijective (fun j => ⟨rowOrder next rows i j, rowOrder_mem next rows i j⟩)
    ⟨fun _ _ h => rowOrder_injective next rows i (congrArg Subtype.val h),
      fun a => by
        obtain ⟨j, hj⟩ := rowOrder_surjective next rows i a.val a.property
        exact ⟨j, Subtype.ext hj⟩⟩

theorem sortedRowEquiv_position {R A : Type*} [LinearOrder A] (next : R → R)
    (rows : R → Finset A) (i : R) (a : rows i) :
    ((sortedRowEquiv next rows i).symm a).val = position next rows i a.val := by
  obtain ⟨j, hj⟩ := (sortedRowEquiv next rows i).surjective a
  rw [← hj, Equiv.symm_apply_apply]
  exact (position_rowOrder next rows i j).symm

end ResearchMain.Laminar
