import SumsetRanges.OrdinaryTaggedConvolution
import Mathlib.RingTheory.PowerSeries.Basic

open Finset PowerSeries
namespace SumsetRanges

noncomputable def ordinarySeries {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) : PowerSeries ℤ :=
  PowerSeries.mk (fun q => ((ordinarySums A q).card : ℤ))

@[simp] theorem coeff_ordinarySeries {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) (q : ℕ) :
    PowerSeries.coeff q (ordinarySeries A) = ((ordinarySums A q).card : ℤ) := by
  simp [ordinarySeries]

theorem ordinarySeries_taggedUnion {α β : Type*} [AddCommMonoid α] [AddCommMonoid β]
    [DecidableEq α] [DecidableEq β] (A : Finset α) (B : Finset β) :
    ordinarySeries (taggedUnion A B) = ordinarySeries A * ordinarySeries B := by
  ext q
  rw [coeff_ordinarySeries,card_ordinarySums_taggedUnion,coeff_mul]
  simp only [coeff_ordinarySeries]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun p r => ((ordinarySums A p).card : ℤ) * ((ordinarySums B r).card : ℤ)) q]
  push_cast
  rfl

end SumsetRanges
