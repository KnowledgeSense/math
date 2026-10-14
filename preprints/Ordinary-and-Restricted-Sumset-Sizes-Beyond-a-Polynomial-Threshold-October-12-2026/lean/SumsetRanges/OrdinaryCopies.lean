import SumsetRanges.OrdinarySeparated
import SumsetRanges.OrdinaryDenseSets
import SumsetRanges.FreeAtoms
import SumsetRanges.SeriesAgreement

open Finset
namespace SumsetRanges
section
variable {α : Type*} [AddCommMonoid α] [DecidableEq α]

theorem ordinarySeries_empty_generic : ordinarySeries (∅ : Finset α)=1 := by
  apply PowerSeries.ext
  intro q
  cases q with
  | zero => simp [ordinarySeries,ordinarySums]
  | succ q => simp [ordinarySeries,ordinarySums]

theorem ordinarySeries_image_injective {β : Type*} [AddCommMonoid β] [DecidableEq β]
    (A : Finset α) (φ : α →+ β) (hφ : Function.Injective φ) :
    ordinarySeries (A.image φ)=ordinarySeries A := by
  apply PowerSeries.ext
  intro q
  rw [coeff_ordinarySeries,coeff_ordinarySeries,ordinarySums_image,
    Finset.card_image_of_injective _ hφ]

theorem ordinarySeries_independentCopies (A : Finset α) (δ : α →+ ℤ)
    (hδ : ∀a∈A,δ a=1) (r : ℕ) :
    ordinarySeries (independentCopies A r)=(ordinarySeries A)^r := by
  induction r with
  | zero => simp [independentCopies,ordinarySeries_empty_generic]
  | succ r ih =>
      rw [independentCopies,ordinarySeries_image_injective _ _ (prependHom_injective r),
        ordinarySeries_separatedUnion A (independentCopies A r) δ hδ,ih,pow_succ']

theorem ordinarySeries_singleton (a : α) : ordinarySeries {a}=geometricSeries := by
  apply PowerSeries.ext
  intro q
  rw [coeff_ordinarySeries,ordinarySums_singleton]
  simp [geometricSeries]

end

theorem ordinarySeries_freeAtoms (n : ℕ) : ordinarySeries (freeAtoms n)=geometricSeries^n := by
  rw [freeAtoms,ordinarySeries_independentCopies {1} (AddMonoidHom.id ℤ) (by simp),ordinarySeries_singleton]

end SumsetRanges
