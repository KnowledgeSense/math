import SumsetRanges.SeparatedConvolution
import Mathlib.Data.Fin.Tuple.Basic

open Finset Polynomial
namespace SumsetRanges

section
variable {α : Type*} [AddCommMonoid α] [DecidableEq α]

def prependHom (r : ℕ) : (α × (Fin r → α)) →+ (Fin (r+1) → α) where
  toFun x := Fin.cons x.1 x.2
  map_zero' := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  map_add' x y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

omit [DecidableEq α] in
theorem prependHom_injective (r : ℕ) : Function.Injective (prependHom (α := α) r) := by
  intro x y he
  apply Prod.ext
  · exact congrFun he 0
  · funext j
    exact congrFun he j.succ

def independentCopies (A : Finset α) : (r : ℕ) → Finset (Fin r → α)
  | 0 => ∅
  | r+1 => (separatedUnion A (independentCopies A r)).image (prependHom r)

theorem card_independentCopies (A : Finset α) (δ : α →+ ℤ) (hδ : ∀ a∈A,δ a=1)
    (r : ℕ) : (independentCopies A r).card = r*A.card := by
  induction r with
  | zero => simp [independentCopies]
  | succ r ih =>
    rw [independentCopies,Finset.card_image_of_injective _ (prependHom_injective r),
      card_separatedUnion A (independentCopies A r) δ hδ,ih]
    ring

@[simp] theorem restrictedPolynomial_empty : restrictedPolynomial (∅ : Finset α)=1 := by
  simp [restrictedPolynomial,restrictedSums]

theorem restrictedPolynomial_image_injective {β : Type*} [AddCommMonoid β] [DecidableEq β]
    (A : Finset α) (φ : α →+ β) (hφ : Function.Injective φ) :
    restrictedPolynomial (A.image φ) = restrictedPolynomial A := by
  ext q
  rw [coeff_restrictedPolynomial,coeff_restrictedPolynomial,
    card_restrictedSums_image A φ hφ.injOn q hφ.injOn]

theorem restrictedPolynomial_independentCopies (A : Finset α) (δ : α →+ ℤ)
    (hδ : ∀ a∈A,δ a=1) (r : ℕ) :
    restrictedPolynomial (independentCopies A r) = (restrictedPolynomial A)^r := by
  induction r with
  | zero => simp [independentCopies]
  | succ r ih =>
    rw [independentCopies,restrictedPolynomial_image_injective _ _ (prependHom_injective r),
      restrictedPolynomial_separatedUnion A (independentCopies A r) δ hδ,ih,pow_succ']

end
end SumsetRanges
