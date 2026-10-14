import Dowling.DeletionIncidenceKernel
import Dowling.DeletionIncidenceMobius
import Dowling.DeletionKLTriangular

noncomputable section
namespace Dowling
open Finset LaurentPolynomial MatroidInverseZ IncidenceAlgebra
open scoped Classical
variable {α β : Type*} [Fintype α] [Fintype β] [PartialOrder α] [PartialOrder β]
  [LocallyFiniteOrder α] [LocallyFiniteOrder β]

def deletionYCoordinate (r : α→ℕ) (t b : α) : DeletionLaurent :=
  deletionLift (2*(r t : ℤ)-r b) (signedInverseZKernel r b t)

 theorem deletionMobiusVector_eq_combination (r : α→ℕ) (hr : Monotone r)
    (t : α) (ht : ∀ a,a≤t) :
    (fun a=>T (r a)*C (mu ℤ a t))=deletionKLCombination r (deletionYCoordinate r t) := by
  funext a
  rw [deletionMobiusVector_expansion r hr a t (ht a)]
  apply sum_subset (subset_univ _)
  intro b hb hnot
  have hab : ¬a≤b := fun h=>hnot (mem_Icc.mpr ⟨h,ht b⟩)
  simp [deletionKLVector,hab]

/-- Inverting the genuine local KL intertwiner transports the inverse-Z coordinates. -/
theorem deletionYCoordinate_transition (r : α→ℕ) (s : β→ℕ)
    (hr : Monotone r) (hs : Monotone s) (d : α→β) (c : β→α)
    (hgc : ∀ b a,c b≤a↔b≤d a) (hdc : ∀ b,d (c b)=b)
    (t : α) (u : β) (ht : ∀ a,a≤t) (hu : ∀ b,b≤u) (hct : c u=t)
    (κ : α→β→DeletionLaurent)
    (hκ : ∀ b,deletionPush r s d (deletionKLVector r b)=deletionKLCombination s (κ b))
    (y : β) :
    deletionYCoordinate s u y=∑ b,κ b y*deletionYCoordinate r t b := by
  apply congrFun (deletionKLCombination_injective s ?_) y
  funext x
  rw [← deletionMobiusVector_eq_combination s hs u hu]
  dsimp only
  rw [← deletionPush_mobius r s d c hgc hdc t u ht hu hct x,
    deletionMobiusVector_eq_combination r hr t ht]
  change deletionPush r s d (fun a=>∑ b,deletionKLVector r b a*deletionYCoordinate r t b) x=_
  rw [deletionPush_sum]
  simp only [deletionPush_mul_right]
  simp_rw [hκ]
  simp only [deletionKLCombination,sum_mul,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro z hz
  apply sum_congr rfl
  intro b hb
  ring

end Dowling
