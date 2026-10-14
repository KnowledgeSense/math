import Dowling.DeletionIncidenceTransition

noncomputable section
namespace Dowling
open Finset LaurentPolynomial
open scoped Classical
variable {α β : Type*} [Fintype α] [Fintype β] [PartialOrder α] [PartialOrder β]
  [LocallyFiniteOrder α] [LocallyFiniteOrder β]

/-- The local deletion matrix, separating rank-preserving and coloop tops. -/
def deletionKLTransition (r : α→ℕ) (s : β→ℕ) (d : α→β) (b : α) (y : β) : DeletionLaurent :=
  if s (d b)=r b then C ((deletionPush r s d (deletionKLVector r b) y).coeff 0)
  else if d b=y then T 1+T (-1) else 0

 theorem deletionKLTransition_intertwiner (r : α→ℕ) (s : β→ℕ) (d : α→β) (c : β→α)
    (hr : Monotone r) (hs : Monotone s)
    (hgc : ∀ x a,c x≤a↔x≤d a) (hcr : ∀ x,r (c x)=s x)
    (hdrop : ∀ a,r a≤s (d a)+1)
    (hcoloop : ∀ b,s (d b)≠r b→∀ x,
      deletionPush r s d (deletionKLVector r b) x=(T 1+T (-1))*deletionKLVector s (d b) x)
    (b : α) :
    deletionPush r s d (deletionKLVector r b)=deletionKLCombination s (deletionKLTransition r s d b) := by
  funext x
  by_cases hb : s (d b)=r b
  · rw [deletionKL_push_expansion r s d c hr hs hgc hcr hdrop b hb x]
    unfold deletionKLCombination
    apply sum_congr rfl
    intro y hy
    rw [deletionKLTransition,ite_eq_left hb,mul_comm]
  · rw [hcoloop b hb x]
    simp only [deletionKLCombination,deletionKLTransition,hb,ite_false,mul_ite,mul_zero]
    rw [sum_eq_single (d b)]
    · simp [mul_comm]
    · intro y hy hyb
      simp [Ne.symm hyb]
    · simp

 omit [Fintype β] [PartialOrder α] [PartialOrder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β] in
 theorem deletion_two_fiber_sum {R : Type*} [AddCommMonoid R] (d : α→β)
    (x : β) (a e : α) (hae : a≠e) (hf : ∀ b,d b=x↔b=a∨b=e) (f : α→R) :
    (∑ b,if d b=x then f b else 0)=f a+f e := by
  rw [← sum_filter]
  have hs : univ.filter (fun b=>d b=x)={a,e} := by
    ext b
    simp [hf]
  rw [hs,sum_pair hae]

end Dowling
