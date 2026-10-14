import Fan.ProductInvariants
import BoseBurton.ZIncidenceTransport
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

noncomputable section
namespace MatroidInverseZ
open Finset Polynomial
open scoped Classical BigOperators
variable {α β : Type*} [PartialOrder α] [PartialOrder β]
  [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  [DecidableEq α] [DecidableEq β] [DecidableLE α] [DecidableLE β]

theorem zKernel_product (r : α → ℕ) (s : β → ℕ)
    (hr : Monotone r) (hs : Monotone s) (a b : α × β) (_hab : a ≤ b) :
    zKernel (fun x : α × β => r x.1+s x.2) a b =
      zKernel r a.1 b.1*zKernel s a.2 b.2 := by
  rw [zKernel_apply,zKernel_apply,zKernel_apply,Icc_prod_def,sum_product,sum_mul_sum]
  apply sum_congr rfl
  intro x hx
  apply sum_congr rfl
  intro y hy
  have hax := hr (mem_Icc.mp hx).1
  have hay := hs (mem_Icc.mp hy).1
  have hd : r x+s y-(r a.1+s a.2)=(r x-r a.1)+(s y-s a.2) := by omega
  rw [hd,pow_add,kl_product r s hr hs (x,y) b ⟨(mem_Icc.mp hx).2,(mem_Icc.mp hy).2⟩]
  ring

end MatroidInverseZ

namespace Dowling
open scoped Classical BigOperators

/-- The standard dependent tuple split, with its actual pointwise order. -/
def piFinSuccOrderIso {n : ℕ} (β : Fin (n+1) → Type*) [∀ i, PartialOrder (β i)] :
    (β 0 × ∀ i : Fin n, β i.succ) ≃o (∀ i, β i) where
  toEquiv := Fin.consEquiv β
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      exact ⟨h 0,fun i => h i.succ⟩
    · rintro ⟨h0,ht⟩ i
      induction i using Fin.cases with
      | zero => exact h0
      | succ i => exact ht i

end Dowling
