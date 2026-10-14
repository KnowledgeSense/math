import BoseBurton.ZIncidence

noncomputable section
namespace MatroidInverseZ
open Finset Polynomial IncidenceAlgebra
variable {α β : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α] [DecidableLE α]
  [PartialOrder β] [LocallyFiniteOrder β] [DecidableEq β] [DecidableLE β]

theorem zKernel_interval_transport (f : α ↪o β)
    (hI : ∀ a b y,f a≤y→y≤f b→∃ x,f x=y)
    (r : α→ℕ) (s : β→ℕ) (hr : ∀ a b,s (f b)-s (f a)=r b-r a) (a b : α) :
    zKernel s (f a) (f b)=zKernel r a b := by
  rw [zKernel_apply,zKernel_apply,← map_Icc_interval f hI a b,sum_map]
  simp only [RelEmbedding.coe_toEmbedding]
  apply sum_congr rfl
  intro x _
  rw [hr a x,kl_interval_transport f hI r s hr x b]

end MatroidInverseZ
