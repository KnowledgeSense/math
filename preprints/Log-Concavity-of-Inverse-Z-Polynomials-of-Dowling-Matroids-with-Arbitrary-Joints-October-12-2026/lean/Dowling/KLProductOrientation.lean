import Dowling.ZDependentProduct

noncomputable section
namespace Dowling
open MatroidInverseZ
open scoped Classical

abbrev intervalP {α : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]
    [DecidableLE α] (r : α → ℕ) (a b : α) := kl r b a

theorem intervalP_diag {α : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]
    [DecidableLE α] (r : α → ℕ) (a : α) : intervalP r a a=1 := kl_self r a

theorem intervalP_transport {α β : Type*} [PartialOrder α] [PartialOrder β]
    [LocallyFiniteOrder α] [LocallyFiniteOrder β] [DecidableEq α] [DecidableEq β]
    [DecidableLE α] [DecidableLE β] (f : α ↪o β)
    (hI : ∀ a b y, f a≤y → y≤f b → ∃ x, f x=y)
    (r : α → ℕ) (s : β → ℕ) (hr : ∀ a b, s (f b)-s (f a)=r b-r a) (a b : α) :
    intervalP s (f a) (f b)=intervalP r a b := kl_interval_transport f hI r s hr a b

theorem intervalP_product {α β : Type*} [PartialOrder α] [PartialOrder β]
    [LocallyFiniteOrder α] [LocallyFiniteOrder β] [DecidableEq α] [DecidableEq β]
    [DecidableLE α] [DecidableLE β] (r : α → ℕ) (s : β → ℕ)
    (hr : Monotone r) (hs : Monotone s) (a b : α×β) (hab : a≤b) :
    intervalP (fun x => r x.1+s x.2) a b=intervalP r a.1 b.1*intervalP s a.2 b.2 :=
  kl_product r s hr hs a b hab

end Dowling
