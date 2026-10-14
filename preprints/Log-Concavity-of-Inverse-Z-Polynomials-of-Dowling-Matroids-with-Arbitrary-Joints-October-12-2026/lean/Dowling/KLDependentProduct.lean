import Dowling.KLFiniteProduct
import Mathlib.Data.Fintype.EquivFin

noncomputable section
namespace Dowling
open MatroidInverseZ Finset
open scoped Classical BigOperators

/-- Genuine KL multiplicativity for any finite family of finite ranked intervals. -/
theorem intervalP_pi {ι : Type*} [Fintype ι] (β : ι → Type*)
    [∀ i, PartialOrder (β i)] [∀ i, Fintype (β i)] [∀ i, LocallyFiniteOrder (β i)]
    [∀ i, DecidableEq (β i)] [∀ i, DecidableLE (β i)]
    (r : ∀ i, β i → ℕ) (hr : ∀ i, Monotone (r i))
    (a b : ∀ i, β i) (hab : a ≤ b) :
    intervalP (fun x => ∑ i, r i (x i)) a b = ∏ i, intervalP (r i) (a i) (b i) := by
  let e := Fintype.equivFin ι
  let f := piReindexOrderIso e β
  have he (x : ∀ i, β i) :
      (∑ j, r (e.symm j) (f x j)) = ∑ i, r i (x i) :=
    e.symm.sum_comp (fun i => r i (x i))
  have ht := intervalP_transport f.toOrderEmbedding
    (fun _ _ y _ _ => ⟨f.symm y,f.apply_symm_apply y⟩)
    (fun x => ∑ i, r i (x i)) (fun x => ∑ j, r (e.symm j) (x j))
    (fun x y => by
      change (∑ j, r (e.symm j) (f y j))-(∑ j, r (e.symm j) (f x j)) = _
      rw [he,he]) a b
  change intervalP (fun x => ∑ j, r (e.symm j) (x j)) (f a) (f b) = _ at ht
  rw [← ht,intervalP_pi_fin (Fintype.card ι) (fun j => β (e.symm j))
    (fun j => r (e.symm j)) (fun j => hr (e.symm j)) (f a) (f b) (f.monotone hab)]
  exact e.symm.prod_comp (fun i => intervalP (r i) (a i) (b i))

end Dowling
