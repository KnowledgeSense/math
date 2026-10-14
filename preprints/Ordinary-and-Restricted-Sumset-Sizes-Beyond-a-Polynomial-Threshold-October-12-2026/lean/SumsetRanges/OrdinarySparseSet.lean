import SumsetRanges.OrdinaryRelationFamily
import SumsetRanges.SparseSet

open Finset
namespace SumsetRanges

noncomputable def ordinaryNonfreeSize (h : ℕ) (r u : ℕ → ℕ) : ℕ :=
  ∑m∈Icc 2 (h-1),(2*r m+1+2*u m)

noncomputable def ordinarySparseSeries (h c : ℕ) (r u : ℕ → ℕ) : PowerSeries ℤ :=
  geometricSeries^(c-ordinaryNonfreeSize h r u)*
    ∏m∈Icc 2 (h-1),ordinarySeries (carryG (m+1) (r m))*ordinarySeries (carryH m (u m))

def naturalFreeAtoms (n : ℕ) := independentCopies ({1} : Finset ℕ) n

def naturalDegree : ℕ →+ ℤ := Nat.castAddMonoidHom ℤ

theorem card_naturalFreeAtoms (n : ℕ) : (naturalFreeAtoms n).card=n := by
  rw [naturalFreeAtoms,card_independentCopies {1} naturalDegree (by simp [naturalDegree])]
  simp

theorem naturalFreeAtoms_mass (n : ℕ) : ∀v∈naturalFreeAtoms n,(∑i,v i)≤1 :=
  copied_size_bound {1} id rfl 1 n (by simp)

theorem ordinarySeries_naturalFreeAtoms (n : ℕ) : ordinarySeries (naturalFreeAtoms n)=geometricSeries^n := by
  rw [naturalFreeAtoms,ordinarySeries_independentCopies {1} naturalDegree (by simp [naturalDegree]),ordinarySeries_singleton]

theorem card_ordinaryRelationBlocks_nonfree (h : ℕ) (r u : ℕ → ℕ) (hh : 2≤h) :
    (ordinaryRelationBlocks r u (h-2)).card=ordinaryNonfreeSize h r u := by
  rw [card_ordinaryRelationBlocks,sum_range_shift_two (fun j => 2*r j+1+2*u j)]
  have he : h-2+1=h-1 := by omega
  rw [he]
  rfl

abbrev OrdinarySparseAtom (h c : ℕ) (r u : ℕ → ℕ) :=
  Fin (c-ordinaryNonfreeSize h r u) ⊕ OrdinaryRelationAtom r u (h-2)
abbrev OrdinarySparseTag (h : ℕ) := Fin 1 ⊕ OrdinaryRelationTag (h-2)

noncomputable def ordinarySparseSet (h c : ℕ) (r u : ℕ → ℕ) :
    Finset (OrdinarySpace (OrdinarySparseAtom h c r u) (OrdinarySparseTag h)) :=
  mixedJoin (mixedLift (naturalFreeAtoms (c-ordinaryNonfreeSize h r u))) (ordinaryRelationBlocks r u (h-2))

theorem ordinarySparseSet_bound (h c : ℕ) (r u : ℕ → ℕ) (hh : 2≤h) :
    ∀a∈ordinarySparseSet h c r u,MixedBound h a := by
  apply mixedJoin_bound
  · intro a ha
    exact (mixedLift_bound _ _ (naturalFreeAtoms_mass _) a ha).mono (by omega)
  · have he : h-2+2=h := by omega
    simpa only [he] using ordinaryRelationBlocks_bound r u (h-2)

theorem card_ordinarySparseSet (h c : ℕ) (r u : ℕ → ℕ) (hh : 2≤h)
    (hc : ordinaryNonfreeSize h r u≤c) : (ordinarySparseSet h c r u).card=c := by
  rw [ordinarySparseSet,card_mixedJoin _ _ (mixedLift_degree _),card_mixedLift,card_naturalFreeAtoms,
    card_ordinaryRelationBlocks_nonfree h r u hh,Nat.sub_add_cancel hc]

theorem ordinarySeries_sparseSet (h c : ℕ) (r u : ℕ → ℕ) (hh : 2≤h) :
    ordinarySeries (ordinarySparseSet h c r u)=ordinarySparseSeries h c r u := by
  rw [ordinarySparseSet,ordinarySeries_mixedJoin _ _ (mixedLift_degree _),ordinarySeries_mixedLift,
    ordinarySeries_naturalFreeAtoms,ordinarySeries_relationBlocks,
    prod_range_shift_two (fun j => ordinarySeries (carryG (j+1) (r j))*ordinarySeries (carryH j (u j)))]
  have he : h-2+1=h-1 := by omega
  rw [he]
  rfl

theorem ordinarySparseAtom_card (h c : ℕ) (r u : ℕ → ℕ) (hh : 2≤h)
    (hc : ordinaryNonfreeSize h r u≤c) : Fintype.card (OrdinarySparseAtom h c r u)≤c := by
  change Fintype.card (Fin (c-ordinaryNonfreeSize h r u) ⊕ OrdinaryRelationAtom r u (h-2))≤c
  rw [Fintype.card_sum,Fintype.card_fin]
  have ha := ordinaryRelationAtom_card r u (h-2)
  rw [card_ordinaryRelationBlocks_nonfree h r u hh] at ha
  omega

theorem ordinarySparseTag_card (h : ℕ) (hh : 2≤h) : Fintype.card (OrdinarySparseTag h)=2*h-3 := by
  change Fintype.card (Fin 1 ⊕ OrdinaryRelationTag (h-2))=_
  rw [Fintype.card_sum,Fintype.card_fin,ordinaryRelationTag_card]
  omega

end SumsetRanges
