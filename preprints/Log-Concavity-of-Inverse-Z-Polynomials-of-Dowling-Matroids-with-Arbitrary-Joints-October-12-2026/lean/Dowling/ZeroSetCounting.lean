import Dowling.ZeroSetPartition
import Mathlib.Data.Finset.Powerset

noncomputable section
namespace Dowling
open Finset
open scoped Classical
variable {n : ℕ}

/-- Literal zero vertex sets of prescribed size containing the deleted joint. -/
def jointZeroSets (i : Fin n) (r : ℕ) : Finset (Finset (Fin n)) :=
  (univ.powersetCard r).filter (i∈·)

theorem jointZeroSets_mem (i : Fin n) (r : ℕ) (Z : Finset (Fin n)) :
    Z∈jointZeroSets i r ↔ Z.card=r ∧ i∈Z := by
  simp [jointZeroSets]

theorem jointZeroSets_card (i : Fin n) (r : ℕ) (hr : 1≤r) :
    (jointZeroSets i r).card=(n-1).choose (r-1) := by
  have h := card_filter_powersetCard_subset ({i} : Finset (Fin n)) univ r
    (subset_univ _) (by simpa using hr)
  simpa [jointZeroSets] using h

/-- The trivial gain group needs a second retained mark in the zero block. -/
def markedJointZeroSets (X : Set (Fin n)) (i : Fin n) (r : ℕ) : Finset (Finset (Fin n)) :=
  (jointZeroSets i r).filter (fun Z => ∃ j∈X, j≠i ∧ j∈Z)

theorem markedJointZeroSets_mem (X : Set (Fin n)) (i : Fin n) (r : ℕ)
    (Z : Finset (Fin n)) :
    Z∈markedJointZeroSets X i r ↔ Z.card=r ∧ i∈Z ∧ ∃ j∈X, j≠i ∧ j∈Z := by
  simp only [markedJointZeroSets,mem_filter,jointZeroSets_mem,and_assoc]

theorem jointZeroSets_unmarked (X : Set (Fin n)) (i : Fin n) (r : ℕ) :
    (jointZeroSets i r).filter (fun Z => ¬∃ j∈X, j≠i ∧ j∈Z)=
      ((insert i (univ\X.toFinset)).powersetCard r).filter (i∈·) := by
  ext Z
  simp only [mem_filter,jointZeroSets_mem,mem_powersetCard]
  constructor
  · rintro ⟨⟨hcard,hi⟩,hno⟩
    refine ⟨⟨?_,hcard⟩,hi⟩
    intro j hj
    by_cases hji : j=i
    · exact mem_insert.mpr (Or.inl hji)
    · exact mem_insert.mpr (Or.inr (mem_sdiff.mpr ⟨mem_univ _,by
        intro hjX
        exact hno ⟨j,Set.mem_toFinset.mp hjX,hji,hj⟩⟩))
  · rintro ⟨⟨hsub,hcard⟩,hi⟩
    refine ⟨⟨hcard,hi⟩,?_⟩
    rintro ⟨j,hjX,hji,hj⟩
    rcases mem_insert.mp (hsub hj) with h | h
    · exact hji h
    · exact (mem_sdiff.mp h).2 (Set.mem_toFinset.mpr hjX)

theorem jointZeroSets_unmarked_card (X : Set (Fin n)) (i : Fin n) (hiX : i∈X)
    (r : ℕ) (hr : 1≤r) :
    ((jointZeroSets i r).filter (fun Z => ¬∃ j∈X, j≠i ∧ j∈Z)).card=
      (n-X.toFinset.card).choose (r-1) := by
  rw [jointZeroSets_unmarked]
  have hc : (insert i (univ\X.toFinset)).card=n-X.toFinset.card+1 := by
    rw [card_insert_of_notMem (by simp [hiX]),card_sdiff_of_subset (subset_univ _)]
    simp
  have h := card_filter_powersetCard_subset ({i} : Finset (Fin n))
    (insert i (univ\X.toFinset)) r (by simp) (by simpa using hr)
  simpa only [singleton_subset_iff,card_singleton,hc,Nat.add_sub_cancel] using h

theorem markedJointZeroSets_card (X : Set (Fin n)) (i : Fin n) (hiX : i∈X)
    (r : ℕ) (hr : 1≤r) :
    (markedJointZeroSets X i r).card=
      (n-1).choose (r-1)-(n-X.toFinset.card).choose (r-1) := by
  have h := card_filter_add_card_filter_not (s := jointZeroSets i r)
    (fun Z : Finset (Fin n) => ∃ j∈X, j≠i ∧ j∈Z)
  rw [jointZeroSets_card i r hr,jointZeroSets_unmarked_card X i hiX r hr] at h
  change ((jointZeroSets i r).filter _).card=_
  omega

end Dowling
