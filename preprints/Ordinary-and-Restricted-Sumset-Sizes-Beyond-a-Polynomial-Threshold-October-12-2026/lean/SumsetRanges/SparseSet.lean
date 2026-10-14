import SumsetRanges.RelationFamily
import SumsetRanges.FreeAtoms
import SumsetRanges.SparseParameters
import Mathlib.Algebra.BigOperators.Intervals

open Finset Polynomial
namespace SumsetRanges

theorem prod_range_shift_two {α : Type*} [CommMonoid α] (f : ℕ → α) (n : ℕ) :
    (∏j∈range n,f (j+2))=∏j∈Icc 2 (n+1),f j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ,Finset.prod_Icc_succ_top (by omega),ih]

theorem sum_range_shift_two {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    (∑j∈range n,f (j+2))=∑j∈Icc 2 (n+1),f j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ,Finset.sum_Icc_succ_top (by omega),ih]

theorem card_relationBlocks_nonfree (h : ℕ) (r u : ℕ → ℕ) (hh : 1≤h) :
    (relationBlocks r u (h-1)).card=nonfreeSize h r u := by
  rw [card_relationBlocks,sum_range_shift_two (fun j => 2*j*r j+j*u j) (h-1)]
  simp [nonfreeSize,Nat.sub_add_cancel hh]

abbrev SparseAtom (h c : ℕ) (r u : ℕ → ℕ) := Fin (c-nonfreeSize h r u) ⊕ RelationAtom r u (h-1)

noncomputable def sparseSet (h c : ℕ) (r u : ℕ → ℕ) : Finset (SparseAtom h c r u→ℤ) :=
  (separatedUnion (freeAtoms (c-nonfreeSize h r u)) (relationBlocks r u (h-1))).image
    (joinCoordinates _ _)

noncomputable def sparseDegree (h c : ℕ) (r u : ℕ → ℕ) : (SparseAtom h c r u→ℤ) →+ ℤ :=
  joinedDegree (freeDegree (c-nonfreeSize h r u)) (relationDegree r u (h-1))

theorem sparseDegree_points (h c : ℕ) (r u : ℕ → ℕ) :
    ∀v∈sparseSet h c r u,sparseDegree h c r u v=1 :=
  joinedDegree_points _ _ _ _ (freeDegree_points _) (relationDegree_points _ _ _)

theorem card_sparseSet (h c : ℕ) (r u : ℕ → ℕ) (hh : 1≤h) (hc : nonfreeSize h r u≤c) :
    (sparseSet h c r u).card=c := by
  rw [sparseSet,Finset.card_image_of_injective _ (joinCoordinates_injective _ _),
    card_separatedUnion _ _ (freeDegree _) (freeDegree_points _),card_freeAtoms,
    card_relationBlocks_nonfree h r u hh,Nat.sub_add_cancel hc]

theorem restrictedPolynomial_sparseSet (h c : ℕ) (r u : ℕ → ℕ) (hh : 1≤h) :
    restrictedPolynomial (sparseSet h c r u)=sparsePolynomial h c r u := by
  rw [sparseSet,restrictedPolynomial_image_injective _ _ (joinCoordinates_injective _ _),
    restrictedPolynomial_separatedUnion _ _ (freeDegree _) (freeDegree_points _),
    restrictedPolynomial_freeAtoms,restrictedPolynomial_relationBlocks,
    prod_range_shift_two (fun j => restrictedPolynomial (linearBlocks j (r j))*
      restrictedPolynomial (sharedAtomBlock j (u j))) (h-1),
    Nat.sub_add_cancel hh]
  unfold sparsePolynomial
  apply congrArg (fun P : Polynomial ℤ => (1+X)^(c-nonfreeSize h r u)*P)
  apply Finset.prod_congr rfl
  intro m hm
  rw [sharedBlockPolynomial_eq_restricted m (u m) (Finset.mem_Icc.mp hm).1]

theorem sparseSet_norm (h c : ℕ) (r u : ℕ → ℕ) (hh : 1≤h) :
    ∀v∈sparseSet h c r u,coordinateNorm v≤2*h-1 := by
  intro v hv
  obtain ⟨⟨a,b⟩,hp,rfl⟩ := Finset.mem_image.mp hv
  rw [coordinateNorm_join]
  rcases (mem_separatedUnion _ _ (a,b)).mp hp with ⟨ha,rfl⟩ | ⟨rfl,hb⟩
  · have hb' := freeAtoms_norm _ a ha
    simp only [coordinateNorm_zero,add_zero]
    omega
  · have hb' := relationBlocks_norm r u (h-1) b hb
    simp only [coordinateNorm_zero,zero_add]
    simpa [Nat.sub_add_cancel hh] using hb'

theorem sparseAtom_card_le (h c : ℕ) (r u : ℕ → ℕ) (hh : 1≤h)
    (hc : nonfreeSize h r u≤c) (hu : ∀m∈Icc 2 h,1≤u m) :
    Fintype.card (SparseAtom h c r u)≤c := by
  rw [Fintype.card_sum,Fintype.card_fin]
  have hi := relationAtom_card_le r u (h-1) (fun j hj => hu (j+2) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩))
  rw [card_relationBlocks_nonfree h r u hh] at hi
  omega

end SumsetRanges
