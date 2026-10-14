import SumsetRanges.BlockNorms

open Finset Polynomial
namespace SumsetRanges

abbrev OrderAtom (m r u : ℕ) := (Fin r × LinearAtom m) ⊕ SharedAtom m u

def curriedCoordinates (ι κ : Type*) : (ι×κ→ℤ) →+ (ι→κ→ℤ) where
  toFun v i j := v (i,j)
  map_zero' := rfl
  map_add' _ _ := rfl

def flatLinearBlocks (m r : ℕ) : Finset (Fin r×LinearAtom m→ℤ) :=
  (linearBlocks m r).image (uncurriedCoordinates (Fin r) (LinearAtom m))

def flatLinearDegree (m r : ℕ) : (Fin r×LinearAtom m→ℤ) →+ ℤ :=
  (copiedDegree (linearDegree m) r).comp (curriedCoordinates (Fin r) (LinearAtom m))

theorem flatLinearDegree_points (m r : ℕ) (hm : 2≤m) :
    ∀v∈flatLinearBlocks m r,flatLinearDegree m r v=1 := by
  intro v hv
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
  exact copiedDegree_points (linearBlock m) (linearDegree m) (linearDegree_block m (by omega)) r w hw

theorem flatLinearBlocks_norm (m r : ℕ) (hm : 2≤m) :
    ∀v∈flatLinearBlocks m r,coordinateNorm v≤2*m-1 := by
  intro v hv
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
  rw [coordinateNorm_uncurried]
  exact copied_size_bound (linearBlock m) coordinateNorm coordinateNorm_zero (2*m-1) r
    (linearBlock_norm m (by omega)) w hw

def orderBlock (m r u : ℕ) : Finset (OrderAtom m r u→ℤ) :=
  (separatedUnion (flatLinearBlocks m r) (sharedAtomBlock m u)).image
    (joinCoordinates (Fin r×LinearAtom m) (SharedAtom m u))

def orderDegree (m r u : ℕ) : (OrderAtom m r u→ℤ) →+ ℤ :=
  joinedDegree (flatLinearDegree m r) (sharedDegreeHom m u)

theorem orderDegree_points (m r u : ℕ) (hm : 2≤m) :
    ∀v∈orderBlock m r u,orderDegree m r u v=1 :=
  joinedDegree_points _ _ _ _ (flatLinearDegree_points m r hm) (sharedDegreeHom_points m u hm)

theorem card_orderBlock (m r u : ℕ) (hm : 2≤m) :
    (orderBlock m r u).card=2*m*r+m*u := by
  rw [orderBlock,Finset.card_image_of_injective _ (joinCoordinates_injective _ _),
    card_separatedUnion _ _ (flatLinearDegree m r) (flatLinearDegree_points m r hm),
    flatLinearBlocks,Finset.card_image_of_injective _ (uncurriedCoordinates_injective _ _),
    card_linearBlocks m r hm,card_sharedAtomBlock m u hm]

theorem restrictedPolynomial_orderBlock (m r u : ℕ) (hm : 2≤m) :
    restrictedPolynomial (orderBlock m r u)=
      restrictedPolynomial (linearBlocks m r)*restrictedPolynomial (sharedAtomBlock m u) := by
  rw [orderBlock,restrictedPolynomial_image_injective _ _ (joinCoordinates_injective _ _),
    restrictedPolynomial_separatedUnion _ _ (flatLinearDegree m r) (flatLinearDegree_points m r hm),
    flatLinearBlocks,restrictedPolynomial_image_injective _ _ (uncurriedCoordinates_injective _ _)]

theorem orderBlock_norm (m r u : ℕ) (hm : 2≤m) :
    ∀v∈orderBlock m r u,coordinateNorm v≤2*m-1 := by
  intro v hv
  obtain ⟨⟨a,b⟩,hp,rfl⟩ := Finset.mem_image.mp hv
  rw [coordinateNorm_join]
  rcases (mem_separatedUnion _ _ (a,b)).mp hp with ⟨ha,rfl⟩ | ⟨rfl,hb⟩
  · simpa using flatLinearBlocks_norm m r hm a ha
  · have hb' := sharedAtomBlock_norm m u (by omega) b hb
    simp only [coordinateNorm_zero,zero_add]
    omega

theorem orderAtom_card_le (m r u : ℕ) (hm : 2≤m) (hu : 1≤u) :
    Fintype.card (OrderAtom m r u)≤2*m*r+m*u := by
  simp only [OrderAtom,LinearAtom,SharedAtom,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_option,Fintype.card_fin]
  have he : m-1+1=m := by omega
  nlinarith

end SumsetRanges
