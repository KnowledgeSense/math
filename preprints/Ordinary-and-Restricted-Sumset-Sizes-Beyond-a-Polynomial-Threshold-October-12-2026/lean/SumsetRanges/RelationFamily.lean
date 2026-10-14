import SumsetRanges.OrderBlocks

open Finset Polynomial
namespace SumsetRanges

abbrev RelationAtom (r u : ℕ → ℕ) : ℕ → Type
  | 0 => Fin 0
  | n+1 => OrderAtom (n+2) (r (n+2)) (u (n+2)) ⊕ RelationAtom r u n

instance relationAtomFintype (r u : ℕ → ℕ) : (n : ℕ) → Fintype (RelationAtom r u n)
  | 0 => inferInstanceAs (Fintype (Fin 0))
  | n+1 => @instFintypeSum _ _ inferInstance (relationAtomFintype r u n)

def relationBlocks (r u : ℕ → ℕ) : (n : ℕ) → Finset (RelationAtom r u n → ℤ)
  | 0 => ∅
  | n+1 => (separatedUnion (orderBlock (n+2) (r (n+2)) (u (n+2))) (relationBlocks r u n)).image
    (joinCoordinates _ _)

def relationDegree (r u : ℕ → ℕ) : (n : ℕ) → (RelationAtom r u n → ℤ) →+ ℤ
  | 0 => 0
  | n+1 => joinedDegree (orderDegree (n+2) (r (n+2)) (u (n+2))) (relationDegree r u n)

theorem relationDegree_points (r u : ℕ → ℕ) (n : ℕ) :
    ∀v∈relationBlocks r u n,relationDegree r u n v=1 := by
  induction n with
  | zero => simp [relationBlocks]
  | succ n ih => exact joinedDegree_points _ _ _ _ (orderDegree_points _ _ _ (by omega)) ih

theorem card_relationBlocks (r u : ℕ → ℕ) (n : ℕ) :
    (relationBlocks r u n).card=∑j∈range n,(2*(j+2)*r (j+2)+(j+2)*u (j+2)) := by
  induction n with
  | zero => simp [relationBlocks]
  | succ n ih =>
      rw [relationBlocks,Finset.card_image_of_injective _ (joinCoordinates_injective _ _),
        card_separatedUnion _ _ (orderDegree _ _ _) (orderDegree_points _ _ _ (by omega)),
        card_orderBlock _ _ _ (by omega),ih,Finset.sum_range_succ]
      omega

theorem restrictedPolynomial_relationBlocks (r u : ℕ → ℕ) (n : ℕ) :
    restrictedPolynomial (relationBlocks r u n)=∏j∈range n,
      restrictedPolynomial (linearBlocks (j+2) (r (j+2)))*
        restrictedPolynomial (sharedAtomBlock (j+2) (u (j+2))) := by
  induction n with
  | zero => simp [relationBlocks]
  | succ n ih =>
      rw [relationBlocks,restrictedPolynomial_image_injective _ _ (joinCoordinates_injective _ _),
        restrictedPolynomial_separatedUnion _ _ (orderDegree _ _ _) (orderDegree_points _ _ _ (by omega)),
        restrictedPolynomial_orderBlock _ _ _ (by omega),ih,Finset.prod_range_succ]
      ring

theorem relationBlocks_norm (r u : ℕ → ℕ) (n : ℕ) :
    ∀v∈relationBlocks r u n,coordinateNorm v≤2*(n+1)-1 := by
  induction n with
  | zero => simp [relationBlocks]
  | succ n ih =>
      intro v hv
      obtain ⟨⟨a,b⟩,hp,rfl⟩ := Finset.mem_image.mp hv
      rw [coordinateNorm_join]
      rcases (mem_separatedUnion _ _ (a,b)).mp hp with ⟨ha,rfl⟩ | ⟨rfl,hb⟩
      · simpa using orderBlock_norm (n+2) _ _ (by omega) a ha
      · have hb' := ih b hb
        simp only [coordinateNorm_zero,zero_add]
        omega

theorem relationAtom_card_le (r u : ℕ → ℕ) (n : ℕ) (hu : ∀j<n,1≤u (j+2)) :
    Fintype.card (RelationAtom r u n)≤(relationBlocks r u n).card := by
  induction n with
  | zero => simp [RelationAtom,relationBlocks]
  | succ n ih =>
      change Fintype.card (OrderAtom (n+2) (r (n+2)) (u (n+2)) ⊕ RelationAtom r u n)≤_
      rw [Fintype.card_sum,relationBlocks,Finset.card_image_of_injective _ (joinCoordinates_injective _ _),
        card_separatedUnion _ _ (orderDegree _ _ _) (orderDegree_points _ _ _ (by omega)),
        card_orderBlock _ _ _ (by omega)]
      exact Nat.add_le_add (orderAtom_card_le _ _ _ (by omega) (hu n (by omega)))
        (ih (fun j hj => hu j (by omega)))

end SumsetRanges
