import ASR312.BalancedAssembly

namespace ASR312

abbrev FirstEmptyBalanced (p n m : ℕ) :=
  {A : AvoidingRectangle (p+(n+1)) (p+m) (p+m) // nonemptyRows (rowPrefix A.val) = p ∧
    ∀ j, A.val ((0 : Fin (n+1)).natAdd p) j = .zero}

noncomputable def firstEmptyBalancedEquiv (p n m : ℕ) :
    FirstEmptyBalanced p n m ≃
      AvoidingRectangle p (p+m) p × ↥((Finset.univ.erase (0 : Fin (n+1))).powersetCard m) := by
  classical
  let forward : FirstEmptyBalanced p n m →
      AvoidingRectangle p (p+m) p × ↥((Finset.univ.erase (0 : Fin (n+1))).powersetCard m) := fun A =>
    ⟨⟨rowPrefix A.val.val,rowPrefix_asr _ A.val.property.1,A.property.1,
      rowPrefix_extendable _ A.val.property.2.2⟩,
      ⟨rowSupport (rowSuffix A.val.val),by
        rw [Finset.mem_powersetCard,Finset.subset_erase]
        refine ⟨⟨Finset.subset_univ _,?_⟩,?_⟩
        · rw [mem_rowSupport]
          rintro ⟨j,hj⟩
          exact hj (A.property.2 j)
        · have hh := rowSlices_nonemptyRows A.val.val
          rw [A.val.property.2.1,A.property.1,← rowSupport_card] at hh
          omega⟩⟩
  let backward : AvoidingRectangle p (p+m) p × ↥((Finset.univ.erase (0 : Fin (n+1))).powersetCard m) →
      FirstEmptyBalanced p n m := fun D => by
    have hc := zeroSumColumns_rowcomplete_card D.1.val D.1.property.1 D.1.property.2.1
    have hs := (Finset.mem_powersetCard.mp D.2.property).2
    have hz := (Finset.subset_erase.mp (Finset.mem_powersetCard.mp D.2.property).1).2
    refine ⟨⟨balancedAssembly D.1.val hc D.2.val hs,
      balancedAssembly_asr _ _ _ _ D.1.property.1 D.1.property.2.1 D.1.property.2.2,
      balancedAssembly_nonemptyRows _ _ _ _ D.1.property.2.1,
      balancedAssembly_extendable _ _ _ _ D.1.property.1 D.1.property.2.1 D.1.property.2.2⟩,?_,?_⟩
    · rw [balancedAssembly_prefix]
      exact D.1.property.2.1
    · exact balancedAssembly_emptyRow _ _ _ _ hz
  refine ⟨forward,backward,?_,?_⟩
  · intro A
    apply Subtype.ext
    apply Subtype.ext
    apply balanced_eq_of_prefix_suffixSupport _ _
      (backward (forward A)).val.property.1 (backward (forward A)).val.property.2.2
      (backward (forward A)).val.property.2.1 (backward (forward A)).property.2
      A.val.property.1 A.val.property.2.2 A.val.property.2.1 A.property.2
    · exact balancedAssembly_prefix _ _ _ _
    · exact balancedAssembly_suffixSupport _ _ _ _
  · intro D
    apply Prod.ext
    · apply Subtype.ext
      exact balancedAssembly_prefix _ _ _ _
    · apply Subtype.ext
      exact balancedAssembly_suffixSupport _ _ _ _

theorem firstEmptyBalanced_card (p n m : ℕ) :
    Nat.card (FirstEmptyBalanced p n m) = S p (p+m) p * n.choose m := by
  classical
  rw [Nat.card_congr (firstEmptyBalancedEquiv p n m),Nat.card_prod]
  simp only [Nat.card_eq_fintype_card,Fintype.card_coe,Finset.card_powersetCard]
  simp [S]

end ASR312
