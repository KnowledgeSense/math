import MainTheorems.PreorderGamma.GammaProperties

namespace ResearchMain.PreorderGamma

open scoped BigOperators Classical

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

omit [DecidableEq E] in
theorem supportPolynomial_orderDual :
    supportPolynomial (E := E) = supportPolynomial (E := OrderDual E) := by
  rw [supportPolynomial_eq_preorderEnumerator, supportPolynomial_eq_preorderEnumerator]
  exact supportEnumerator_transpose (fun a b : E => b ≤ a)

omit [Fintype E] [DecidableEq E] in
theorem isMatchedPair_orderDual_swap (I J : Finset E) :
    @IsMatchedPair (OrderDual E) (OrderDual.instPreorder E) J I ↔
      IsMatchedPair (E := E) I J := by
  change (Disjoint J I ∧ ∃ f : J ≃ I, ∀ a : J, (f a).val ≤ a.val) ↔
    (Disjoint I J ∧ ∃ f : I ≃ J, ∀ a : I, a.val ≤ (f a).val)
  constructor
  · rintro ⟨hd, f, hf⟩
    refine ⟨hd.symm, f.symm, ?_⟩
    intro a
    have h := hf (f.symm a)
    have he : (f (f.symm a)).val = a.val :=
      congrArg (fun x : I => x.val) (f.apply_symm_apply a)
    rw [he] at h
    exact h
  · rintro ⟨hd, f, hf⟩
    refine ⟨hd.symm, f.symm, ?_⟩
    intro b
    have h := hf (f.symm b)
    have he : (f (f.symm b)).val = b.val :=
      congrArg (fun x : J => x.val) (f.apply_symm_apply b)
    rw [he] at h
    exact h

noncomputable def matchedPairsOrderDualEquiv (k : ℕ) :
    (matchedPairs (E := E) k) ≃ (matchedPairs (E := OrderDual E) k) where
  toFun p := ⟨p.val.swap, by
    obtain ⟨hI, hJ, hm⟩ := (mem_matchedPairs (E := E)).mp p.property
    exact (mem_matchedPairs (E := OrderDual E)).mpr
      ⟨hJ, hI, (isMatchedPair_orderDual_swap (E := E) p.val.1 p.val.2).mpr hm⟩⟩
  invFun p := ⟨p.val.swap, by
    obtain ⟨hI, hJ, hm⟩ := (mem_matchedPairs (E := OrderDual E)).mp p.property
    exact (mem_matchedPairs (E := E)).mpr
      ⟨hJ, hI, (isMatchedPair_orderDual_swap (E := E) p.val.2 p.val.1).mp hm⟩⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by apply Subtype.ext; rfl

omit [DecidableEq E] in
theorem gammaCoefficient_orderDual (k : ℕ) :
    gammaCoefficient (E := E) k = gammaCoefficient (E := OrderDual E) k := by
  unfold gammaCoefficient
  simpa only [Fintype.card_coe] using Fintype.card_congr (matchedPairsOrderDualEquiv k)

end ResearchMain.PreorderGamma
