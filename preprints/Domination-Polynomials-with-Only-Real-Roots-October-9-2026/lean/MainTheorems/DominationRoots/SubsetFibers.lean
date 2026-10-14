import MainTheorems.DominationRoots.StarClassification

namespace ResearchMain.DominationRoots

open Classical Polynomial

variable {ι : Type} [Fintype ι]
variable {W : ι → Type} [∀ i, Fintype (W i)]

noncomputable def subsetFiber (R : Finset (Σ i, W i)) (i : ι) : Finset (W i) :=
  Finset.univ.filter (fun w => ⟨i, w⟩ ∈ R)

noncomputable def assembleFibers (T : ∀ i, Finset (W i)) : Finset (Σ i, W i) :=
  Finset.univ.sigma T

omit [Fintype ι] in
theorem mem_subsetFiber (R : Finset (Σ i, W i)) (i : ι) (w : W i) :
    w ∈ subsetFiber R i ↔ ⟨i, w⟩ ∈ R := by simp [subsetFiber]

omit [∀ i, Fintype (W i)] in
theorem mem_assembleFibers (T : ∀ i, Finset (W i)) (i : ι) (w : W i) :
    (⟨i, w⟩ : Σ i, W i) ∈ assembleFibers T ↔ w ∈ T i := by simp [assembleFibers]

theorem fiber_assemble (T : ∀ i, Finset (W i)) : subsetFiber (assembleFibers T) = T := by
  funext i
  ext w
  rw [mem_subsetFiber, mem_assembleFibers]

theorem assemble_fiber (R : Finset (Σ i, W i)) : assembleFibers (subsetFiber R) = R := by
  ext p
  rcases p with ⟨i, w⟩
  rw [mem_assembleFibers, mem_subsetFiber]

omit [∀ i, Fintype (W i)] in
theorem assembleFibers_card (T : ∀ i, Finset (W i)) :
    (assembleFibers T).card = ∑ i, (T i).card := by
  exact Finset.card_sigma _ _

noncomputable def subsetFiberEquiv : Finset (Σ i, W i) ≃ (∀ i, Finset (W i)) where
  toFun := subsetFiber
  invFun := assembleFibers
  left_inv := assemble_fiber
  right_inv := fiber_assemble

theorem polynomial_fiber_sum (P : ∀ i, Finset (W i) → Prop) :
    (∑ R : Finset (Σ i, W i), if ∀ i, P i (subsetFiber R i) then (X : ℤ[X]) ^ R.card else 0) =
      ∏ i, (∑ S : Finset (W i), if P i S then (X : ℤ[X]) ^ S.card else 0) := by
  have hterm (T : ∀ i, Finset (W i)) :
      (if ∀ i, P i (subsetFiber (assembleFibers T) i) then
        (X : ℤ[X]) ^ (assembleFibers T).card else 0) =
      ∏ i, if P i (T i) then (X : ℤ[X]) ^ (T i).card else 0 := by
    rw [fiber_assemble, assembleFibers_card]
    by_cases hall : ∀ i, P i (T i)
    · rw [ite_eq_left hall]
      simp_rw [ite_eq_left (hall _)]
      exact (Finset.prod_pow_eq_pow_sum Finset.univ (fun i => (T i).card) X).symm
    · rw [ite_eq_right hall]
      push Not at hall
      obtain ⟨i, hi⟩ := hall
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact ite_eq_right hi
  calc
    _ = ∑ T : ∀ i, Finset (W i), ∏ i, if P i (T i) then (X : ℤ[X]) ^ (T i).card else 0 := by
      apply Fintype.sum_equiv (subsetFiberEquiv (ι := ι) (W := W))
      intro R
      dsimp only [subsetFiberEquiv, Equiv.coe_fn_mk]
      simpa only [assemble_fiber] using hterm (subsetFiber R)
    _ = _ := (Fintype.prod_sum (fun i (S : Finset (W i)) =>
      if P i S then (X : ℤ[X]) ^ S.card else 0)).symm

end ResearchMain.DominationRoots
