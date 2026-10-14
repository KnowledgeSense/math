import MainTheorems.Chollet.RankCoefficients.PermanentCoefficient

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

variable {I : Type*} [Fintype I] [instI : DecidableEq I]

theorem sum_bijective_functions {R : Type*} [AddCommMonoid R] (F : (I → I) → R) :
    (∑ f : I → I, if Function.Bijective f then F f else 0) =
      ∑ e : Equiv.Perm I, F e := by
  classical
  let : DecidableEq I := instI
  rw [← Finset.sum_filter]
  apply Finset.sum_bij
    (fun f hf => Equiv.ofBijective f (Finset.mem_filter.mp hf).2)
  · intro f hf
    exact Finset.mem_univ _
  · intro f hf g hg hfg
    exact congrArg (fun e : Equiv.Perm I => (e : I → I)) hfg
  · intro e _
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.bijective⟩,
      Equiv.ext (fun _ => rfl)⟩
  · intro f _
    rfl

theorem rowVariable_prod (f : I → I) :
    (∏ i, rowVariable (f i)) =
      if Function.Bijective f then monomial (Finset.univ : Finset I) else 0 := by
  classical
  let : DecidableEq I := instI
  by_cases hf : Function.Bijective f
  · rw [ite_eq_left hf]
    let e : Equiv.Perm I := Equiv.ofBijective f hf
    unfold monomial
    exact Fintype.prod_equiv e _ _ (fun _ => rfl)
  · rw [ite_eq_right hf]
    have hi : ¬ Function.Injective f := by
      intro hi
      exact hf ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hi, rfl⟩)
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hi
    rw [← Finset.mul_prod_erase Finset.univ (fun k => rowVariable (f k)) (Finset.mem_univ i)]
    have hj : j ∈ (Finset.univ : Finset I).erase i :=
      Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩
    rw [← Finset.mul_prod_erase (Finset.univ.erase i) (fun k => rowVariable (f k)) hj,
      ← mul_assoc, hij, variable_mul_self, zero_mul]

theorem quotient_columnProduct (Q : Matrix I I ℂ) :
    Ideal.Quotient.mk (squareIdeal I) (columnProduct Q) =
      scalar Q.permanent * monomial (Finset.univ : Finset I) := by
  classical
  let : DecidableEq I := instI
  have he : Ideal.Quotient.mk (squareIdeal I) (columnProduct Q) =
      ∏ j, ∑ i, scalar (Q i j) * rowVariable i := by
    simp only [columnProduct, map_prod, map_sum, map_mul, scalar, rowVariable]
  rw [he, Fintype.prod_sum]
  have ht : ∀ f : I → I,
      (∏ j, scalar (Q (f j) j) * rowVariable (f j)) =
        if Function.Bijective f then
          scalar (∏ j, Q (f j) j) * monomial (Finset.univ : Finset I) else 0 := by
    intro f
    rw [Finset.prod_mul_distrib, rowVariable_prod, ← scalar_prod]
    split_ifs <;> simp
  simp only [ht]
  rw [sum_bijective_functions, ← Finset.sum_mul, ← scalar_sum]
  rfl

end ResearchMain.Chollet.RankCoefficients

