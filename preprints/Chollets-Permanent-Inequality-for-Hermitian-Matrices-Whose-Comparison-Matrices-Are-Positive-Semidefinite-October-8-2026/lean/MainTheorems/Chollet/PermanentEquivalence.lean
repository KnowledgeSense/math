import MainTheorems.Chollet.GramExpansion

namespace ResearchMain.Chollet

variable {I J R : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [CommSemiring R]

theorem permanent_reindex (e : I ≃ J) (A : Matrix J J R) :
    (A.submatrix e e).permanent = A.permanent := by
  classical
  unfold Matrix.permanent
  apply Fintype.sum_equiv e.permCongr
  intro π
  apply Fintype.prod_equiv e
  intro i
  simp [Equiv.permCongr]

omit [Fintype J] [DecidableEq J] in
theorem permanent_congruence (A : Matrix I I R) (d : I → R) :
    Matrix.permanent ((fun i j => d i * A i j * d j) : Matrix I I R) =
      (∏ i, d i) ^ 2 * A.permanent := by
  unfold Matrix.permanent
  simp only [Finset.prod_mul_distrib]
  have hd : ∀ σ : Equiv.Perm I, (∏ i, d (σ i)) = ∏ i, d i :=
    fun σ => Fintype.prod_equiv σ _ _ (fun _ => rfl)
  simp only [hd]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

end ResearchMain.Chollet
