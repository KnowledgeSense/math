import MainTheorems.Chollet.Basic

namespace ResearchMain.Chollet

section Semiring

variable {I J R : Type*} [Fintype I] [Fintype J] [DecidableEq I] [CommSemiring R]

theorem permanent_mul_expand (Q : Matrix I J R) (T : Matrix J I R) :
    (Q * T).permanent = ∑ f : I → J, (Q.submatrix id f).permanent * ∏ i, T (f i) i := by
  calc
    _ = ∑ σ : Equiv.Perm I, ∑ f : I → J, (∏ i, Q (σ i) (f i)) * ∏ i, T (f i) i := by
      simp only [Matrix.permanent, Matrix.mul_apply, Fintype.prod_sum, Finset.prod_mul_distrib]
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Matrix.permanent, Matrix.submatrix_apply, id_eq, Finset.sum_mul]

def permuteFunctions (π : Equiv.Perm I) : (I → J) ≃ (I → J) where
  toFun f i := f (π i)
  invFun f i := f (π.symm i)
  left_inv f := by funext i; simp
  right_inv f := by funext i; simp

theorem permanent_mul_assignment (Q : Matrix I J R) (T : Matrix J I R) (π : Equiv.Perm I) :
    (∑ f : I → J, (Q.submatrix id f).permanent * ∏ i, T (f i) (π i)) = (Q * T).permanent := by
  rw [permanent_mul_expand]
  symm
  apply Fintype.sum_equiv (permuteFunctions π)
  intro f
  have hp : (Q.submatrix id (permuteFunctions π f)).permanent = (Q.submatrix id f).permanent := by
    exact Matrix.permanent_permute_rows π (Q.submatrix id f)
  have ht : (∏ i, T (permuteFunctions π f i) (π i)) = ∏ i, T (f i) i :=
    Fintype.prod_equiv π _ _ (fun _ => rfl)
  rw [hp, ht]

theorem permanent_mul_symmetrized (Q : Matrix I J R) (T : Matrix J I R) :
    (∑ f : I → J, (Q.submatrix id f).permanent * (T.submatrix f id).permanent) =
      (Fintype.card (Equiv.Perm I) : R) * (Q * T).permanent := by
  simp only [Matrix.permanent, Matrix.submatrix_apply, id_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  change (∑ π : Equiv.Perm I, ∑ f : I → J,
    (Q.submatrix id f).permanent * ∏ i, T (f (π i)) i) = _
  have h : ∀ π : Equiv.Perm I, (∑ f : I → J,
      (Q.submatrix id f).permanent * ∏ i, T (f (π i)) i) = (Q * T).permanent := by
    intro π
    have he : ∀ f : I → J, (∏ i, T (f (π i)) i) = ∏ i, T (f i) (π.symm i) := by
      intro f
      apply Fintype.prod_equiv π
      intro i
      simp
    simp only [he]
    exact permanent_mul_assignment Q T π.symm
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [Matrix.permanent, Finset.mul_sum]

end Semiring

section Complex

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]

theorem permanent_gram_identity (Q : Matrix I J ℂ) :
    (Fintype.card (Equiv.Perm I) : ℝ) * (Q * Q.conjTranspose).permanent.re =
      ∑ f : I → J, ‖(Q.submatrix id f).permanent‖ ^ 2 := by
  have h := permanent_mul_symmetrized Q Q.conjTranspose
  have hc : ∀ f : I → J, (Q.conjTranspose.submatrix f id).permanent = star (Q.submatrix id f).permanent := by
    intro f
    change (conjugate (Q.submatrix id f)).transpose.permanent = _
    rw [Matrix.permanent_transpose, permanent_conjugate]
  simp only [hc, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  have hr := congrArg Complex.re h
  simpa [← Complex.ofReal_pow] using hr.symm

theorem permanent_gram_nonneg (Q : Matrix I J ℂ) : 0 ≤ (Q * Q.conjTranspose).permanent.re := by
  have hc : (0 : ℝ) < Fintype.card (Equiv.Perm I) := by exact_mod_cast Fintype.card_pos
  have hs : (0 : ℝ) ≤ ∑ f : I → J, ‖(Q.submatrix id f).permanent‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [← permanent_gram_identity] at hs
  exact nonneg_of_mul_nonneg_right hs hc

end Complex

end ResearchMain.Chollet
