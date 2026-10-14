import MainTheorems.Chollet.GramExpansion

open scoped ComplexOrder MatrixOrder

namespace ResearchMain.Chollet

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem positiveSemidefinite_permanent_nonneg {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    0 ≤ A.permanent.re := by
  have hPSD : (CFC.sqrt A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hQ : (CFC.sqrt A).conjTranspose = CFC.sqrt A := hPSD.isHermitian
  have hg : CFC.sqrt A * (CFC.sqrt A).conjTranspose = A := by
    rw [hQ, ← sq, CFC.sq_sqrt A hA.nonneg]
  have h := permanent_gram_nonneg (CFC.sqrt A)
  rwa [hg] at h

theorem permanent_diagonal_congruence (A : Matrix I I ℂ) (d : I → ℂ) :
    Matrix.permanent ((fun i j => d i * A i j * d j) : Matrix I I ℂ) =
      (∏ i, d i) ^ 2 * A.permanent := by
  unfold Matrix.permanent
  simp only [Finset.prod_mul_distrib]
  have hd : ∀ σ : Equiv.Perm I, (∏ i, d (σ i)) = ∏ i, d i :=
    fun σ => Fintype.prod_equiv σ _ _ (fun _ => rfl)
  simp only [hd]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  ring

end ResearchMain.Chollet
