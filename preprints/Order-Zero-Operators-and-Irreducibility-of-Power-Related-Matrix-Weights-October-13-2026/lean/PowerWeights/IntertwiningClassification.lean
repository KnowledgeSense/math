import PowerWeights.PolynomialClassification

namespace PowerWeights

open Polynomial

@[simp] theorem constant_smul {N : ℕ} (z : ℂ) (F : Matrix (Fin N) (Fin N) ℂ) :
    constant (z • F) = C z • constant F := by
  ext i j n
  simp [constant]

@[simp] theorem adjoint_diagonal (N : ℕ) (s : Schedule) :
    adjoint (diagonal N s) = diagonal N s := by
  apply Matrix.ext
  intro i j
  by_cases hij : i=j
  · subst j; simp [diagonal,adjoint,conjugate,Matrix.diagonal]
  · simp [diagonal,adjoint,conjugate,Matrix.diagonal,hij,Ne.symm hij]

 theorem polynomialWeight_adjoint (N : ℕ) (s : Schedule) (a : ℕ → ℝ) :
    adjoint (polynomialWeight N s a)=polynomialWeight N s a := by
  simp [polynomialWeight,adjoint_mul,mul_assoc]

/-- Pointwise polynomial intertwining already forces both intertwiners to have
scalar left factor. No moment-determinacy hypothesis is involved. -/
theorem polynomial_intertwiner_scalar {N : ℕ} (hN : 0<N) (s : Schedule)
    (a : ℕ → ℝ) (ha : ∀ i, i+1<N → a i≠0)
    (C₀ D : Matrix (Fin N) (Fin N) ℂ)
    (h : constant C₀ * polynomialWeight N s a =
      polynomialWeight N s a * constant D) :
    ∃ c : ℂ, C₀=c • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  let P := polynomialWeight N s a
  have hstar : constant D.conjTranspose * P = P * constant C₀.conjTranspose := by
    have hs := congrArg adjoint h
    simpa [adjoint_mul,polynomialWeight_adjoint,P] using hs.symm
  let U := C₀+D.conjTranspose
  let V := Complex.I • (C₀-D.conjTranspose)
  change constant C₀*P=P*constant D at h
  have hU : constant U * P = P*adjoint (constant U) := by
    rw [adjoint_constant]
    dsimp [U]
    simp only [constant_add,add_mul,Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose,constant_add,mul_add]
    rw [h,hstar]
    abel
  have hV : constant V * P = P*adjoint (constant V) := by
    rw [adjoint_constant]
    dsimp [V]
    simp only [constant_smul,constant_sub,Matrix.smul_mul,sub_mul,
      Matrix.conjTranspose_smul,Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose,Complex.star_def,Complex.conj_I,
      constant_smul,constant_sub,Matrix.mul_smul,mul_sub,map_neg]
    rw [h,hstar]
    simp only [neg_smul,smul_sub]
    abel
  obtain ⟨u,hu⟩ := polynomial_symmetric_constants s a ha U hU hN
  obtain ⟨v,hv⟩ := polynomial_symmetric_constants s a ha V hV hN
  refine ⟨(1/2 : ℂ)*((u : ℂ)-Complex.I*(v : ℂ)), ?_⟩
  have hr : C₀=(1/2 : ℂ) • (U-Complex.I • V) := by
    dsimp [U,V]
    simp only [smul_smul,Complex.I_mul_I,neg_one_smul,sub_neg_eq_add]
    module
  rw [hr,hu,hv,smul_smul,← sub_smul,smul_smul]

end PowerWeights
