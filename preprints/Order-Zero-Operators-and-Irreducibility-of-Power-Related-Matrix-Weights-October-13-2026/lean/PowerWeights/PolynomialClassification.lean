import PowerWeights.DiagonalReduction

namespace PowerWeights

variable {N : ℕ} (s : Schedule) (a : ℕ → ℝ)
    (ha : ∀ i, i+1<N → a i≠0) (F : Matrix (Fin N) (Fin N) ℂ)
    (h : constant F * polynomialWeight N s a =
      polynomialWeight N s a * adjoint (constant F))
include ha h

 theorem diagonal_values_at_edge (i j : Fin N) (hn : pathMatrix N a i j≠0) :
    F i i=F j j := by
  have he := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i j)
    (commutes_path s a ha F h)
  conv_lhs at he => rw [diagonal_form s a ha F h]
  conv_rhs at he => rw [diagonal_form s a ha F h]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at he
  apply mul_right_cancel₀ hn
  exact he.trans (mul_comm _ _)

 theorem adjacent_diagonal_values (i j : Fin N) (hj : j.val=i.val+1) :
    F i i=F j j := by
  have hane : (a i.val : ℂ)≠0 := by
    exact_mod_cast ha i.val (by have := j.isLt; omega)
  by_cases hi : i.val%2=0
  · apply diagonal_values_at_edge s a ha F h i j
    simpa [pathMatrix,hi,hj] using hane
  · have hjpar : j.val%2=0 := by omega
    apply Eq.symm
    apply diagonal_values_at_edge s a ha F h j i
    unfold pathMatrix
    rw [ite_eq_right (by omega), ite_eq_left ⟨hjpar,hj⟩]
    exact hane

 theorem all_diagonal_values (hN : 0<N) (i : Fin N) :
    F i i=F ⟨0,hN⟩ ⟨0,hN⟩ := by
  have aux : ∀ n, ∀ hn : n<N, F ⟨n,hn⟩ ⟨n,hn⟩=F ⟨0,hN⟩ ⟨0,hN⟩ := by
    intro n
    induction n with
    | zero => intro hn; rfl
    | succ n ih =>
      intro hn
      let prev : Fin N := ⟨n,by omega⟩
      have he := adjacent_diagonal_values s a ha F h prev ⟨n+1,hn⟩ rfl
      exact he.symm.trans (ih prev.isLt)
  exact aux i.val i.isLt

/-- Every constant symmetric matrix for either actual polynomial weight is a
real scalar, for every positive size and all nonzero real path parameters. -/
theorem polynomial_symmetric_constants (hN : 0<N) :
    ∃ c : ℝ, F=(c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  let i₀ : Fin N := ⟨0,hN⟩
  have hr : ((F i₀ i₀).re : ℂ)=F i₀ i₀ :=
    Complex.conj_eq_iff_re.mp (diagonal_star_fixed s a ha F h i₀)
  refine ⟨(F i₀ i₀).re, ?_⟩
  ext i j
  by_cases hij : i=j
  · subst j
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    exact (all_diagonal_values s a ha F h hN i).trans hr.symm
  · simp [Matrix.smul_apply, hij,
      off_diagonal_zero s a ha F h i j hij]

end PowerWeights
