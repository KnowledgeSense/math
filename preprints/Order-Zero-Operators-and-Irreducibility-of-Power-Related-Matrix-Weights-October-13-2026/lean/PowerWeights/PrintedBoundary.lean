import PowerWeights.PathInjectivity

namespace PowerWeights

open Polynomial

 theorem transformed_linear {N : ℕ} (s : Schedule) (a : ℕ → ℝ)
    (F : Matrix (Fin N) (Fin N) ℂ)
    (h : constant F * polynomialWeight N s a =
      polynomialWeight N s a * adjoint (constant F)) (i j : Fin N) :
    transformed a F i j = C (F i j) +
      C ((F*pathMatrix N a-pathMatrix N a*F) i j)*X := by
  rw [transformed_entry, path_sandwich_zero s a F h]
  simp [quadratic]

/-- The repeated initial exponent in the printed convention needs one extra
coefficient comparison, valid whenever the third vertex exists. -/
theorem printed_boundary_entry {N : ℕ} (hN : 2<N) (a : ℕ → ℝ)
    (ha : a 0 ≠ 0) (F : Matrix (Fin N) (Fin N) ℂ)
    (h : constant F * polynomialWeight N .printed a =
      polynomialWeight N .printed a * adjoint (constant F)) :
    F ⟨1,by omega⟩ ⟨2,hN⟩ = 0 := by
  let i₀ : Fin N := ⟨0,by omega⟩
  let i₁ : Fin N := ⟨1,by omega⟩
  let i₂ : Fin N := ⟨2,hN⟩
  have he := transformed_entry_relation .printed a F h i₂ i₀
  rw [transformed_linear .printed a F h, transformed_linear .printed a F h] at he
  have hc := congrArg (fun p : ℂ[X] => p.coeff 2) he
  have hd : (F*pathMatrix N a-pathMatrix N a*F) i₀ i₂ = 0 := by
    apply (starRingEnd ℂ).injective
    simpa [i₀,i₂,exponent,conjugate,Polynomial.coeff_map,
      coeff_mul_X_pow', coeff_C_mul_X] using hc.symm
  have hF := mul_path_even_column a F i₀ i₂ (by simp [i₂])
  have hAF : (pathMatrix N a*F) i₀ i₂=0 := by
    simpa [Matrix.sub_apply,hF] using hd
  have hs : (pathMatrix N a*F) i₀ i₂ = (a 0 : ℂ)*F i₁ i₂ := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i₁]
    · simp [pathMatrix,i₀,i₁]
    · intro t _ ht
      have hz : pathMatrix N a i₀ t=0 := by
        by_contra hn
        have hp := path_support hn
        have he : t=i₁ := by apply Fin.ext; dsimp [i₀,i₁] at *; omega
        exact ht he
      simp [hz]
    · simp
  rw [hs] at hAF
  have hane : (a 0 : ℂ) ≠ 0 := by exact_mod_cast ha
  exact (mul_eq_zero.mp hAF).resolve_left hane

end PowerWeights
