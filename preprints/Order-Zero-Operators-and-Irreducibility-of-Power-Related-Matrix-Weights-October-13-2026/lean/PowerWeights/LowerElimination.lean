import PowerWeights.PrintedBoundary

namespace PowerWeights

 theorem printed_boundary_zero {N : ℕ} (a : ℕ → ℝ)
    (ha : ∀ i, i+1<N → a i≠0) (F : Matrix (Fin N) (Fin N) ℂ)
    (h : constant F * polynomialWeight N .printed a =
      polynomialWeight N .printed a * adjoint (constant F))
    (i j : Fin N) (hi : i.val=1) (hj : j.val=2) : F i j=0 := by
  have hN : 2<N := by have := j.isLt; omega
  have hz := printed_boundary_entry hN a (ha 0 (by omega)) F h
  convert hz using 1
  congr 1 <;> apply Fin.ext <;> omega

 theorem lower_row_unique {N : ℕ} (s : Schedule) (a : ℕ → ℝ)
    (ha : ∀ i, i+1<N → a i≠0) (F : Matrix (Fin N) (Fin N) ℂ)
    (h : constant F * polynomialWeight N s a =
      polynomialWeight N s a * adjoint (constant F))
    (i j t : Fin N) (hi : i.val%2=1) (hj : j.val%2=0) (ht : t.val%2=0)
    (hf : F i j≠0) (hg : F i t≠0) : j=t := by
  have hs₁ := lower_entry_support s a F h i j hi hj hf
  have hs₂ := lower_entry_support s a F h i t hi ht hg
  rcases hs₁ with hs₁ | ⟨hs,hi₁,hj₀⟩
  · rcases hs₂ with hs₂ | ⟨hs,hi₁,ht₀⟩
    · apply Fin.ext; omega
    · subst s
      exact False.elim (hf (printed_boundary_zero a ha F h i j hi₁ (by omega)))
  · rcases hs₂ with hs₂ | ⟨_,_,ht₀⟩
    · subst s
      exact False.elim (hg (printed_boundary_zero a ha F h i t hi₁ (by omega)))
    · apply Fin.ext; omega

 theorem lower_block_zero {N : ℕ} (s : Schedule) (a : ℕ → ℝ)
    (ha : ∀ i, i+1<N → a i≠0) (F : Matrix (Fin N) (Fin N) ℂ)
    (h : constant F * polynomialWeight N s a =
      polynomialWeight N s a * adjoint (constant F))
    (i j : Fin N) (hi : i.val%2=1) (hj : j.val%2=0) : F i j=0 := by
  by_contra hf
  have hs := lower_entry_support s a F h i j hi hj hf
  have haji : pathMatrix N a j i ≠ 0 := by
    rcases hs with hs | ⟨_,hi₁,hj₀⟩
    · have hne : i.val ≠ j.val+1 := by omega
      have hh : (a i.val : ℂ) ≠ 0 := by
        exact_mod_cast ha i.val (by have := j.isLt; omega)
      unfold pathMatrix
      rw [ite_eq_right (by omega), ite_eq_left ⟨hj,hs⟩]
      exact hh
    · have hh : (a j.val : ℂ) ≠ 0 := by
        exact_mod_cast ha j.val (by have := i.isLt; omega)
      simpa [pathMatrix,hj₀,hi₁] using hh
  have hsum : (F*pathMatrix N a) i i = F i j*pathMatrix N a j i := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_single j
    · intro t _ ht
      by_cases hft : F i t=0
      · simp [hft]
      by_cases hat : pathMatrix N a t i=0
      · simp [hat]
      have htpar := (path_support hat).1
      have he := lower_row_unique s a ha F h i j t hi hj htpar hf hft
      exact False.elim (ht he.symm)
    · simp
  have hz := lower_times_path_zero s a ha F h i i hi
  rw [hsum] at hz
  exact haji ((mul_eq_zero.mp hz).resolve_left hf)

end PowerWeights
