import PowerWeights.Definitions

namespace PowerWeights

 theorem path_support {N : ℕ} {a : ℕ → ℝ} {i j : Fin N}
    (h : pathMatrix N a i j ≠ 0) :
    i.val % 2 = 0 ∧ j.val % 2 = 1 ∧
      (j.val = i.val+1 ∨ i.val = j.val+1) := by
  unfold pathMatrix at h
  split_ifs at h with h₁ h₂
  · obtain ⟨hi, hj⟩ := h₁
    exact ⟨hi, by omega, Or.inl hj⟩
  · obtain ⟨hi, hj⟩ := h₂
    exact ⟨hi, by omega, Or.inr hj⟩
  · exact False.elim (h rfl)

 theorem path_square_zero (N : ℕ) (a : ℕ → ℝ) :
    pathMatrix N a * pathMatrix N a = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro t _
  by_cases h₁ : pathMatrix N a i t = 0
  · simp [h₁]
  · have h₂ : pathMatrix N a t j = 0 := by
      by_contra h₂
      have hs₁ := path_support h₁
      have hs₂ := path_support h₂
      omega
    simp [h₂]

end PowerWeights
