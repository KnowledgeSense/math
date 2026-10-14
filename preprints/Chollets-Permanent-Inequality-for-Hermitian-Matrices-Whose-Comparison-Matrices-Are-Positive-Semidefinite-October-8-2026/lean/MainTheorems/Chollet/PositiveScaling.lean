import MainTheorems.Chollet.ZMonotonicity

open Matrix

namespace ResearchMain.Chollet

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem z_matrix_positive_solution {M : Matrix I I ℝ} (hM : M.PosSemidef)
    (hZ : ∀ i j, i ≠ j → M i j ≤ 0) (v : I → ℝ)
    (hv : ∀ i, 0 < (M *ᵥ v) i) : ∀ i, 0 < v i := by
  let w : I → ℝ := fun i => min (v i) 0
  let u : I → ℝ := fun i => max (v i) 0
  have hwu : ∀ i, w i + u i = v i := by intro i; simp only [w, u, min_add_max, add_zero]
  have hcross : ∀ i j, 0 ≤ w i * M i j * u j := by
    intro i j
    by_cases he : i = j
    · subst j
      have hz : w i * u i = 0 := by
        dsimp [w, u]
        rcases le_total (v i) 0 with h | h
        · rw [min_eq_left h, max_eq_right h]; simp
        · rw [min_eq_right h, max_eq_left h]; simp
      have he : w i * M i i * u i = M i i * (w i * u i) := by ring
      rw [he, hz, mul_zero]
    · exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (min_le_right _ _) (hZ i j he))
        (le_max_right _ _)
  have hquad : 0 ≤ w ⬝ᵥ (M *ᵥ v) := by
    have hm := hM.dotProduct_mulVec_nonneg w
    have hu : 0 ≤ w ⬝ᵥ (M *ᵥ u) := by
      simp only [dotProduct, mulVec, Finset.mul_sum]
      exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by
        simpa only [mul_assoc] using hcross i j))
    have he : v = w + u := by funext i; exact (hwu i).symm
    rw [he, mulVec_add, dotProduct_add]
    simpa only [Pi.star_apply, star_trivial] using add_nonneg hm hu
  have hnonneg : ∀ i, 0 ≤ v i := by
    intro i
    by_contra hi
    have hn : v i < 0 := lt_of_not_ge hi
    have hs : w ⬝ᵥ (M *ᵥ v) < 0 := by
      apply Finset.sum_neg'
      · intro j _
        exact mul_nonpos_of_nonpos_of_nonneg (min_le_right _ _) (hv j).le
      · exact ⟨i, Finset.mem_univ _, mul_neg_of_neg_of_pos
          (by simpa [w, min_eq_left hn.le] using hn) (hv i)⟩
    exact (not_lt_of_ge hquad) hs
  intro i
  by_contra hi
  have hz : v i = 0 := le_antisymm (le_of_not_gt hi) (hnonneg i)
  have hn : (M *ᵥ v) i ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    by_cases he : i = j
    · subst j; simp [hz]
    · exact mul_nonpos_of_nonpos_of_nonneg (hZ i j he) (hnonneg j)
  exact (not_lt_of_ge hn) (hv i)

theorem positive_scaling_exists {M : Matrix I I ℝ} (hM : M.PosDef)
    (hZ : ∀ i j, i ≠ j → M i j ≤ 0) :
    ∃ v : I → ℝ, (∀ i, 0 < v i) ∧ M *ᵥ v = 1 := by
  let := hM.isUnit.invertible
  let v := M⁻¹ *ᵥ (1 : I → ℝ)
  have hv : M *ᵥ v = 1 := by
    change M *ᵥ (M⁻¹ *ᵥ (1 : I → ℝ)) = 1
    rw [mulVec_mulVec, Matrix.mul_inv_of_invertible, one_mulVec]
  exact ⟨v, z_matrix_positive_solution hM.posSemidef hZ v (by simp [hv]), hv⟩

end ResearchMain.Chollet
