import EdgeColoringMixing.AlternatingInfluence
import EdgeColoringMixing.GramCancellation

set_option autoImplicit false

namespace EdgeColoringMixing.WeightedInjection
open Finset

variable {d q : ℕ}

/-- The entrywise conditional covariance bound, before summing influences. -/
theorem covariance_ratio_weight_le (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (i j : Fin d) (c b : Fin q) (hij : i ≠ j) :
    let μ := law W hW.nonneg (partition_pos W hW)
    |covariance μ (i,c) (j,b)| / mean μ j b ≤ W i c / (s + 1) := by
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  have ht : 0 < s + 1 := by linarith [hW.positive]
  by_cases hx : mean μ j b = 0
  · have hz := covariance_eq_zero_of_mean_zero μ (i,c) (j,b) hx
    change |covariance μ (i,c) (j,b)| / mean μ j b ≤ _
    rw [hz, hx]
    simpa using div_nonneg (hW.nonneg i c) ht.le
  · have hxpos := lt_of_le_of_ne (mean_nonneg μ j b) (Ne.symm hx)
    have hxW := (marginal_pos_iff W hW j b).mp hxpos
    have hp := mean_nonneg μ i c
    have hpc := conditionalMean_nonneg μ (j,b) (i,c) hxpos
    have hpmax := marginal_le W hW i c
    have hpcmax := conditionalMean_le W hW j i b c hxW hij.symm
    change conditionalMean μ (j,b) (i,c) ≤ _ at hpcmax
    change mean μ i c ≤ _ at hpmax
    have heq : |covariance μ (i,c) (j,b)| / mean μ j b =
        |conditionalMean μ (j,b) (i,c) - mean μ i c| := by
      unfold conditionalMean
      rw [add_sub_cancel_left, abs_div, abs_of_nonneg (mean_nonneg μ j b)]
    change |covariance μ (i,c) (j,b)| / mean μ j b ≤ _
    rw [heq]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Lower marginals convert the weight bound to the dimensionless constant in the paper. -/
theorem covariance_ratio_le (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (i j : Fin d) (c b : Fin q) (hij : i ≠ j) :
    let μ := law W hW.nonneg (partition_pos W hW)
    |covariance μ (i,c) (j,b)| / mean μ j b ≤
      ((q : ℝ) * ((d : ℝ) + s) / (s + 1)^2) * mean μ i c := by
  dsimp only
  apply (covariance_ratio_weight_le W hW i j c b hij).trans
  have ht : 0 < s + 1 := by linarith [hW.positive]
  have hq : 0 < (q : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt c.isLt
  have hds : 0 < (d : ℝ) + s := add_pos_of_nonneg_of_pos (Nat.cast_nonneg d) hW.positive
  have h := marginal_ge W hW i c
  have hmul := mul_le_mul_of_nonneg_left h
    (show 0 ≤ (q : ℝ) * ((d : ℝ) + s) / (s + 1)^2 by positivity)
  apply le_trans ?_ hmul
  apply le_of_eq
  field_simp

/-- The squared Gram contribution is bounded by the absolute cross-row influence. -/
theorem crossRowGram_le_absolute (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (i : Fin d) (c : Fin q) :
    let μ := law W hW.nonneg (partition_pos W hW)
    crossRowGram μ c i i ≤
      ((q : ℝ) * ((d : ℝ) + s) / (s + 1)^2) * mean μ i c * crossRowAbs μ i c := by
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  let V := (q : ℝ) * ((d : ℝ) + s) / (s + 1)^2
  have hs := hW.positive
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hp := mean_nonneg μ i c
  change crossRowGram μ c i i ≤ V * mean μ i c * crossRowAbs μ i c
  unfold crossRowGram crossRowAbs
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hji : j = i
  · subst j
    simp
  · simp only [hji, ite_false]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    by_cases hbc : b = c
    · simp only [hbc, ne_eq, not_true_eq_false, false_and, ite_false]
      exact mul_nonneg (mul_nonneg hV hp) (abs_nonneg _)
    · simp only [hbc, hji, ne_eq, not_false_eq_true, and_self, ite_true]
      have h := mul_le_mul_of_nonneg_right
        (covariance_ratio_le W hW i j c b (Ne.symm hji))
        (abs_nonneg (covariance μ (i,c) (j,b)))
      change (|covariance μ (i,c) (j,b)| / mean μ j b) *
        |covariance μ (i,c) (j,b)| ≤ _ at h
      apply le_trans ?_ h
      apply le_of_eq
      unfold normalizedCovarianceProduct
      rw [div_mul_eq_mul_div]
      congr 1
      simpa only [pow_two] using (sq_abs (covariance μ (i,c) (j,b))).symm

/-- Lemma 4.5: the quantitative squared cross-row covariance estimate for the actual law. -/
theorem crossRowGram_diagonal_bound (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (i : Fin d) (c : Fin q) :
    let μ := law W hW.nonneg (partition_pos W hW)
    let V := (q : ℝ) * ((d : ℝ) + s) / (s + 1)^2
    crossRowGram μ c i i ≤ 4 * V * ((d : ℝ) - 1) * mean μ i c / (s + 1)^2 := by
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  let V := (q : ℝ) * ((d : ℝ) + s) / (s + 1)^2
  have hs := hW.positive
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hp := mean_nonneg μ i c
  have ht : 0 < s + 1 := by linarith [hW.positive]
  have hd : (1 : ℝ) ≤ d := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt i.isLt)
  have hpmax : mean μ i c ≤ 1 / (s + 1) :=
    (marginal_le W hW i c).trans
      (div_le_div_of_nonneg_right (hW.le_one i c) ht.le)
  have h₁ := crossRowGram_le_absolute W hW i c
  have h₂ := mul_le_mul_of_nonneg_left (crossRow_covariance_bound W hW i c)
    (mul_nonneg hV hp)
  change crossRowGram μ c i i ≤ V * mean μ i c * crossRowAbs μ i c at h₁
  change V * mean μ i c * crossRowAbs μ i c ≤
    V * mean μ i c * (4 * ((d : ℝ) - 1) * mean μ i c / (s + 1)) at h₂
  change crossRowGram μ c i i ≤ 4 * V * ((d : ℝ) - 1) * mean μ i c / (s + 1)^2
  apply (h₁.trans h₂).trans
  have h₃ := mul_le_mul_of_nonneg_left hpmax
    (show 0 ≤ 4 * V * ((d : ℝ) - 1) * mean μ i c / (s + 1) by positivity)
  convert h₃ using 1 <;> field_simp

/-- The same uniform constant works for every smaller-row link. -/
theorem crossRowGram_diagonal_bound_uniform (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (i : Fin d) (c : Fin q) (Δ : ℕ) (hd : d ≤ Δ) :
    let μ := law W hW.nonneg (partition_pos W hW)
    let V := (q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2
    crossRowGram μ c i i ≤ 4 * V * ((d : ℝ) - 1) * mean μ i c / (s + 1)^2 := by
  dsimp only
  apply (crossRowGram_diagonal_bound W hW i c).trans
  have hdn : 0 ≤ (d : ℝ) - 1 := by
    have h : (1 : ℝ) ≤ d := by
      exact_mod_cast Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt i.isLt)
    linarith
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (mean_nonneg _ _ _)
  apply mul_le_mul_of_nonneg_right _ hdn
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
  have hcast : (d : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hd
  linarith

end EdgeColoringMixing.WeightedInjection
