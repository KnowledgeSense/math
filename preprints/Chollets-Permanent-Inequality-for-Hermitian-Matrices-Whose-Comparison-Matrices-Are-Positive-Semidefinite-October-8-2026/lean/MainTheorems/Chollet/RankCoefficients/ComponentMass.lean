import MainTheorems.Chollet.Basic
import MainTheorems.Chollet.ElementaryBounds

noncomputable section

namespace ResearchMain.Chollet

variable {I T : Type*} [Fintype I] [DecidableEq I]

def componentRatio (a : ℝ) (d : I → ℝ) (z c : I → ℂ) (s : Finset I) : ℝ :=
  ‖∑ i ∈ s, c i * z i‖ ^ 2 / (a * ∑ i ∈ s, d i)

omit [Fintype I] [DecidableEq I] in
theorem component_phase_bound (s : Finset I) (z c : I → ℂ)
    (hc : ∀ i ∈ s, ‖c i‖ ≤ 1) :
    ‖∑ i ∈ s, c i * z i‖ ≤ ∑ i ∈ s, ‖z i‖ := by
  calc
    ‖∑ i ∈ s, c i * z i‖ ≤ ∑ i ∈ s, ‖c i * z i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖z i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      simpa using mul_le_mul_of_nonneg_right (hc i hi) (norm_nonneg (z i))

omit [Fintype I] [DecidableEq I] in
theorem componentRatio_nonneg (a : ℝ) (d : I → ℝ) (z c : I → ℂ)
    (s : Finset I) (ha : 0 ≤ a) (hd : ∀ i ∈ s, 0 ≤ d i) :
    0 ≤ componentRatio a d z c s := by
  exact div_nonneg (sq_nonneg _) (mul_nonneg ha (Finset.sum_nonneg hd))

omit [Fintype I] [DecidableEq I] in
theorem componentRatio_le (a : ℝ) (d : I → ℝ) (z c : I → ℂ)
    (s : Finset I) (ha : 0 < a) (hd : ∀ i ∈ s, ‖z i‖ ≤ d i)
    (hc : ∀ i ∈ s, ‖c i‖ ≤ 1) :
    componentRatio a d z c s ≤ (∑ i ∈ s, ‖z i‖) / a := by
  have hz : 0 ≤ ∑ i ∈ s, ‖z i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (z i))
  have hD : (∑ i ∈ s, ‖z i‖) ≤ ∑ i ∈ s, d i := Finset.sum_le_sum hd
  have hD0 : 0 ≤ ∑ i ∈ s, d i := hz.trans hD
  by_cases hDp : 0 < ∑ i ∈ s, d i
  · have hp := component_phase_bound s z c hc
    have hs : ‖∑ i ∈ s, c i * z i‖ ^ 2 ≤
        (∑ i ∈ s, ‖z i‖) * ∑ i ∈ s, d i := by
      have hsq := (sq_le_sq₀ (norm_nonneg _) hz).mpr hp
      have hm := mul_le_mul_of_nonneg_left hD hz
      nlinarith
    unfold componentRatio
    apply (div_le_iff₀ (mul_pos ha hDp)).mpr
    have he : (∑ i ∈ s, ‖z i‖) / a * (a * ∑ i ∈ s, d i) =
        (∑ i ∈ s, ‖z i‖) * ∑ i ∈ s, d i := by
      field_simp [ha.ne']
    rwa [he]
  · have hDz : ∑ i ∈ s, d i = 0 := by linarith
    simp only [componentRatio, hDz, mul_zero, div_zero]
    exact div_nonneg hz ha.le

omit [Fintype I] [DecidableEq I] in
theorem component_zero_mass (d : I → ℝ) (z c : I → ℂ)
    (s : Finset I) (hd : ∀ i ∈ s, ‖z i‖ ≤ d i)
    (hD : ∑ i ∈ s, d i = 0) :
    (∑ i ∈ s, c i * z i) = 0 := by
  have hd0 : ∀ i ∈ s, 0 ≤ d i := fun i hi => (norm_nonneg _).trans (hd i hi)
  have hdi : ∀ i ∈ s, d i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hd0).mp hD
  apply Finset.sum_eq_zero
  intro i hi
  have hz : z i = 0 := norm_eq_zero.mp (by
    have h := hd i hi
    rw [hdi i hi] at h
    exact le_antisymm h (norm_nonneg _))
  simp only [hz, mul_zero]

theorem componentRatio_total [DecidableEq T] (t : Finset T) (s : T → Finset I)
    (hs : Set.PairwiseDisjoint (↑t) s) (a : ℝ) (d : I → ℝ) (z : I → ℂ)
    (c : T → I → ℂ) (ha : 0 < a) (hd : ∀ i, ‖z i‖ ≤ d i)
    (hc : ∀ j ∈ t, ∀ i ∈ s j, ‖c j i‖ ≤ 1) (hm : ∑ i, ‖z i‖ ≤ a) :
    ∑ j ∈ t, componentRatio a d z (c j) (s j) ≤ 1 := by
  calc
    ∑ j ∈ t, componentRatio a d z (c j) (s j)
        ≤ ∑ j ∈ t, (∑ i ∈ s j, ‖z i‖) / a := by
      apply Finset.sum_le_sum
      intro j hj
      exact componentRatio_le a d z (c j) (s j) ha (fun i _ => hd i) (hc j hj)
    _ = (∑ i ∈ t.biUnion s, ‖z i‖) / a := by
      rw [Finset.sum_biUnion hs]
      simp only [Finset.sum_div]
    _ ≤ (∑ i, ‖z i‖) / a := by
      apply div_le_div_of_nonneg_right _ ha.le
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => norm_nonneg (z i))
    _ ≤ 1 := (div_le_one ha).mpr hm

end ResearchMain.Chollet
