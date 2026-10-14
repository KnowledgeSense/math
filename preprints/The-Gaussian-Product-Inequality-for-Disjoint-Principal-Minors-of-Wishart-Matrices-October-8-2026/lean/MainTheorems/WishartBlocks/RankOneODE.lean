import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

namespace ResearchMain.WishartBlocks

theorem rankOne_integrating_factor {q θ : ℝ} {g₁ g₂ : ℝ → ℝ}
    (hθ : 0 < θ) (hderiv : HasDerivAt g₁ (g₂ θ) θ) :
    HasDerivAt (fun t : ℝ => t ^ (q / 2) * g₁ t)
      (θ ^ (q / 2 - 1) / 2 * (2 * θ * g₂ θ + q * g₁ θ)) θ := by
  have hp := Real.hasDerivAt_rpow_const (p := q / 2) (Or.inl hθ.ne')
  convert hp.mul hderiv using 1
  have he : θ ^ (q / 2) = θ ^ (q / 2 - 1) * θ := by
    simpa only [sub_add_cancel] using Real.rpow_add_one hθ.ne' (q / 2 - 1)
  rw [he]
  ring

theorem rankOne_derivative_nonneg {q : ℝ} {g₁ g₂ : ℝ → ℝ}
    (hq : 0 < q) (hc : ContinuousOn g₁ (Set.Ici 0))
    (hd : ∀ θ > 0, HasDerivAt g₁ (g₂ θ) θ)
    (hode : ∀ θ > 0, 0 ≤ 2 * θ * g₂ θ + q * g₁ θ) :
    ∀ θ ≥ 0, 0 ≤ g₁ θ := by
  let h : ℝ → ℝ := fun θ => θ ^ (q / 2) * g₁ θ
  have hh : ContinuousOn h (Set.Ici 0) :=
    (Real.continuous_rpow_const (by positivity : 0 ≤ q / 2)).continuousOn.mul hc
  have hm : MonotoneOn h (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hh
    · intro θ hθ
      rw [interior_Ici, Set.mem_Ioi] at hθ
      exact (rankOne_integrating_factor hθ (hd θ hθ)).differentiableAt.differentiableWithinAt
    · intro θ hθ
      rw [interior_Ici, Set.mem_Ioi] at hθ
      rw [(rankOne_integrating_factor hθ (hd θ hθ)).deriv]
      exact mul_nonneg (by positivity) (hode θ hθ)
  have hz : h 0 = 0 := by
    dsimp [h]
    rw [Real.zero_rpow (by positivity : q / 2 ≠ 0), zero_mul]
  have hn : ∀ θ > 0, 0 ≤ g₁ θ := by
    intro θ hθ
    have hpos : 0 < θ ^ (q / 2) := Real.rpow_pos_of_pos hθ _
    have ht := hm (by simp) hθ.le hθ.le
    rw [hz] at ht
    exact nonneg_of_mul_nonneg_right ht hpos
  intro θ hθ
  rcases eq_or_lt_of_le hθ with rfl | hθ
  · have hlim : Filter.Tendsto g₁ (nhdsWithin 0 (Set.Ioi 0)) (nhds (g₁ 0)) :=
      (hc 0 (by simp)).mono (by intro x hx; exact (Set.mem_Ioi.mp hx).le)
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hn t (Set.mem_Ioi.mp ht)
  · exact hn θ hθ

theorem rankOne_monotone {q : ℝ} {g g₁ g₂ : ℝ → ℝ}
    (hq : 0 < q) (hc : ContinuousOn g (Set.Ici 0))
    (hc₁ : ContinuousOn g₁ (Set.Ici 0))
    (hd : ∀ θ > 0, HasDerivAt g (g₁ θ) θ)
    (hd₁ : ∀ θ > 0, HasDerivAt g₁ (g₂ θ) θ)
    (hode : ∀ θ > 0, 0 ≤ 2 * θ * g₂ θ + q * g₁ θ) :
    MonotoneOn g (Set.Ici 0) := by
  have hn := rankOne_derivative_nonneg hq hc₁ hd₁ hode
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hc
  · intro θ hθ
    rw [interior_Ici, Set.mem_Ioi] at hθ
    exact (hd θ hθ).differentiableAt.differentiableWithinAt
  · intro θ hθ
    rw [interior_Ici, Set.mem_Ioi] at hθ
    rw [(hd θ hθ).deriv]
    exact hn θ hθ.le

end ResearchMain.WishartBlocks
