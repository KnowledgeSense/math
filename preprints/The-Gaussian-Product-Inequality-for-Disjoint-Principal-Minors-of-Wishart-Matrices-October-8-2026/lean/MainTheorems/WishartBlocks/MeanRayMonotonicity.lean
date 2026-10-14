import MainTheorems.WishartBlocks.RankOneODE

namespace ResearchMain.WishartBlocks

theorem meanRay_monotone {q : ℝ} {h h₁ h₂ : ℝ → ℝ} (hq : 1 < q)
    (hd : ∀ s : ℝ, HasDerivAt h (h₁ s) s)
    (hd₁ : ∀ s : ℝ, HasDerivAt h₁ (h₂ s) s)
    (hode : ∀ s > 0, 0 ≤ h₂ s / 2 + (q - 1) * h₁ s / (2 * s)) :
    MonotoneOn (fun θ => h (Real.sqrt θ)) (Set.Ici 0) := by
  have hc : ContinuousOn h (Set.Ici 0) := fun s _ => (hd s).continuousAt.continuousWithinAt
  have hc₁ : ContinuousOn h₁ (Set.Ici 0) := fun s _ => (hd₁ s).continuousAt.continuousWithinAt
  have hm : MonotoneOn h (Set.Ici 0) :=
    rankOne_monotone (q := 2 * (q - 1)) (by linarith) hc hc₁
      (fun s _ => hd s) (fun s _ => hd₁ s) (fun s hs => by
        have h := mul_nonneg (hode s hs) (by positivity : 0 ≤ 4 * s)
        have he : (h₂ s / 2 + (q - 1) * h₁ s / (2 * s)) * (4 * s) =
            2 * s * h₂ s + 2 * (q - 1) * h₁ s := by
          field_simp [hs.ne']
          ring
        rwa [he] at h)
  intro θ hθ η hη hθη
  exact hm (Real.sqrt_nonneg θ) (Real.sqrt_nonneg η) (Real.sqrt_le_sqrt hθη)

end ResearchMain.WishartBlocks
