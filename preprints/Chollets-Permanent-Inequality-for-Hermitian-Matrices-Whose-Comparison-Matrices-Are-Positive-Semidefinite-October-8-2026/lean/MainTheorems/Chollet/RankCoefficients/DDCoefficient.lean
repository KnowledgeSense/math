import MainTheorems.Chollet.RankCoefficients.GramCoefficientBounds
import MainTheorems.Chollet.DDGram

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

variable {I : Type*} [Fintype I] [LinearOrder I]

theorem dd_coefficient_bound (B : Matrix I I ℂ) (hB : B.IsHermitian)
    (a : ℝ) (z : I → ℂ) (ha : 0 < a)
    (hd : ∀ i, ‖z i‖ ≤ ddRemainder B i) (hm : ∑ i, ‖z i‖ ≤ a)
    (k : ℕ) (hk : 1 ≤ k) :
    rankCoefficient B (normalizedBorder a z) k ≤
      rankCoefficient B (normalizedBorder a z) 1 ∧
    rankCoefficient B (normalizedBorder a z) 1 ≤
      rankCoefficient B (normalizedBorder a z) 0 := by
  let U := edgeColumns (ddEdge B) (fun e => (Real.sqrt ‖B e.1.1 e.1.2‖ : ℂ))
  let D := Matrix.diagonal (fun i => (Real.sqrt (ddRemainder B i) : ℂ))
  have hQ : Matrix.fromCols U D * (Matrix.fromCols U D).conjTranspose = B := by
    have h := ddGram_reconstruct B hB (fun i => (norm_nonneg _).trans (hd i))
    change Matrix.fromCols D U * (Matrix.fromCols D U).conjTranspose = B at h
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromCols_mul_fromRows] at h ⊢
    rw [add_comm]
    exact h
  have h := edge_gram_coefficient_bound (ddEdge B)
    (fun e => (Real.sqrt ‖B e.1.1 e.1.2‖ : ℂ)) a (ddRemainder B) z ha hd hm k hk
  change rankCoefficient (Matrix.fromCols U D * (Matrix.fromCols U D).conjTranspose)
      (normalizedBorder a z) k ≤
    rankCoefficient (Matrix.fromCols U D * (Matrix.fromCols U D).conjTranspose)
      (normalizedBorder a z) 1 ∧
    rankCoefficient (Matrix.fromCols U D * (Matrix.fromCols U D).conjTranspose)
      (normalizedBorder a z) 1 ≤
    rankCoefficient (Matrix.fromCols U D * (Matrix.fromCols U D).conjTranspose)
      (normalizedBorder a z) 0 at h
  simpa only [hQ] using h

end ResearchMain.Chollet.RankCoefficients
