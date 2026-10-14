import MainTheorems.Chollet.RankCoefficients.PatternBounds

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

variable {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I]

theorem gram_coefficient_split (U : Matrix I E ℂ) (D : Matrix I I ℂ)
    (x : I → ℂ) (k : ℕ) :
    (Fintype.card (Equiv.Perm I) : ℝ) *
        rankCoefficient ((Matrix.fromCols U D) * (Matrix.fromCols U D).conjTranspose) x k =
      ∑ s : Finset I, ∑ l : s → E, ((patternPolynomial U D x s l).coeff k).re := by
  have h := congrArg (fun P : Polynomial ℂ => (P.coeff k).re)
    (gram_assignment_polynomial_split U D x)
  have hc : (Fintype.card (Equiv.Perm I) : ℂ) =
      ((Fintype.card (Equiv.Perm I) : ℝ) : ℂ) := by norm_cast
  simpa only [hc, real_scalar_coefficient, rankCoefficient, Polynomial.finsetSum_coeff,
    Complex.re_sum] using h

theorem edge_gram_coefficient_bound (edges : E → UnitEdge I) (w : E → ℂ)
    (a : ℝ) (d : I → ℝ) (z : I → ℂ) (ha : 0 < a)
    (hd : ∀ i, ‖z i‖ ≤ d i) (hm : ∑ i, ‖z i‖ ≤ a)
    (k : ℕ) (hk : 1 ≤ k) :
    let Q := Matrix.fromCols (edgeColumns edges w)
      (Matrix.diagonal (fun i => (Real.sqrt (d i) : ℂ)))
    rankCoefficient (Q * Q.conjTranspose) (normalizedBorder a z) k ≤
      rankCoefficient (Q * Q.conjTranspose) (normalizedBorder a z) 1 ∧
    rankCoefficient (Q * Q.conjTranspose) (normalizedBorder a z) 1 ≤
      rankCoefficient (Q * Q.conjTranspose) (normalizedBorder a z) 0 := by
  dsimp only
  have hc : (0 : ℝ) < Fintype.card (Equiv.Perm I) := by
    exact_mod_cast Fintype.card_pos
  have hb := fun s l => pattern_coefficient_bound edges w a d z ha hd hm s l k hk
  constructor
  · apply le_of_mul_le_mul_left _ hc
    rw [gram_coefficient_split, gram_coefficient_split]
    apply Finset.sum_le_sum
    intro s _
    apply Finset.sum_le_sum
    intro l _
    exact (hb s l).1
  · apply le_of_mul_le_mul_left _ hc
    rw [gram_coefficient_split, gram_coefficient_split]
    apply Finset.sum_le_sum
    intro s _
    apply Finset.sum_le_sum
    intro l _
    exact (hb s l).2

end ResearchMain.Chollet.RankCoefficients

