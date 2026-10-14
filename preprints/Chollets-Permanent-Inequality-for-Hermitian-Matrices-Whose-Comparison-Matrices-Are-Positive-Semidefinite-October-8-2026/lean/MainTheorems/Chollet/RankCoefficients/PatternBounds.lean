import MainTheorems.Chollet.RankCoefficients.PatternGram
import MainTheorems.Chollet.RankCoefficients.WeightedNormalForm

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

variable {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I]

theorem real_scalar_coefficient (P : Polynomial ℂ) (w : ℝ) (k : ℕ) :
    ((Polynomial.C (w : ℂ) * P).coeff k).re = w * (P.coeff k).re := by
  simp only [Polynomial.coeff_C_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

omit [Fintype E] in
theorem contracted_pattern_polynomial (U : Matrix I E ℂ) (d : I → ℝ)
    (x : I → ℂ) (s : Finset I) (l : s → E) (p : RootedPartition I) (c : ℂ)
    (hd : ∀ i, 0 ≤ d i)
    (h : (∏ j : s, linearForm (fun i => U i (l j))) = scalar c * p.polynomial)
    (e : p.parts ≃ {i : I // i ∉ s}) :
    patternPolynomial U (Matrix.diagonal (fun i => (Real.sqrt (d i) : ℂ))) x s l =
      Polynomial.C (((‖c‖ ^ 2 * Fintype.card (Equiv.Perm p.parts) : ℝ) : ℂ)) *
        rankPolynomial (Matrix.diagonal (fun t => (p.mass d t : ℂ))) (p.contraction x) := by
  rw [patternPolynomial_contraction U _ x s l p c h e]
  have hD : (fun t j => p.contraction
      (fun i => Matrix.diagonal (fun u => (Real.sqrt (d u) : ℂ)) i j) t) =
      p.diagonalColumns d := by
    funext t j
    exact p.contraction_diagonal d t j
  rw [hD, ← gram_assignment_polynomial, p.diagonalColumns_gram d hd]
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast, Polynomial.C_mul]
  ring

omit [Fintype E] in
theorem pattern_coefficient_bound (edges : E → UnitEdge I) (w : E → ℂ)
    (a : ℝ) (d : I → ℝ) (z : I → ℂ) (ha : 0 < a)
    (hd : ∀ i, ‖z i‖ ≤ d i) (hm : ∑ i, ‖z i‖ ≤ a)
    (s : Finset I) (l : s → E) (k : ℕ) (hk : 1 ≤ k) :
    ((patternPolynomial (edgeColumns edges w)
      (Matrix.diagonal (fun i => (Real.sqrt (d i) : ℂ)))
      (normalizedBorder a z) s l).coeff k).re ≤
      ((patternPolynomial (edgeColumns edges w)
        (Matrix.diagonal (fun i => (Real.sqrt (d i) : ℂ)))
        (normalizedBorder a z) s l).coeff 1).re ∧
    ((patternPolynomial (edgeColumns edges w)
      (Matrix.diagonal (fun i => (Real.sqrt (d i) : ℂ)))
      (normalizedBorder a z) s l).coeff 1).re ≤
      ((patternPolynomial (edgeColumns edges w)
        (Matrix.diagonal (fun i => (Real.sqrt (d i) : ℂ)))
        (normalizedBorder a z) s l).coeff 0).re := by
  classical
  obtain ⟨p, c, hp, hc⟩ := weighted_normal_form edges w s l
  rcases hc with hc | hc
  · rw [hc, scalar_zero, zero_mul] at hp
    simp only [patternPolynomial_zero _ _ _ s l hp, Polynomial.coeff_zero,
      Complex.zero_re, le_refl, and_self]
  · obtain ⟨e⟩ := remaining_equiv p s hc
    simp only [contracted_pattern_polynomial _ d _ s l p c
      (fun i => (norm_nonneg _).trans (hd i)) hp e, real_scalar_coefficient]
    have hw : 0 ≤ ‖c‖ ^ 2 * (Fintype.card (Equiv.Perm p.parts) : ℝ) :=
      mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
    have hb := p.diagonal_coefficient_bound a d z ha hd hm k hk
    exact ⟨mul_le_mul_of_nonneg_left hb.1 hw, mul_le_mul_of_nonneg_left hb.2 hw⟩

end ResearchMain.Chollet.RankCoefficients
