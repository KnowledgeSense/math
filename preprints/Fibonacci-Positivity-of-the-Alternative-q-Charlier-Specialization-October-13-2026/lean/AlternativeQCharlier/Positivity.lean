import AlternativeQCharlier.Parameters
import AlternativeQCharlier.FinitePositivity
import AlternativeQCharlier.Words

namespace AlternativeQCharlier
noncomputable section

 theorem A_pos {ρ q : ℝ} (h : ParameterBox ρ q) (m n : ℕ) :
    0 < A (x ρ q) (y ρ q) m n := by
  have hx : x ρ q = fun i => c ρ q i*(1+t ρ q i) := funext (x_eq_rescaling h)
  have hy : y ρ q = fun i => c ρ q i*c ρ q (i+1)*t ρ q (i+1) := funext (y_eq_rescaling h)
  rw [hx, hy, A_rescaling, normalized_A]
  exact mul_pos (scaleProduct_pos _ (c_pos h) _ _)
    (lt_of_lt_of_le (by norm_num) (tail_bounds _ (t_nonneg h) (t_le h) m n).1)

 theorem B_pos {ρ q : ℝ} (h : ParameterBox ρ q) (m n : ℕ) :
    0 < B (x ρ q) (y ρ q) m n := by
  have hx : x ρ q = fun i => c ρ q i*(1+t ρ q i) := funext (x_eq_rescaling h)
  have hy : y ρ q = fun i => c ρ q i*c ρ q (i+1)*t ρ q (i+1) := funext (y_eq_rescaling h)
  rw [hx, hy, B_rescaling]
  exact mul_pos (scaleProduct_pos _ (c_pos h) _ _)
    (normalized_B_pos _ (t_nonneg h) (t_pos h) (t_le h) (t_ratio_le h) m n)

/-- Every finite clone Schur word is strictly positive throughout the full
closed-upper-endpoint parameter box of the source theorem. -/
theorem cloneSchur_pos {ρ q : ℝ} (h : ParameterBox ρ q) (w : Word) :
    0 < cloneSchur (x ρ q) (y ρ q) w := by
  induction w with
  | terminal n => exact A_pos h 0 n
  | prepend n w ih => exact mul_pos (B_pos h w.weight n) ih

/-- The same theorem quantified over arbitrary finite lists of letters. -/
theorem all_finite_words_pos {ρ q : ℝ} (h : ParameterBox ρ q) (l : List Bool) :
    0 < cloneSchur (x ρ q) (y ρ q) (Word.fromList l) := cloneSchur_pos h _

end
end AlternativeQCharlier
