import MainTheorems.Chollet.RankPolynomial
import MainTheorems.Chollet.Congruence
import MainTheorems.Chollet.PermanentEquivalence

noncomputable section

namespace ResearchMain.Chollet

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem rankPolynomial_congruence (B : Matrix I I ℂ) (x : I → ℂ) (d : I → ℝ) :
    rankPolynomial (scaledMatrix B d) (fun i => (d i : ℂ) * x i) =
      Polynomial.C (((∏ i, d i : ℝ) : ℂ) ^ 2) * rankPolynomial B x := by
  have he :
      (fun i j => Polynomial.C (scaledMatrix B d i j) +
        Polynomial.X * Polynomial.C (((d i : ℂ) * x i) * star ((d j : ℂ) * x j))) =
      (fun i j => Polynomial.C (d i : ℂ) *
        (Polynomial.C (B i j) + Polynomial.X * Polynomial.C (x i * star (x j))) *
          Polynomial.C (d j : ℂ)) := by
    funext i j
    simp only [scaledMatrix, map_mul, star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  unfold rankPolynomial
  rw [he]
  let M : Matrix I I (Polynomial ℂ) := fun i j =>
    Polynomial.C (B i j) + Polynomial.X * Polynomial.C (x i * star (x j))
  have hc := permanent_congruence M (fun i => Polynomial.C (d i : ℂ))
  change Matrix.permanent (fun i j => Polynomial.C (d i : ℂ) * M i j *
    Polynomial.C (d j : ℂ)) = _
  refine hc.trans ?_
  congr 1
  simp

theorem rankCoefficient_congruence (B : Matrix I I ℂ) (x : I → ℂ) (d : I → ℝ)
    (k : ℕ) :
    rankCoefficient (scaledMatrix B d) (fun i => (d i : ℂ) * x i) k =
      (∏ i, d i : ℝ) ^ 2 * rankCoefficient B x k := by
  rw [rankCoefficient, rankPolynomial_congruence, Polynomial.coeff_C_mul]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, rankCoefficient]

theorem rankCoefficient_le_of_congruence (B : Matrix I I ℂ) (x : I → ℂ)
    (d : I → ℝ) (hd : ∀ i, 0 < d i) (j k : ℕ)
    (h : rankCoefficient (scaledMatrix B d) (fun i => (d i : ℂ) * x i) j ≤
      rankCoefficient (scaledMatrix B d) (fun i => (d i : ℂ) * x i) k) :
    rankCoefficient B x j ≤ rankCoefficient B x k := by
  rw [rankCoefficient_congruence, rankCoefficient_congruence] at h
  have hp : 0 < (∏ i, d i : ℝ) := Finset.prod_pos (fun i _ => hd i)
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hp)).mp h

end ResearchMain.Chollet
