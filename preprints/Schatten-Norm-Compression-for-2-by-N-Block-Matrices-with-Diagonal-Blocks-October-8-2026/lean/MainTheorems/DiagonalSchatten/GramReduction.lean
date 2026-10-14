import MainTheorems.DiagonalSchatten.RaySupport
import MainTheorems.DiagonalSchatten.TwoColumnGram
import MainTheorems.DiagonalSchatten.AreaVector

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

theorem exists_two_column_same_gram (X : Matrix (Fin 2) J ℝ)
    (hX : ∀ i j, 0 ≤ X i j) :
    ∃ T : Matrix (Fin 2) (Fin 2) ℝ, (∀ i j, 0 ≤ T i j) ∧
      gramFirst T = gramFirst X ∧ gramSecond T = gramSecond X ∧
        gramCross T = gramCross X := by
  have ha : 0 ≤ gramFirst X := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : 0 ≤ gramSecond X := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc : 0 ≤ gramCross X := Finset.sum_nonneg fun j _ => mul_nonneg (hX 0 j) (hX 1 j)
  have hdet : gramCross X ^ 2 ≤ gramFirst X * gramSecond X := by
    have he := areaVector_norm_sq X
    nlinarith [sq_nonneg ‖areaVector X‖]
  obtain ⟨T, hT, he⟩ := exists_nonnegative_two_column_gram
    (gramFirst X) (gramSecond X) (gramCross X) ha hb hc hdet
  refine ⟨T, hT, ?_, ?_, ?_⟩
  · have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) he
    simpa [gramFirst, Matrix.mul_apply, Fin.sum_univ_two, pow_two] using h
  · have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) he
    simpa [gramSecond, Matrix.mul_apply, Fin.sum_univ_two, pow_two] using h
  · have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) he
    simpa [gramCross, Matrix.mul_apply, Fin.sum_univ_two] using h

namespace RayParameters

variable (g : RayParameters)

theorem zero_contactPolynomial_two_column_reduction (s : ℝ) (q : Fin 3 → ℝ)
    (hp : g.contactPolynomial s q = 0)
    (hD : ∀ x, 0 ≤ x 0 → 0 ≤ x 1 → (0 < x 0 ∨ 0 < x 1) → g.denominator x ≠ 0)
    (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j) :
    ∃ T : Matrix (Fin 2) (Fin 2) ℝ, (∀ i j, 0 ≤ T i j) ∧
      gramFirst T = gramFirst X ∧ gramSecond T = gramSecond X ∧
      gramCross T = gramCross X ∧
      columnObjective (fun x => s * g.functional x) T =
        columnObjective (fun x => s * g.functional x) X := by
  obtain ⟨T, hT, ha, hb, hc⟩ := exists_two_column_same_gram X hX
  refine ⟨T, hT, ha, hb, hc, ?_⟩
  rw [g.zero_contactPolynomial_objective s q hp hD T hT,
    g.zero_contactPolynomial_objective s q hp hD X hX, ha, hb, hc]

end RayParameters

end

end ResearchMain.DiagonalSchatten
