import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

namespace ResearchMain.DiagonalSchatten

open Matrix
open scoped BigOperators

theorem exists_nonnegative_two_column_gram (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hdet : c ^ 2 ≤ a * b) :
    ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
      (∀ i j, 0 ≤ X i j) ∧ X * X.transpose = !![a, c; c, b] := by
  by_cases haz : a = 0
  · have hcz : c = 0 := by rw [haz] at hdet; nlinarith [sq_nonneg c]
    subst a
    subst c
    let X : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, Real.sqrt b]
    refine ⟨X, ?_, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [X, Real.sqrt_nonneg]
    · ext i j
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
      fin_cases i <;> fin_cases j
      · simp [X]
      · simp [X]
      · simp [X]
      · change 0 * 0 + Real.sqrt b * Real.sqrt b = b
        simpa using Real.mul_self_sqrt hb
  · have ha0 : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
    have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
    have hres : 0 ≤ b - c ^ 2 / a := by
      apply sub_nonneg.mpr
      apply (div_le_iff₀ ha0).mpr
      nlinarith
    let X : Matrix (Fin 2) (Fin 2) ℝ :=
      !![Real.sqrt a, 0; c / Real.sqrt a, Real.sqrt (b - c ^ 2 / a)]
    refine ⟨X, ?_, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j
      · exact (Real.sqrt_nonneg a)
      · exact le_rfl
      · exact div_nonneg hc hsa.le
      · exact Real.sqrt_nonneg _
    · ext i j
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
      fin_cases i <;> fin_cases j
      · change Real.sqrt a * Real.sqrt a + 0 * 0 = a
        simpa using Real.mul_self_sqrt ha
      · change Real.sqrt a * (c / Real.sqrt a) + 0 * Real.sqrt (b - c ^ 2 / a) = c
        simp only [zero_mul, add_zero]
        field_simp [hsa.ne']
      · change c / Real.sqrt a * Real.sqrt a + Real.sqrt (b - c ^ 2 / a) * 0 = c
        simp only [mul_zero, add_zero]
        field_simp [hsa.ne']
      · change (c / Real.sqrt a) * (c / Real.sqrt a) +
          Real.sqrt (b - c ^ 2 / a) * Real.sqrt (b - c ^ 2 / a) = b
        rw [← pow_two, div_pow, Real.sq_sqrt ha, Real.mul_self_sqrt hres]
        ring

theorem nonnegativeGram_positiveSemidefinite (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hdet : c ^ 2 ≤ a * b) :
    (!![a, c; c, b] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  obtain ⟨X, _, hX⟩ := exists_nonnegative_two_column_gram a b c ha hb hc hdet
  rw [← hX, ← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact Matrix.posSemidef_self_mul_conjTranspose X

end ResearchMain.DiagonalSchatten
