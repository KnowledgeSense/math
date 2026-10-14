import MainTheorems.DiagonalSchatten.CompressionHessianMatrix
import Mathlib.Analysis.Convex.PathConnected

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

def positiveDeterminantArrays : Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  {B | (∀ i j, 0 < B i j) ∧ 0 < B.det}

def logDeterminantCone : Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  {L | L 0 1 + L 1 0 < L 0 0 + L 1 1}

def entryExp (L : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => Real.exp (L i j)

theorem logDeterminantCone_convex : Convex ℝ logDeterminantCone := by
  intro X hX Y hY a b ha hb hab
  change a * X 0 1 + b * Y 0 1 + (a * X 1 0 + b * Y 1 0) <
    a * X 0 0 + b * Y 0 0 + (a * X 1 1 + b * Y 1 1)
  change X 0 1 + X 1 0 < X 0 0 + X 1 1 at hX
  change Y 0 1 + Y 1 0 < Y 0 0 + Y 1 1 at hY
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hY
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have h' := add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hX ha')
      (mul_le_mul_of_nonneg_left hY.le hb)
    nlinarith [h']

theorem entryExp_image_logDeterminantCone : entryExp '' logDeterminantCone =
    positiveDeterminantArrays := by
  ext B
  constructor
  · rintro ⟨L, hL, rfl⟩
    refine ⟨fun i j => Real.exp_pos _, ?_⟩
    rw [Matrix.det_fin_two]
    change 0 < Real.exp (L 0 0) * Real.exp (L 1 1) -
      Real.exp (L 0 1) * Real.exp (L 1 0)
    rw [← Real.exp_add, ← Real.exp_add]
    exact sub_pos.mpr (Real.exp_lt_exp.mpr hL)
  · intro hB
    let L : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j => Real.log (B i j)
    refine ⟨L, ?_, ?_⟩
    · change Real.log (B 0 1) + Real.log (B 1 0) <
        Real.log (B 0 0) + Real.log (B 1 1)
      apply Real.exp_lt_exp.mp
      rw [Real.exp_add, Real.exp_add, Real.exp_log (hB.1 0 1),
        Real.exp_log (hB.1 1 0), Real.exp_log (hB.1 0 0), Real.exp_log (hB.1 1 1)]
      have hd := hB.2
      rw [Matrix.det_fin_two] at hd
      exact sub_pos.mp hd
    · ext i j
      exact Real.exp_log (hB.1 i j)

theorem positiveDeterminantArrays_preconnected : IsPreconnected positiveDeterminantArrays := by
  rw [← entryExp_image_logDeterminantCone]
  exact logDeterminantCone_convex.isPreconnected.image entryExp (by
    unfold entryExp
    fun_prop)

theorem entryRoot_determinant_positive_iff {p : ℝ} (hp : 0 < p)
    (B : Matrix (Fin 2) (Fin 2) ℝ) (hB : ∀ i j, 0 < B i j) :
    0 < (realEntryRoot p B).det ↔ 0 < B.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [realEntryRoot, Matrix.of_apply]
  rw [← Real.mul_rpow (hB 0 0).le (hB 1 1).le,
    ← Real.mul_rpow (hB 0 1).le (hB 1 0).le]
  rw [sub_pos, sub_pos]
  exact Real.rpow_lt_rpow_iff (mul_pos (hB 0 1) (hB 1 0)).le
    (mul_pos (hB 0 0) (hB 1 1)).le (one_div_pos.mpr hp)

end

end ResearchMain.DiagonalSchatten
