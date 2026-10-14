import MainTheorems.DiagonalSchatten.DiagonalSpectrum
import Mathlib.Analysis.MeanInequalities

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators

variable {J D : Type*} [Fintype D] [DecidableEq D]

theorem diagonal_norm_triangle {q : ℝ} (hq : 1 ≤ q) (v w : D → ℂ) :
    schattenNorm q (Matrix.diagonal (v + w)) ≤
      schattenNorm q (Matrix.diagonal v) + schattenNorm q (Matrix.diagonal w) := by
  rw [schattenNorm_diagonal, schattenNorm_diagonal, schattenNorm_diagonal]
  calc
    _ ≤ (∑ d, (‖v d‖ + ‖w d‖) ^ q) ^ (1 / q) := by
      apply Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
      · exact Finset.sum_le_sum fun d _ =>
          Real.rpow_le_rpow (norm_nonneg _) (norm_add_le (v d) (w d)) (by linarith)
      · positivity
    _ ≤ _ := Real.Lp_add_le_of_nonneg Finset.univ
      hq (fun d _ => norm_nonneg _) (fun d _ => norm_nonneg _)

variable [DecidableEq J]

set_option maxHeartbeats 800000 in
theorem diagonal_norm_sum {q : ℝ} (hq : 1 ≤ q) (s : Finset J) (v : J → D → ℂ) :
    schattenNorm q (Matrix.diagonal (∑ j ∈ s, v j)) ≤
      ∑ j ∈ s, schattenNorm q (Matrix.diagonal (v j)) := by
  induction s using Finset.induction_on with
  | empty =>
      have hq0 : q ≠ 0 := by linarith
      rw [Finset.sum_empty, Finset.sum_empty, schattenNorm_diagonal]
      simp only [Pi.zero_apply, norm_zero, Real.zero_rpow hq0, Finset.sum_const_zero]
      rw [Real.zero_rpow (one_div_ne_zero hq0)]
  | @insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      calc
        _ ≤ schattenNorm q (Matrix.diagonal (v j)) +
            schattenNorm q (Matrix.diagonal (∑ k ∈ s, v k)) :=
          diagonal_norm_triangle (D := D) hq (v j) (∑ k ∈ s, v k)
        _ ≤ _ := add_le_add le_rfl ih

omit [DecidableEq J] in
theorem diagonal_norm_product {q : ℝ} (hq : 0 < q) (v w : D → ℂ) :
    schattenNorm q (Matrix.diagonal (fun d => v d * star (w d))) ≤
      schattenNorm (2 * q) (Matrix.diagonal v) *
        schattenNorm (2 * q) (Matrix.diagonal w) := by
  let A := schattenNorm (2 * q) (Matrix.diagonal v)
  let B := schattenNorm (2 * q) (Matrix.diagonal w)
  let C := schattenNorm q (Matrix.diagonal (fun d => v d * star (w d)))
  have hA : 0 ≤ A := schattenNorm_nonneg _ _
  have hB : 0 ≤ B := schattenNorm_nonneg _ _
  have hC : 0 ≤ C := schattenNorm_nonneg _ _
  have hCq : C ^ q = ∑ d, ‖v d‖ ^ q * ‖w d‖ ^ q := by
    rw [schattenNorm_rpow q hq.ne', schattenPower_diagonal]
    simp only [norm_mul, norm_star, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  have hAq : A ^ (2 * q) = ∑ d, (‖v d‖ ^ q) ^ 2 := by
    rw [schattenNorm_rpow (2 * q) (by positivity), schattenPower_diagonal]
    apply Finset.sum_congr rfl
    intro d _
    rw [← Real.rpow_mul_natCast (norm_nonneg _) q 2]
    congr 1
    ring
  have hBq : B ^ (2 * q) = ∑ d, (‖w d‖ ^ q) ^ 2 := by
    rw [schattenNorm_rpow (2 * q) (by positivity), schattenPower_diagonal]
    apply Finset.sum_congr rfl
    intro d _
    rw [← Real.rpow_mul_natCast (norm_nonneg _) q 2]
    congr 1
    ring
  apply (Real.rpow_le_rpow_iff hC (mul_nonneg hA hB) (by positivity : 0 < 2 * q)).mp
  rw [Real.mul_rpow hA hB, hAq, hBq,
    show C ^ (2 * q) = (C ^ q) ^ 2 by
      rw [← Real.rpow_mul_natCast hC q 2]; congr 1; ring, hCq]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun d => ‖v d‖ ^ q) (fun d => ‖w d‖ ^ q)

omit [DecidableEq J] in
theorem diagonal_norm_square {q : ℝ} (hq : 0 < q) (v : D → ℂ) :
    schattenNorm q (Matrix.diagonal (fun d => v d * star (v d))) =
      schattenNorm (2 * q) (Matrix.diagonal v) ^ 2 := by
  rw [schattenNorm_diagonal, schattenNorm_diagonal]
  simp only [norm_mul, norm_star, ← sq]
  have hs : (∑ d, (‖v d‖ ^ 2) ^ q) = ∑ d, ‖v d‖ ^ (2 * q) := by
    apply Finset.sum_congr rfl
    intro d _
    simpa using (Real.rpow_natCast_mul (norm_nonneg (v d)) 2 q).symm
  rw [hs]
  have he : 1 / q = (1 / (2 * q)) * (2 : ℝ) := by field_simp
  rw [he]
  simpa using Real.rpow_mul_natCast
    (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) (1 / (2 * q)) 2

end

end ResearchMain.DiagonalSchatten
