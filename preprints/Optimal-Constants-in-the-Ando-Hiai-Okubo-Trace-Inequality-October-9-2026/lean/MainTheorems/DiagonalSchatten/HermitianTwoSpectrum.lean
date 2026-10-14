import MainTheorems.DiagonalSchatten.GramSpectrum

namespace ResearchMain.DiagonalSchatten

noncomputable section

open Matrix
open scoped BigOperators Polynomial

def hermitianTwo (a b : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a : ℂ), z; star z, (b : ℂ)]

def twoEigenvalueGap (a b : ℝ) (z : ℂ) : ℝ :=
  Real.sqrt ((a - b) ^ 2 + 4 * ‖z‖ ^ 2)

def twoEigenvaluePlus (a b : ℝ) (z : ℂ) : ℝ :=
  (a + b + twoEigenvalueGap a b z) / 2

def twoEigenvalueMinus (a b : ℝ) (z : ℂ) : ℝ :=
  (a + b - twoEigenvalueGap a b z) / 2

theorem twoEigenvalues_sum (a b : ℝ) (z : ℂ) :
    twoEigenvaluePlus a b z + twoEigenvalueMinus a b z = a + b := by
  unfold twoEigenvaluePlus twoEigenvalueMinus
  ring

theorem twoEigenvalues_product (a b : ℝ) (z : ℂ) :
    twoEigenvaluePlus a b z * twoEigenvalueMinus a b z = a * b - ‖z‖ ^ 2 := by
  have hs : twoEigenvalueGap a b z ^ 2 = (a - b) ^ 2 + 4 * ‖z‖ ^ 2 := by
    exact Real.sq_sqrt (by positivity)
  unfold twoEigenvaluePlus twoEigenvalueMinus
  nlinarith

theorem twoEigenvaluePlus_nonneg {a b : ℝ} (z : ℂ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ twoEigenvaluePlus a b z := by
  unfold twoEigenvaluePlus twoEigenvalueGap
  positivity

theorem twoEigenvalueMinus_nonneg {a b : ℝ} (z : ℂ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hprod : ‖z‖ ^ 2 ≤ a * b) :
    0 ≤ twoEigenvalueMinus a b z := by
  have hgap : 0 ≤ twoEigenvalueGap a b z := Real.sqrt_nonneg _
  have hs : twoEigenvalueGap a b z ^ 2 = (a - b) ^ 2 + 4 * ‖z‖ ^ 2 :=
    Real.sq_sqrt (by positivity)
  unfold twoEigenvalueMinus
  nlinarith

theorem hermitianTwo_trace (a b : ℝ) (z : ℂ) :
    (hermitianTwo a b z).trace = ((a + b : ℝ) : ℂ) := by
  simp [hermitianTwo, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]

theorem hermitianTwo_det (a b : ℝ) (z : ℂ) :
    (hermitianTwo a b z).det = ((a * b - ‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  change (a : ℂ) * (b : ℂ) - z * star z = ((a * b - ‖z‖ ^ 2 : ℝ) : ℂ)
  have hz : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    simpa [← Complex.ofReal_pow] using Complex.mul_conj' z
  rw [hz]
  push_cast
  ring

theorem hermitianTwo_charpoly (a b : ℝ) (z : ℂ) :
    (hermitianTwo a b z).charpoly =
      (Polynomial.X - Polynomial.C (twoEigenvaluePlus a b z : ℂ)) *
        (Polynomial.X - Polynomial.C (twoEigenvalueMinus a b z : ℂ)) := by
  rw [Matrix.charpoly_fin_two, hermitianTwo_trace, hermitianTwo_det]
  have hsum : (twoEigenvaluePlus a b z : ℂ) + (twoEigenvalueMinus a b z : ℂ) =
      ((a + b : ℝ) : ℂ) := by exact_mod_cast twoEigenvalues_sum a b z
  have hprod : (twoEigenvaluePlus a b z : ℂ) * (twoEigenvalueMinus a b z : ℂ) =
      ((a * b - ‖z‖ ^ 2 : ℝ) : ℂ) := by exact_mod_cast twoEigenvalues_product a b z
  rw [← hsum, ← hprod, map_add, map_mul]
  ring

theorem hermitianTwo_roots (a b : ℝ) (z : ℂ) :
    (hermitianTwo a b z).charpoly.roots =
      ({(twoEigenvaluePlus a b z : ℂ)} : Multiset ℂ) +
        {(twoEigenvalueMinus a b z : ℂ)} := by
  rw [hermitianTwo_charpoly,
    Polynomial.roots_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero _)
      (Polynomial.X_sub_C_ne_zero _)),
    Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]

theorem rootPowerSum_hermitianTwo (p a b : ℝ) (z : ℂ) :
    rootPowerSum p (hermitianTwo a b z) =
      (Real.sqrt (twoEigenvaluePlus a b z)) ^ p +
        (Real.sqrt (twoEigenvalueMinus a b z)) ^ p := by
  rw [rootPowerSum, hermitianTwo_roots]
  simp

theorem rootPowerSum_hermitianTwo_of_nonneg (p : ℝ) {a b : ℝ} (z : ℂ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hprod : ‖z‖ ^ 2 ≤ a * b) :
    rootPowerSum p (hermitianTwo a b z) =
      (twoEigenvaluePlus a b z) ^ (p / 2) + (twoEigenvalueMinus a b z) ^ (p / 2) := by
  rw [rootPowerSum_hermitianTwo,
    ← Real.rpow_div_two_eq_sqrt p (twoEigenvaluePlus_nonneg z ha hb),
    ← Real.rpow_div_two_eq_sqrt p (twoEigenvalueMinus_nonneg z ha hb hprod)]

end

end ResearchMain.DiagonalSchatten
