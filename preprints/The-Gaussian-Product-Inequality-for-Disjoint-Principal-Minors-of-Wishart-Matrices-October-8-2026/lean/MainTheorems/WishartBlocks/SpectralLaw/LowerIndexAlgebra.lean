import MainTheorems.WishartBlocks.SpectralLaw.CholeskyChangeOfVariables
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

namespace ResearchMain.WishartBlocks

open scoped BigOperators

theorem lowerIndex_prod {n : ℕ} {M : Type*} [CommMonoid M]
    (f : (Fin n ×ₗ Fin n) → M) :
    (∏ e : LowerIndex n, f e.val) =
      ∏ i : Fin n, ∏ j : Fin n, if j ≤ i then f (toLex (i, j)) else 1 := by
  classical
  rw [← Finset.prod_subtype
    (Finset.univ.filter fun e : Fin n ×ₗ Fin n => e.2 ≤ e.1) (by simp) f,
    Finset.prod_filter]
  exact Fintype.prod_prod_type _

theorem lowerIndex_sum {n : ℕ} {M : Type*} [AddCommMonoid M]
    (f : (Fin n ×ₗ Fin n) → M) :
    (∑ e : LowerIndex n, f e.val) =
      ∑ i : Fin n, ∑ j : Fin n, if j ≤ i then f (toLex (i, j)) else 0 := by
  classical
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun e : Fin n ×ₗ Fin n => e.2 ≤ e.1) (by simp) f,
    Finset.sum_filter]
  exact Fintype.sum_prod_type _

theorem lower_column_product {n : ℕ} (a : Fin n → ℝ) :
    (∏ e : LowerIndex n, a e.val.2) = ∏ j : Fin n, a j ^ (n - j.val) := by
  change (∏ e : LowerIndex n, a (ofLex e.val).2) = _
  rw [lowerIndex_prod (fun e : Fin n ×ₗ Fin n => a (ofLex e).2), Finset.prod_comm]
  simp only [ofLex_toLex]
  apply Finset.prod_congr rfl
  intro j _
  rw [← Finset.prod_filter]
  have hs : Finset.univ.filter (fun i : Fin n => j ≤ i) = Finset.Ici j := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
  rw [hs, Finset.prod_const, Fin.card_Ici]

theorem lower_diagonal_product {n : ℕ} (a : Fin n → ℝ) :
    (∏ e : LowerIndex n, if e.val.1 = e.val.2 then a e.val.1 else 1) = ∏ i, a i := by
  change (∏ e : LowerIndex n,
    if (ofLex e.val).1 = (ofLex e.val).2 then a (ofLex e.val).1 else 1) = _
  rw [lowerIndex_prod (fun e : Fin n ×ₗ Fin n =>
    if (ofLex e).1 = (ofLex e).2 then a (ofLex e).1 else 1)]
  simp only [ofLex_toLex]
  apply Finset.prod_congr rfl
  intro i _
  change (∏ j : Fin n, if j ≤ i then (if i = j then a i else 1) else 1) = a i
  calc
    _ = ∏ j : Fin n, if i = j then a i else 1 := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hij : i = j
      · subst j
        simp only [le_refl, ite_true]
      · simp only [hij, ite_false, ite_self]
    _ = a i := by simp only [Finset.prod_ite_eq, Finset.mem_univ, ite_true]

theorem choleskyJacobianWeight_formula {n : ℕ} (x : LowerIndex n → ℝ) :
    choleskyJacobianWeight x =
      2 ^ n * ∏ j : Fin n, lowerMatrix x j j ^ (n - j.val) := by
  have he (e : LowerIndex n) :
      (if e.val.1 = e.val.2 then 2 * lowerMatrix x e.val.2 e.val.2
        else lowerMatrix x e.val.2 e.val.2) =
      (if e.val.1 = e.val.2 then 2 else 1) * lowerMatrix x e.val.2 e.val.2 := by
    split_ifs <;> simp only [one_mul]
  unfold choleskyJacobianWeight
  simp_rw [he]
  rw [Finset.prod_mul_distrib, lower_diagonal_product (fun _ => 2),
    lower_column_product (fun j => lowerMatrix x j j)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem lowerGram_trace {n : ℕ} (x : LowerIndex n → ℝ) :
    (lowerMatrix x * (lowerMatrix x).transpose).trace = ∑ e : LowerIndex n, x e ^ 2 := by
  have he : (∑ e : LowerIndex n, lowerMatrix x e.val.1 e.val.2 ^ 2) =
      ∑ i : Fin n, ∑ j : Fin n, lowerMatrix x i j ^ 2 := by
    change (∑ e : LowerIndex n,
      lowerMatrix x (ofLex e.val).1 (ofLex e.val).2 ^ 2) = _
    rw [lowerIndex_sum (fun e : Fin n ×ₗ Fin n =>
      lowerMatrix x (ofLex e).1 (ofLex e).2 ^ 2)]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ≤ i
    · simp only [ofLex_toLex, hj, ite_true]
    · simp only [hj, ite_false, lowerMatrix_lowerTriangular x (lt_of_not_ge hj), pow_two,
        mul_zero]
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n, lowerMatrix x i j ^ 2 := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
    _ = ∑ e : LowerIndex n, lowerMatrix x e.val.1 e.val.2 ^ 2 := he.symm
    _ = _ := by simp only [lowerMatrix_entry]

theorem lowerGram_det {n : ℕ} (x : LowerIndex n → ℝ) :
    (lowerMatrix x * (lowerMatrix x).transpose).det =
      (∏ i : Fin n, lowerMatrix x i i) ^ 2 := by
  rw [Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_of_isLowerTriangular _ (lowerMatrix_lowerTriangular x), pow_two]

theorem lowerGram_det_rpow {n : ℕ} {x : LowerIndex n → ℝ}
    (hx : x ∈ positiveLowerCoordinates n) (β : ℝ) :
    (lowerMatrix x * (lowerMatrix x).transpose).det ^ β =
      ∏ i : Fin n, lowerMatrix x i i ^ (2 * β) := by
  rw [lowerGram_det, ← Real.rpow_natCast_mul
    (Finset.prod_nonneg fun i _ => (hx i).le) 2 β]
  exact (Real.finsetProd_rpow Finset.univ _ (fun i _ => (hx i).le) _).symm

end ResearchMain.WishartBlocks
