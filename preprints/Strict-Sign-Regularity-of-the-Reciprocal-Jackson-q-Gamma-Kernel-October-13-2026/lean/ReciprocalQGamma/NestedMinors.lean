import ReciprocalQGamma.NestedCoefficients
import ReciprocalQGamma.GeneralizedVandermonde
import Mathlib.LinearAlgebra.Matrix.Block

noncomputable section
open scoped BigOperators
open Polynomial
namespace ReciprocalQGamma

theorem nestedPolynomial_monic (c : ℕ → ℝ) (k : ℕ) : (nestedPolynomial c k).Monic := by
  induction k with
  | zero => simp [nestedPolynomial]
  | succ k ih => rw [nestedPolynomial_succ]; exact ih.mul (monic_X_add_C _)

theorem nestedPolynomial_degree (c : ℕ → ℝ) (k : ℕ) : (nestedPolynomial c k).natDegree = k := by
  induction k with
  | zero => simp [nestedPolynomial]
  | succ k ih =>
    rw [nestedPolynomial_succ, (nestedPolynomial_monic c k).natDegree_mul (monic_X_add_C _),
      ih, natDegree_X_add_C]

theorem coefficientMatrix_final (c : ℕ → ℝ) (m : ℕ) (k d : Fin m) :
    coefficientMatrix c m m k d = (nestedPolynomial c k.val).coeff d.val := by
  simp [coefficientMatrix, intermediatePolynomial]

theorem coefficientMatrix_triangular (c : ℕ → ℝ) (m : ℕ) :
    (coefficientMatrix c m m).IsLowerTriangular := by
  intro i j hij
  rw [coefficientMatrix_final]
  exact coeff_eq_zero_of_natDegree_lt (by simpa [nestedPolynomial_degree] using hij)

theorem coefficientMatrix_diagonal (c : ℕ → ℝ) (m : ℕ) (k : Fin m) :
    coefficientMatrix c m m k k = 1 := by
  rw [coefficientMatrix_final]
  simpa [nestedPolynomial_degree] using (nestedPolynomial_monic c k.val).coeff_natDegree

theorem coefficientMatrix_principal_det (c : ℕ → ℝ) {r m : ℕ}
    (k : Fin r → Fin m) (hk : StrictMono k) :
    ((coefficientMatrix c m m).submatrix k k).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [Matrix.submatrix_apply, coefficientMatrix_diagonal]
  · intro i j hij
    exact coefficientMatrix_triangular c m (hk hij)

theorem nestedPolynomial_eval_finite (c : ℕ → ℝ) (m : ℕ) (k : Fin m) (s : ℝ) :
    (nestedPolynomial c k.val).eval s =
      ∑ d : Fin m, s ^ d.val * coefficientMatrix c m m k d := by
  simp_rw [coefficientMatrix_final]
  rw [Fin.sum_univ_eq_sum_range (fun d => s ^ d * (nestedPolynomial c k.val).coeff d) m]
  rw [Polynomial.eval_eq_sum_range' (n := m) (by simp [nestedPolynomial_degree]) s]
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- Every selected-degree minor of the nested-product basis is strictly positive. -/
theorem nestedPolynomial_minors_pos (c : ℕ → ℝ) (hc : ∀ j, 0 ≤ c j)
    {r m : ℕ} (s : Fin r → ℝ) (hs : StrictMono s) (hpos : ∀ i, 0 < s i)
    (k : Fin r → Fin m) (hk : StrictMono k) :
    0 < Matrix.det (fun i j => (nestedPolynomial c (k j).val).eval (s i)) := by
  let A : Matrix (Fin r) (Fin m) ℝ := fun i d => s i ^ d.val
  let B : Matrix (Fin m) (Fin r) ℝ := fun d j => coefficientMatrix c m m (k j) d
  have he : (fun i j => (nestedPolynomial c (k j).val).eval (s i)) = A * B := by
    ext i j
    exact nestedPolynomial_eval_finite c m (k j) (s i)
  rw [he]
  have ha : ∀ g : Fin r → Fin m, StrictMono g → 0 < (A.submatrix id g).det := by
    intro g hg
    exact generalizedVandermonde_pos s (fun i => (g i).val) hs hpos (fun _ _ h => hg h)
  have hb : ∀ g : Fin r → Fin m, StrictMono g → 0 ≤ (B.submatrix g id).det := by
    intro g hg
    have hc' := coefficientMatrix_totallyNonneg c hc m m hk hg
    rw [← Matrix.det_transpose]
    exact hc'
  have hsum : 0 < ∑ f : Fin r → Fin m, (A.submatrix id f).det * (B.submatrix f id).det := by
    apply Finset.sum_pos'
    · intro f _; exact minor_product_nonneg A B (fun g hg => (ha g hg).le) hb f
    · refine ⟨k, Finset.mem_univ _, ?_⟩
      have hbk : (B.submatrix k id).det = 1 := by
        rw [← Matrix.det_transpose]
        exact coefficientMatrix_principal_det c k hk
      rw [hbk, mul_one]
      exact ha k hk
  rw [← cauchyBinet_unordered A B] at hsum
  exact pos_of_mul_pos_right hsum (by positivity)

end ReciprocalQGamma
