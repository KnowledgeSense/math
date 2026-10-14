import MainTheorems.Chollet.GramExpansion
import Mathlib.Algebra.MvPolynomial.Expand

noncomputable section

namespace ResearchMain.Chollet

open MvPolynomial

variable {I J K : Type*} [Fintype I] [Fintype J] [DecidableEq I]

def weightedGram (Q : Matrix I J ℂ) (w : J → K →₀ ℕ) :
    Matrix I I (MvPolynomial K ℂ) :=
  fun i j => ∑ a, monomial (w a + w a) (Q i a * star (Q j a))

theorem permanent_monomial_columns (Q : Matrix I I ℂ) (w : I → K →₀ ℕ) :
    Matrix.permanent (fun i j => monomial (w j) (Q i j)) =
      monomial (∑ j, w j) Q.permanent := by
  simp only [Matrix.permanent, ← monomial_sum_prod]
  exact (map_sum (monomial (∑ j, w j)) _ _).symm

theorem permanent_weightedGram (Q : Matrix I J ℂ) (w : J → K →₀ ℕ) :
    (Fintype.card (Equiv.Perm I) : MvPolynomial K ℂ) * (weightedGram Q w).permanent =
      ∑ f : I → J, monomial ((∑ i, w (f i)) + ∑ i, w (f i))
        (((‖(Q.submatrix id f).permanent‖ ^ 2 : ℝ) : ℂ)) := by
  let S : Matrix I J (MvPolynomial K ℂ) := fun i j => monomial (w j) (Q i j)
  let T : Matrix J I (MvPolynomial K ℂ) := fun j i => monomial (w j) (star (Q i j))
  have hm : S * T = weightedGram Q w := by
    funext i j
    change (∑ a, monomial (w a) (Q i a) * monomial (w a) (star (Q j a))) = _
    simp only [weightedGram, monomial_mul_monomial]
  have h := permanent_mul_symmetrized S T
  rw [hm] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro f _
  have hs : (S.submatrix id f).permanent =
      monomial (∑ i, w (f i)) (Q.submatrix id f).permanent :=
    permanent_monomial_columns (Q.submatrix id f) (w ∘ f)
  have ht : (T.submatrix f id).permanent =
      monomial (∑ i, w (f i)) (star (Q.submatrix id f).permanent) := by
    rw [← Matrix.permanent_transpose]
    have he : (T.submatrix f id).transpose =
        fun i j => monomial (w (f j)) (conjugate (Q.submatrix id f) i j) := rfl
    rw [he, permanent_monomial_columns, permanent_conjugate]
  rw [hs, ht, monomial_mul_monomial]
  simp only [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem weightedGram_coeff_nonneg (Q : Matrix I J ℂ) (w : J → K →₀ ℕ)
    (d : K →₀ ℕ) : 0 ≤ ((weightedGram Q w).permanent.coeff d).re := by
  classical
  have h := congrArg (fun p : MvPolynomial K ℂ => (p.coeff d).re)
    (permanent_weightedGram Q w)
  have hc : (0 : ℝ) < Fintype.card (Equiv.Perm I) := by exact_mod_cast Fintype.card_pos
  have hs : (0 : ℝ) ≤
      ((∑ f : I → J, monomial ((∑ i, w (f i)) + ∑ i, w (f i))
        (((‖(Q.submatrix id f).permanent‖ ^ 2 : ℝ) : ℂ))).coeff d).re := by
    simp only [coeff_sum, Complex.re_sum, coeff_monomial]
    apply Finset.sum_nonneg
    intro f _
    split_ifs <;> simp [-Complex.ofReal_pow]
  have hn : (Fintype.card (Equiv.Perm I) : MvPolynomial K ℂ) =
      C (Fintype.card (Equiv.Perm I) : ℂ) := by simp
  rw [hn, coeff_C_mul] at h
  have he : ((Fintype.card (Equiv.Perm I) : ℂ) *
      (weightedGram Q w).permanent.coeff d).re =
      (Fintype.card (Equiv.Perm I) : ℝ) * ((weightedGram Q w).permanent.coeff d).re := by
    simp
  rw [he] at h
  rw [← h] at hs
  exact nonneg_of_mul_nonneg_right hs hc

theorem weightedGram_coeff_im_zero (Q : Matrix I J ℂ) (w : J → K →₀ ℕ)
    (d : K →₀ ℕ) : ((weightedGram Q w).permanent.coeff d).im = 0 := by
  classical
  have h := congrArg (fun p : MvPolynomial K ℂ => (p.coeff d).im)
    (permanent_weightedGram Q w)
  have hr :
      ((∑ f : I → J, monomial ((∑ i, w (f i)) + ∑ i, w (f i))
        (((‖(Q.submatrix id f).permanent‖ ^ 2 : ℝ) : ℂ))).coeff d).im = 0 := by
    simp only [coeff_sum, Complex.im_sum, coeff_monomial]
    apply Finset.sum_eq_zero
    intro f _
    split_ifs <;> simp [-Complex.ofReal_pow]
  have hn : (Fintype.card (Equiv.Perm I) : MvPolynomial K ℂ) =
      C (Fintype.card (Equiv.Perm I) : ℂ) := by simp
  rw [hn, coeff_C_mul] at h
  have he : (Fintype.card (Equiv.Perm I) : ℝ) *
      ((weightedGram Q w).permanent.coeff d).im = 0 := by
    simpa using h.trans hr
  have hc : (Fintype.card (Equiv.Perm I) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact (mul_eq_zero.mp he).resolve_left hc

end ResearchMain.Chollet
