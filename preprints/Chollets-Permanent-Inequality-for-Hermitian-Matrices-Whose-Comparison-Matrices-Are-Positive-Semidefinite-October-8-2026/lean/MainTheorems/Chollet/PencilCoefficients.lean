import MainTheorems.Chollet.PolynomialGram
import MainTheorems.Chollet.Positivity

noncomputable section

open scoped ComplexOrder MatrixOrder

namespace ResearchMain.Chollet

open MvPolynomial

variable {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I]

theorem permanent_map_ringHom {R S : Type*} [CommSemiring R] [CommSemiring S]
    (A : Matrix I I R) (f : R →+* S) :
    f A.permanent = (A.map f).permanent := by
  simp only [Matrix.permanent, map_sum, map_prod, Matrix.map_apply]

def pencilPolynomial (P : K → Matrix I I ℂ) : MvPolynomial K ℂ :=
  Matrix.permanent (fun i j => ∑ k, C (P k i j) * X k)

theorem pencil_expand_eq_weightedGram (P : K → Matrix I I ℂ)
    (hP : ∀ k, (P k).PosSemidef) :
    expand 2 (pencilPolynomial P) =
      (weightedGram (fun i (a : K × I) => CFC.sqrt (P a.1) i a.2)
        (fun a => Finsupp.single a.1 1)).permanent := by
  classical
  let Q : Matrix I (K × I) ℂ := fun i a => CFC.sqrt (P a.1) i a.2
  let w : K × I → K →₀ ℕ := fun a => Finsupp.single a.1 1
  have hQ : ∀ k, CFC.sqrt (P k) * (CFC.sqrt (P k)).conjTranspose = P k := by
    intro k
    have hs : (CFC.sqrt (P k)).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (P k))
    rw [hs.isHermitian, ← sq, CFC.sq_sqrt (P k) (hP k).nonneg]
  have he : expand 2 (pencilPolynomial P) = (weightedGram Q w).permanent := by
    let A : Matrix I I (MvPolynomial K ℂ) := fun i j => ∑ k, C (P k i j) * X k
    have ha := permanent_map_ringHom A (expand 2).toRingHom
    change (expand 2).toRingHom A.permanent = _
    rw [ha]
    apply congrArg Matrix.permanent
    funext i j
    change expand 2 (∑ k, C (P k i j) * X k) = weightedGram Q w i j
    simp only [map_sum, map_mul, expand_C, expand_X,
      weightedGram, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro k _
    have hg := congrFun (congrFun (hQ k) i) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at hg
    change C (P k i j) * X k ^ 2 =
      ∑ a, monomial (Finsupp.single k 1 + Finsupp.single k 1)
        (CFC.sqrt (P k) i a * star (CFC.sqrt (P k) j a))
    rw [← map_sum, hg]
    rw [X_pow_eq_monomial, C_mul_monomial]
    simp only [mul_one, ← Finsupp.single_add]
  exact he

theorem pencil_coeff_nonneg (P : K → Matrix I I ℂ) (hP : ∀ k, (P k).PosSemidef)
    (d : K →₀ ℕ) : 0 ≤ ((pencilPolynomial P).coeff d).re := by
  classical
  have h := weightedGram_coeff_nonneg
    (fun i (a : K × I) => CFC.sqrt (P a.1) i a.2)
    (fun a => Finsupp.single a.1 1) (2 • d)
  rw [← pencil_expand_eq_weightedGram P hP, coeff_expand_smul 2 (by decide)] at h
  exact h

theorem pencil_coeff_im_zero (P : K → Matrix I I ℂ) (hP : ∀ k, (P k).PosSemidef)
    (d : K →₀ ℕ) : ((pencilPolynomial P).coeff d).im = 0 := by
  classical
  have h := weightedGram_coeff_im_zero
    (fun i (a : K × I) => CFC.sqrt (P a.1) i a.2)
    (fun a => Finsupp.single a.1 1) (2 • d)
  rw [← pencil_expand_eq_weightedGram P hP, coeff_expand_smul 2 (by decide)] at h
  exact h

end ResearchMain.Chollet
