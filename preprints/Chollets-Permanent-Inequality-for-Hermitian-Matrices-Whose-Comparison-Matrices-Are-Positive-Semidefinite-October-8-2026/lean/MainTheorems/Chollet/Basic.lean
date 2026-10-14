import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace ResearchMain.Chollet

variable {I : Type*} [Fintype I] [DecidableEq I]

def hadamard (A B : Matrix I I ℂ) : Matrix I I ℂ := fun i j => A i j * B i j

def conjugate (A : Matrix I I ℂ) : Matrix I I ℂ := fun i j => star (A i j)

noncomputable def squaredEntries (A : Matrix I I ℂ) : Matrix I I ℝ := fun i j => ‖A i j‖ ^ 2

noncomputable def comparison (A : Matrix I I ℂ) : Matrix I I ℝ :=
  fun i j => if i = j then (A i i).re else -‖A i j‖

def ComparisonPSD (A : Matrix I I ℂ) : Prop := A.IsHermitian ∧ (comparison A).PosSemidef

theorem permanent_conjugate (A : Matrix I I ℂ) : (conjugate A).permanent = star A.permanent := by
  simp [Matrix.permanent, conjugate]

theorem permanent_real {A : Matrix I I ℂ} (hA : A.IsHermitian) : A.permanent.im = 0 := by
  have hc : conjugate A = A.transpose := by
    ext i j
    exact hA.apply j i
  have hs : star A.permanent = A.permanent := by
    rw [← permanent_conjugate, hc, Matrix.permanent_transpose]
  have hi := congrArg Complex.im hs
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

theorem permanent_squaredEntries (A : Matrix I I ℂ) :
    (squaredEntries A).permanent = ∑ σ : Equiv.Perm I, ‖∏ i, A (σ i) i‖ ^ 2 := by
  simp only [squaredEntries, Matrix.permanent, norm_prod, Finset.prod_pow]

theorem permanent_hadamard_cauchySchwarz (A B : Matrix I I ℂ) :
    ‖(hadamard A B).permanent‖ ^ 2 ≤ (squaredEntries A).permanent * (squaredEntries B).permanent := by
  have hn : ‖(hadamard A B).permanent‖ ≤
      ∑ σ : Equiv.Perm I, ‖∏ i, A (σ i) i‖ * ‖∏ i, B (σ i) i‖ := by
    unfold Matrix.permanent hadamard
    simp only [Finset.prod_mul_distrib]
    simpa only [norm_mul] using norm_sum_le Finset.univ
      (fun σ : Equiv.Perm I => (∏ i, A (σ i) i) * (∏ i, B (σ i) i))
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun σ : Equiv.Perm I => ‖∏ i, A (σ i) i‖)
    (fun σ : Equiv.Perm I => ‖∏ i, B (σ i) i‖)
  rw [permanent_squaredEntries, permanent_squaredEntries]
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))).mpr hn
  exact hs.trans hc

end ResearchMain.Chollet
