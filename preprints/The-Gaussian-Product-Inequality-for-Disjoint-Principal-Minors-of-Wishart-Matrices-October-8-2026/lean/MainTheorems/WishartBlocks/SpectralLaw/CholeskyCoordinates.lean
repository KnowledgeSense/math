import MainTheorems.WishartBlocks.SpectralLaw.CholeskyJacobian
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Instances.Matrix

namespace ResearchMain.WishartBlocks

open scoped BigOperators

noncomputable def lowerEntry {n : ℕ} (i j : Fin n) :
    (LowerIndex n → ℝ) →L[ℝ] ℝ :=
  if h : j ≤ i then ContinuousLinearMap.proj ⟨toLex (i, j), h⟩ else 0

noncomputable def lowerMatrix {n : ℕ} (x : LowerIndex n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => lowerEntry i j x

@[fun_prop] theorem continuous_lowerMatrix (n : ℕ) :
    Continuous (lowerMatrix (n := n)) :=
  continuous_pi fun i => continuous_pi fun j => (lowerEntry i j).continuous

theorem lowerMatrix_lowerTriangular {n : ℕ} (x : LowerIndex n → ℝ) :
    (lowerMatrix x).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  simp only [lowerMatrix, lowerEntry, not_le_of_gt hij, dite_false,
    zero_apply]

@[simp] theorem lowerIndex_from_projection {n : ℕ} (e : LowerIndex n) :
    (⟨toLex (e.val.1, e.val.2), e.property⟩ : LowerIndex n) = e := by
  apply Subtype.ext
  exact Prod.ext rfl rfl

@[simp] theorem lowerMatrix_entry {n : ℕ} (x : LowerIndex n → ℝ) (e : LowerIndex n) :
    lowerMatrix x e.val.1 e.val.2 = x e := by
  simp only [lowerMatrix, lowerEntry, e.property, dite_true,
    ContinuousLinearMap.proj_apply, lowerIndex_from_projection]

noncomputable def choleskyCoordinates {n : ℕ} (x : LowerIndex n → ℝ) :
    LowerIndex n → ℝ := fun e =>
  (lowerMatrix x * (lowerMatrix x).transpose) e.val.1 e.val.2

noncomputable def choleskyDerivative {n : ℕ} (x : LowerIndex n → ℝ) :
    (LowerIndex n → ℝ) →L[ℝ] (LowerIndex n → ℝ) :=
  ContinuousLinearMap.pi fun e =>
    ∑ k : Fin n, ((lowerEntry e.val.1 k x) • lowerEntry e.val.2 k +
      (lowerEntry e.val.2 k x) • lowerEntry e.val.1 k)

theorem choleskyCoordinates_hasFDerivAt {n : ℕ} (x : LowerIndex n → ℝ) :
    HasFDerivAt choleskyCoordinates (choleskyDerivative x) x := by
  unfold choleskyDerivative
  apply hasFDerivAt_pi.mpr
  intro e
  have h := HasFDerivAt.fun_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) =>
    ((lowerEntry e.val.1 k).hasFDerivAt (x := x)).mul
      ((lowerEntry e.val.2 k).hasFDerivAt (x := x)))
  simpa only [choleskyCoordinates, lowerMatrix, Matrix.mul_apply,
    Matrix.transpose_apply, Pi.mul_apply] using h

theorem lowerEntry_apply_single {n : ℕ} (i j : Fin n) (f : LowerIndex n) :
    lowerEntry i j (Pi.single f (1 : ℝ)) =
      if i = f.val.1 ∧ j = f.val.2 then 1 else 0 := by
  by_cases he : i = f.val.1 ∧ j = f.val.2
  · rcases he with ⟨rfl, rfl⟩
    simp only [lowerEntry, f.property, dite_true,
      ContinuousLinearMap.proj_apply, lowerIndex_from_projection,
      Pi.single_eq_same, ite_true, and_self]
  · rw [ite_eq_right he]
    unfold lowerEntry
    split_ifs with hj
    · have hneq : f ≠ ⟨toLex (i, j), hj⟩ := by
        intro h
        apply he
        exact ⟨(congrArg (fun e : LowerIndex n => e.val.1) h).symm,
          (congrArg (fun e : LowerIndex n => e.val.2) h).symm⟩
      simp only [ContinuousLinearMap.proj_apply, Pi.single_apply, Ne.symm hneq, ite_false]
    · exact zero_apply _

theorem sum_lowerEntry_single {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) (f : LowerIndex n) :
    (∑ k : Fin n, L i k * lowerEntry j k (Pi.single f (1 : ℝ))) =
      if j = f.val.1 then L i f.val.2 else 0 := by
  simp_rw [lowerEntry_apply_single]
  by_cases hj : j = f.val.1
  · simp [hj]
  · simp [hj]

theorem choleskyDerivative_toMatrix {n : ℕ} (x : LowerIndex n → ℝ) :
    LinearMap.toMatrix' (choleskyDerivative x).toLinearMap =
      choleskyJacobian (lowerMatrix x) := by
  ext e f
  rw [LinearMap.toMatrix'_apply]
  change choleskyDerivative x (Pi.single f (1 : ℝ)) e = _
  rw [choleskyDerivative, ContinuousLinearMap.pi_apply]
  simp only [sum_apply, add_apply, smul_apply, smul_eq_mul]
  change (∑ k : Fin n,
    (lowerMatrix x e.val.1 k * lowerEntry e.val.2 k (Pi.single f 1) +
      lowerMatrix x e.val.2 k * lowerEntry e.val.1 k (Pi.single f 1))) = _
  rw [Finset.sum_add_distrib, sum_lowerEntry_single, sum_lowerEntry_single]
  exact add_comm _ _

theorem choleskyDerivative_det {n : ℕ} (x : LowerIndex n → ℝ) :
    (LinearMap.toMatrix' (choleskyDerivative x).toLinearMap).det =
      ∏ e : LowerIndex n,
        if e.val.1 = e.val.2 then 2 * lowerMatrix x e.val.2 e.val.2
          else lowerMatrix x e.val.2 e.val.2 := by
  rw [choleskyDerivative_toMatrix,
    choleskyJacobian_det (lowerMatrix_lowerTriangular x)]

end ResearchMain.WishartBlocks
