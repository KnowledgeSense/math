import MainTheorems.DiagonalSchatten.CompressionHomogeneity
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Operator.NormedSpace

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise Topology

variable {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]

omit [DecidableEq J] [Nonempty J] in
theorem positive_arrays_open :
    IsOpen {B : Matrix (Fin 2) J ℝ | ∀ i j, 0 < B i j} := by
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_lt continuous_const (by fun_prop)

theorem compressionFunctional_fderiv_scale {p t : ℝ} (hp : 1 < p) (ht : 0 < t)
    (B : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 < B i j) :
    fderiv ℝ (compressionFunctional p) (t • B) = fderiv ℝ (compressionFunctional p) B := by
  have hBt : ∀ i j, 0 < (t • B) i j := by
    intro i j
    change 0 < t * B i j
    exact mul_pos ht (hB i j)
  have hd := (contDiffAt_compressionFunctional hp B hB).differentiableAt (by norm_num)
  have hdt := (contDiffAt_compressionFunctional hp (t • B) hBt).differentiableAt (by norm_num)
  have hleft : HasFDerivAt (fun Y : Matrix (Fin 2) J ℝ => compressionFunctional p (t • Y))
      ((fderiv ℝ (compressionFunctional p) (t • B)).comp
        (t • ContinuousLinearMap.id ℝ (Matrix (Fin 2) J ℝ))) B := by
    convert! hdt.hasFDerivAt.comp B
      (t • ContinuousLinearMap.id ℝ (Matrix (Fin 2) J ℝ)).hasFDerivAt using 1
  have hright : HasFDerivAt (fun Y : Matrix (Fin 2) J ℝ => t * compressionFunctional p Y)
      (t • fderiv ℝ (compressionFunctional p) B) B := by
    convert! hd.hasFDerivAt.const_smul t using 1
  have heq : (fun Y : Matrix (Fin 2) J ℝ => t * compressionFunctional p Y) =ᶠ[𝓝 B]
      (fun Y => compressionFunctional p (t • Y)) := by
    filter_upwards [positive_arrays_open.mem_nhds hB] with Y hY
    exact (compressionFunctional_homogeneous (by linarith : 0 < p) ht.le Y
      (fun i j => (hY i j).le)).symm
  have hmaps := (hleft.congr_of_eventuallyEq heq).unique hright
  ext E
  have he := congrArg (fun L : Matrix (Fin 2) J ℝ →L[ℝ] ℝ => L E) hmaps
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    map_smul, smul_eq_mul] at he
  exact (mul_left_cancel₀ ht.ne') he

def compressionHessian (p : ℝ) (B : Matrix (Fin 2) J ℝ) :
    Matrix (Fin 2) J ℝ →L[ℝ] (Matrix (Fin 2) J ℝ →L[ℝ] ℝ) :=
  fderiv ℝ (fderiv ℝ (compressionFunctional p)) B

theorem compressionHessian_radial_zero {p : ℝ} (hp : 1 < p)
    (B : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 < B i j)
    (hdet : 0 < gramFirst (realEntryRoot p B) * gramSecond (realEntryRoot p B) -
      gramCross (realEntryRoot p B) ^ 2) : compressionHessian p B B = 0 := by
  have h2 := contDiffAt_compressionFunctional_fullRank (n := 2) (by linarith : 0 < p) B hB hdet
  have hd : DifferentiableAt ℝ (fderiv ℝ (compressionFunctional p)) B :=
    (h2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  ext E
  have hscalar := hd.hasFDerivAt.clm_apply (hasFDerivAt_const E B)
  have hcurve : HasDerivAt (fun t : ℝ => fderiv ℝ (compressionFunctional p) (t • B) E)
      (compressionHessian p B B E) 1 := by
    convert! hscalar.comp_hasDerivAt_of_eq 1
      ((hasDerivAt_id (1 : ℝ)).smul_const B) (by simp) using 1
    simp [compressionHessian]
    change fderiv ℝ (fderiv ℝ (compressionFunctional p)) B B E =
      fderiv ℝ (compressionFunctional p) B 0 +
        fderiv ℝ (fderiv ℝ (compressionFunctional p)) B B E
    rw [map_zero, zero_add]
  have heq : (fun t : ℝ => fderiv ℝ (compressionFunctional p) (t • B) E) =ᶠ[𝓝 (1 : ℝ)]
      (fun _ => fderiv ℝ (compressionFunctional p) B E) := by
    filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)] with t ht
    exact congrArg (fun L : Matrix (Fin 2) J ℝ →L[ℝ] ℝ => L E)
      (compressionFunctional_fderiv_scale hp ht B hB)
  exact hcurve.unique ((hasDerivAt_const (1 : ℝ)
    (fderiv ℝ (compressionFunctional p) B E)).congr_of_eventuallyEq heq)

theorem compressionHessian_symmetric {p : ℝ} (hp : 0 < p)
    (B : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 < B i j)
    (hdet : 0 < gramFirst (realEntryRoot p B) * gramSecond (realEntryRoot p B) -
      gramCross (realEntryRoot p B) ^ 2) (E F : Matrix (Fin 2) J ℝ) :
    compressionHessian p B E F = compressionHessian p B F E := by
  have h2 := contDiffAt_compressionFunctional_fullRank (n := 2) hp B hB hdet
  exact h2.isSymmSndFDerivAt (by norm_num [minSmoothness]) E F

end

end ResearchMain.DiagonalSchatten
