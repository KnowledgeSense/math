import MainTheorems.DiagonalSchatten.CompressionHessian

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped Matrix.Norms.Elementwise Topology

variable {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]

omit [DecidableEq J] [Nonempty J] in
theorem realEntryRoot_positive_gramDet_scale {p t : ℝ} (ht : 0 < t)
    (B : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (hdet : 0 < gramFirst (realEntryRoot p B) * gramSecond (realEntryRoot p B) -
      gramCross (realEntryRoot p B) ^ 2) :
    0 < gramFirst (realEntryRoot p (t • B)) * gramSecond (realEntryRoot p (t • B)) -
      gramCross (realEntryRoot p (t • B)) ^ 2 := by
  rw [realEntryRoot_smul ht.le B hB, gramFirst_smul, gramSecond_smul, gramCross_smul]
  have he : (t ^ (1 / p)) ^ 2 * gramFirst (realEntryRoot p B) *
      ((t ^ (1 / p)) ^ 2 * gramSecond (realEntryRoot p B)) -
        ((t ^ (1 / p)) ^ 2 * gramCross (realEntryRoot p B)) ^ 2 =
      ((t ^ (1 / p)) ^ 2) ^ 2 * (gramFirst (realEntryRoot p B) *
        gramSecond (realEntryRoot p B) - gramCross (realEntryRoot p B) ^ 2) := by ring
  rw [he]
  exact mul_pos (pow_pos (pow_pos (Real.rpow_pos_of_pos ht _) _) _) hdet

theorem compressionHessian_scale {p t : ℝ} (hp : 1 < p) (ht : 0 < t)
    (B E : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 < B i j)
    (hdet : 0 < gramFirst (realEntryRoot p B) * gramSecond (realEntryRoot p B) -
      gramCross (realEntryRoot p B) ^ 2) :
    t • compressionHessian p (t • B) E = compressionHessian p B E := by
  have hBt : ∀ i j, 0 < (t • B) i j := by
    intro i j
    exact mul_pos ht (hB i j)
  have hdetT := realEntryRoot_positive_gramDet_scale ht B (fun i j => (hB i j).le) hdet
  have h2 := contDiffAt_compressionFunctional_fullRank (n := 2) (by linarith : 0 < p) B hB hdet
  have h2T := contDiffAt_compressionFunctional_fullRank (n := 2) (by linarith : 0 < p)
    (t • B) hBt hdetT
  have hd : DifferentiableAt ℝ (fderiv ℝ (compressionFunctional p)) B :=
    (h2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdT : DifferentiableAt ℝ (fderiv ℝ (compressionFunctional p)) (t • B) :=
    (h2T.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  ext F
  have hleft := (hdT.hasFDerivAt.clm_apply (hasFDerivAt_const F (t • B))).comp B
    (t • ContinuousLinearMap.id ℝ (Matrix (Fin 2) J ℝ)).hasFDerivAt
  have hright := hd.hasFDerivAt.clm_apply (hasFDerivAt_const F B)
  have heq : (fun Y => fderiv ℝ (compressionFunctional p) Y F) =ᶠ[𝓝 B]
      (fun Y => fderiv ℝ (compressionFunctional p) (t • Y) F) := by
    filter_upwards [positive_arrays_open.mem_nhds hB] with Y hY
    exact congrArg (fun L : Matrix (Fin 2) J ℝ →L[ℝ] ℝ => L F)
      (compressionFunctional_fderiv_scale hp ht Y hY).symm
  have hm := (hleft.congr_of_eventuallyEq heq).unique hright
  have he := congrArg
    (fun L : Matrix (Fin 2) J ℝ →L[ℝ] ℝ => L E) hm
  change fderiv ℝ (compressionFunctional p) (t • B) 0 +
      compressionHessian p (t • B) (t • E) F =
    fderiv ℝ (compressionFunctional p) B 0 + compressionHessian p B E F at he
  simpa only [map_zero, zero_add, map_smul, smul_apply, smul_eq_mul] using he

end

end ResearchMain.DiagonalSchatten
