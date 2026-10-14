import MainTheorems.DiagonalSchatten.PositiveDeterminantHessian

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise Topology

def exchangeColumns (B : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i => ![B i 1, B i 0]

def exchangeColumnsMap :
    Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := exchangeColumns
    map_add' := by intro B C; ext i j; fin_cases j <;> simp [exchangeColumns]
    map_smul' := by intro t B; ext i j; fin_cases j <;> simp [exchangeColumns]
  }

theorem exchangeColumns_involutive (B : Matrix (Fin 2) (Fin 2) ℝ) :
    exchangeColumns (exchangeColumns B) = B := by
  ext i j
  fin_cases j <;> rfl

theorem realEntryRoot_exchangeColumns (p : ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ) :
    realEntryRoot p (exchangeColumns B) = exchangeColumns (realEntryRoot p B) := by
  ext i j
  fin_cases j <;> rfl

theorem exchangeColumns_gram (B : Matrix (Fin 2) (Fin 2) ℝ) :
    gramFirst (exchangeColumns B) = gramFirst B ∧
    gramSecond (exchangeColumns B) = gramSecond B ∧
    gramCross (exchangeColumns B) = gramCross B := by
  simp only [gramFirst, gramSecond, gramCross, exchangeColumns, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · ring
  constructor <;> ring

theorem exchangeColumns_det (B : Matrix (Fin 2) (Fin 2) ℝ) :
    (exchangeColumns B).det = -B.det := by
  simp only [Matrix.det_fin_two, exchangeColumns, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem compressionFunctional_exchangeColumns {p : ℝ} (hp : 0 < p)
    (B : Matrix (Fin 2) (Fin 2) ℝ) :
    compressionFunctional p (exchangeColumns B) = compressionFunctional p B := by
  rw [compressionFunctional_eq_realEntryRoot, compressionFunctional_eq_realEntryRoot,
    realEntryRoot_exchangeColumns, schattenPower_complexify hp, schattenPower_complexify hp]
  obtain ⟨ha, hb, hc⟩ := exchangeColumns_gram (realEntryRoot p B)
  simp only [realGramPlus, realGramMinus, ha, hb, hc]

theorem exchangeColumns_positive (B : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : ∀ i j, 0 < B i j) : ∀ i j, 0 < exchangeColumns B i j := by
  intro i j
  fin_cases j
  · exact hB i 1
  · exact hB i 0

theorem fderiv_compressionFunctional_exchangeColumns {p : ℝ} (hp : 1 < p)
    (B E : Matrix (Fin 2) (Fin 2) ℝ) (hB : ∀ i j, 0 < B i j) :
    fderiv ℝ (compressionFunctional p) (exchangeColumns B) (exchangeColumns E) =
      fderiv ℝ (compressionFunctional p) B E := by
  have hd := (contDiffAt_compressionFunctional hp B hB).differentiableAt (by norm_num)
  have hdS := (contDiffAt_compressionFunctional hp (exchangeColumns B)
    (exchangeColumns_positive B hB)).differentiableAt (by norm_num)
  have hcomp := hdS.hasFDerivAt.comp B exchangeColumnsMap.hasFDerivAt
  have heq : compressionFunctional (J := Fin 2) p ∘ exchangeColumns = compressionFunctional p :=
    funext (compressionFunctional_exchangeColumns (by linarith : 0 < p))
  rw [heq] at hcomp
  have he := congrArg
    (fun L : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] ℝ => L E) (hcomp.unique hd.hasFDerivAt)
  exact he

theorem compressionHessian_exchangeColumns {p : ℝ} (hp : 1 < p)
    (B E F : Matrix (Fin 2) (Fin 2) ℝ) (hB : ∀ i j, 0 < B i j)
    (hdet : 0 < gramFirst (realEntryRoot p B) * gramSecond (realEntryRoot p B) -
      gramCross (realEntryRoot p B) ^ 2) :
    compressionHessian p (exchangeColumns B) (exchangeColumns E) (exchangeColumns F) =
      compressionHessian p B E F := by
  have hdetS : 0 < gramFirst (realEntryRoot p (exchangeColumns B)) *
      gramSecond (realEntryRoot p (exchangeColumns B)) -
        gramCross (realEntryRoot p (exchangeColumns B)) ^ 2 := by
    rw [realEntryRoot_exchangeColumns]
    obtain ⟨ha, hb, hc⟩ := exchangeColumns_gram (realEntryRoot p B)
    rw [ha, hb, hc]
    exact hdet
  have h2 := contDiffAt_compressionFunctional_fullRank (n := 2) (by linarith : 0 < p) B hB hdet
  have h2S := contDiffAt_compressionFunctional_fullRank (n := 2) (by linarith : 0 < p)
    (exchangeColumns B) (exchangeColumns_positive B hB) hdetS
  have hd := (h2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdS := (h2S.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hlocal : (fun Y : Matrix (Fin 2) (Fin 2) ℝ =>
      fderiv ℝ (compressionFunctional p) (exchangeColumns Y) (exchangeColumns F)) =ᶠ[𝓝 B]
      (fun Y => fderiv ℝ (compressionFunctional p) Y F) := by
    filter_upwards [positive_arrays_open.mem_nhds hB] with Y hY
    exact fderiv_compressionFunctional_exchangeColumns hp Y F hY
  have hleft := (hdS.hasFDerivAt.clm_apply
    (hasFDerivAt_const (exchangeColumns F) (exchangeColumns B))).comp B exchangeColumnsMap.hasFDerivAt
  have hright := hd.hasFDerivAt.clm_apply (hasFDerivAt_const F B)
  have he := congrArg (fun L : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] ℝ => L E)
    ((hleft.congr_of_eventuallyEq hlocal.symm).unique hright)
  change fderiv ℝ (compressionFunctional p) (exchangeColumns B) 0 +
      compressionHessian p (exchangeColumns B) (exchangeColumns E) (exchangeColumns F) =
    fderiv ℝ (compressionFunctional p) B 0 + compressionHessian p B E F at he
  simpa only [ContinuousLinearMap.map_zero, zero_add] using he

theorem twoByTwo_gramDet_eq_det_sq (M : Matrix (Fin 2) (Fin 2) ℝ) :
    gramFirst M * gramSecond M - gramCross M ^ 2 = M.det ^ 2 := by
  simp only [gramFirst, gramSecond, gramCross, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

theorem compressionHessian_two_column_kernel {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2)
    (B : Matrix (Fin 2) (Fin 2) ℝ) (hB : ∀ i j, 0 < B i j)
    (hdet : (realEntryRoot p B).det ≠ 0)
    (E : Matrix (Fin 2) (Fin 2) ℝ) (hE : compressionHessian p B E = 0) :
    ∃ r : ℝ, E = r • B := by
  rcases lt_or_gt_of_ne hdet with hn | hpD
  · have hGramDet : 0 < gramFirst (realEntryRoot p B) * gramSecond (realEntryRoot p B) -
        gramCross (realEntryRoot p B) ^ 2 := by
      rw [twoByTwo_gramDet_eq_det_sq]
      exact sq_pos_of_ne_zero hdet
    have hdetS : 0 < (realEntryRoot p (exchangeColumns B)).det := by
      rw [realEntryRoot_exchangeColumns, exchangeColumns_det]
      linarith
    have hES : compressionHessian p (exchangeColumns B) (exchangeColumns E) = 0 := by
      ext F
      have he := compressionHessian_exchangeColumns hp B E (exchangeColumns F) hB hGramDet
      rw [exchangeColumns_involutive, hE, zero_apply] at he
      exact he
    obtain ⟨r, hr⟩ := positive_determinant_compressionHessian_kernel hp hp2
      (exchangeColumns B) (exchangeColumns_positive B hB) hdetS (exchangeColumns E) hES
    refine ⟨r, ?_⟩
    have he := congrArg exchangeColumns hr
    change exchangeColumns (exchangeColumns E) =
      exchangeColumnsMap (r • exchangeColumns B) at he
    rw [map_smul, show exchangeColumnsMap (exchangeColumns B) = B by
      exact exchangeColumns_involutive B, exchangeColumns_involutive] at he
    exact he
  · exact positive_determinant_compressionHessian_kernel hp hp2 B hB hpD E hE

end

end ResearchMain.DiagonalSchatten
