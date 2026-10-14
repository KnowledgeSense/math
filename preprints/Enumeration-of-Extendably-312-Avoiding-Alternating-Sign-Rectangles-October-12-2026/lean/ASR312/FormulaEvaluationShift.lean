import ASR312.FormulaEvaluationSeries

noncomputable section
open PowerSeries
namespace ASR312

theorem B_subst_shift_cleared (a m : ℕ) (w : PowerSeries ℚ) (hw : HasSubst w) :
    (B ((a:ℤ)-m)).subst w*(1+w)^m=(1+w)^a := by
  have h := B_add ((a:ℤ)-m) (m:ℤ)
  rw [show (a:ℤ)-m+m=a by ring] at h
  rw [B_nat,B_nat] at h
  have hs := congrArg (substAlgHom hw) h
  simp only [map_mul,map_pow,map_add,map_one,coe_substAlgHom,subst_X hw] at hs
  exact hs.symm

end ASR312
