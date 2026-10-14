import BoseBurton.ProjectiveEvaluationIntervals

noncomputable section
open scoped Classical
namespace BoseBurton
open Submodule Module Finset Polynomial MatroidInverseZ IncidenceAlgebra
variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V] [Finite V]

theorem projective_zKernel_top :
    zKernel (fun S : Submodule K V=>finrank K S) ⊥ ⊤=projectiveRankEnumerator K V := by
  classical
  rw [zKernel_apply]
  simp only [finrank_bot,Nat.sub_zero,Icc_bot_top,projectiveRankEnumerator]
  apply sum_congr rfl
  intro U _
  rw [projective_interval_kl U ⊤ le_top,mul_one]

theorem projectiveY_mobius_sum :
    projectiveY K V=∑ U : Submodule K V,
      C ((-1:ℤ)^(finrank K V)*IncidenceAlgebra.mu ℤ (⊥ : Submodule K V) U*
        IncidenceAlgebra.mu ℤ U (⊤ : Submodule K V))*X^(finrank K V-finrank K U) := by
  classical
  unfold projectiveY
  rw [inverseZ_eq_signed_product _ (fun _ _ h=>Submodule.finrank_mono h),projective_klInverseKernel,
    IncidenceAlgebra.mul_apply]
  simp only [finrank_top,finrank_bot,Nat.sub_zero,Icc_bot_top,mul_sum]
  apply sum_congr rfl
  intro U _
  change C ((-1:ℤ)^(finrank K V))*(C (IncidenceAlgebra.mu ℤ (⊥ : Submodule K V) U)*
    (C (IncidenceAlgebra.mu ℤ U (⊤ : Submodule K V))*X^(finrank K (⊤ : Submodule K V)-finrank K U)))=_
  rw [finrank_top]
  simp only [map_mul]
  ring

end BoseBurton
