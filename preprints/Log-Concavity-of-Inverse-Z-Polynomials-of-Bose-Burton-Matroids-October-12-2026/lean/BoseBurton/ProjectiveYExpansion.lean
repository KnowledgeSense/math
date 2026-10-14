import BoseBurton.ProjectiveMobiusIntervals
import BoseBurton.ProjectiveEvaluationZ
import BoseBurton.OriginalKernel

noncomputable section
namespace BoseBurton
open Submodule Module Finset Polynomial
variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [Fintype K] [Module.Finite K V] [Finite V]

theorem projectiveY_real_expansion :
    (projectiveY K V).map (Int.castRingHom ℝ)=∑ U : Submodule K V,
      C ((Fintype.card K:ℝ)^((finrank K U).choose 2+(finrank K V-finrank K U).choose 2))*
        X^(finrank K V-finrank K U) := by
  classical
  rw [projectiveY_mobius_sum,Polynomial.map_sum]
  apply sum_congr rfl
  intro U _
  simp only [Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X]
  change C ((((-1:ℤ)^(finrank K V)*IncidenceAlgebra.mu ℤ (⊥ : Submodule K V) U*
    IncidenceAlgebra.mu ℤ U (⊤ : Submodule K V)):ℤ):ℝ)*X^(finrank K V-finrank K U)=_
  push_cast
  rw [projective_lower_mu_formula,projective_upper_mu_formula]
  have he : finrank K U+(finrank K V-finrank K U)=finrank K V := Nat.add_sub_of_le (Submodule.finrank_le U)
  have hs : (-1:ℝ)^(finrank K V)*(-1)^(finrank K U)*(-1)^(finrank K V-finrank K U)=1 := by
    rw [mul_assoc,← pow_add,he]
    exact signed_square _
  have hscalar : (-1:ℝ)^(finrank K V)*
      ((-1:ℝ)^(finrank K U)*(Fintype.card K:ℝ)^((finrank K U).choose 2))*
      ((-1:ℝ)^(finrank K V-finrank K U)*(Fintype.card K:ℝ)^((finrank K V-finrank K U).choose 2))=
      (Fintype.card K:ℝ)^((finrank K U).choose 2+(finrank K V-finrank K U).choose 2) := by
    rw [pow_add]
    linear_combination (Fintype.card K:ℝ)^((finrank K U).choose 2)*
      (Fintype.card K:ℝ)^((finrank K V-finrank K U).choose 2)*hs
  rw [hscalar]

end BoseBurton
