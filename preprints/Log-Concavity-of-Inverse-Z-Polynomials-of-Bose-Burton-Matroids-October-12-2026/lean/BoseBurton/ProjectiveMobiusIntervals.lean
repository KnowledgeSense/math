import BoseBurton.ProjectiveMobius

noncomputable section
open scoped Classical
namespace BoseBurton
open Submodule Module MatroidInverseZ IncidenceAlgebra
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype K] [Module.Finite K V] [Finite V]

omit [Fintype K] [Module.Finite K V] in
theorem projective_upper_mu (U : Submodule K V) :
    IncidenceAlgebra.mu ℤ U (⊤ : Submodule K V)=
      IncidenceAlgebra.mu ℤ (⊥ : Submodule K (V ⧸ U)) ⊤ := by
  classical
  have h := mu_interval_transport U.comapMkQOrderEmbedding (quotientSpace_fills U) ⊥ ⊤
  change IncidenceAlgebra.mu ℤ ((⊥ : Submodule K (V ⧸ U)).comap U.mkQ)
    ((⊤ : Submodule K (V ⧸ U)).comap U.mkQ)=_ at h
  simpa only [comap_top,show (⊥ : Submodule K (V ⧸ U)).comap U.mkQ=U from U.ker_mkQ] using h

theorem projective_lower_mu_formula (U : Submodule K V) :
    (IncidenceAlgebra.mu ℤ (⊥ : Submodule K V) U:ℝ)=
      (-1:ℝ)^(finrank K U)*(Fintype.card K:ℝ)^((finrank K U).choose 2) := by
  rw [projective_lower_mu,projective_mu_formula K U]

theorem projective_upper_mu_formula (U : Submodule K V) :
    (IncidenceAlgebra.mu ℤ U (⊤ : Submodule K V):ℝ)=
      (-1:ℝ)^(finrank K V-finrank K U)*(Fintype.card K:ℝ)^((finrank K V-finrank K U).choose 2) := by
  rw [projective_upper_mu,projective_mu_formula K (V ⧸ U)]
  have h := Submodule.finrank_quotient_add_finrank U
  rw [show finrank K (V ⧸ U)=finrank K V-finrank K U by omega]

end BoseBurton
