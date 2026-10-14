import BoseBurton.ProjectiveEvaluation

noncomputable section
open scoped Classical
namespace BoseBurton
open Submodule Module Finset Polynomial MatroidInverseZ IncidenceAlgebra
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V] [Finite V]

theorem projective_interval_kl (A B : Submodule K V) (hab : A≤B) :
    kl (fun S : Submodule K V=>finrank K S) B A=1 := by
  classical
  have hr (S : Submodule K B) : finrank K (MapSubtype.orderEmbedding B S)=finrank K S :=
    (Submodule.equivMapOfInjective B.subtype B.subtype_injective S).finrank_eq.symm
  have h := kl_interval_transport (MapSubtype.orderEmbedding B) (subspaceSpace_fills B)
    (fun S : Submodule K B=>finrank K S) (fun S : Submodule K V=>finrank K S)
    (fun a b=>by rw [hr a,hr b]) (A.comap B.subtype) ⊤
  change kl (fun S : Submodule K V=>finrank K S)
    ((⊤ : Submodule K B).map B.subtype) ((A.comap B.subtype).map B.subtype)=_ at h
  rw [Submodule.map_top,range_subtype,map_comap_subtype,inf_eq_right.mpr hab] at h
  rw [h,projective_upper_kl,projectiveP_eq_one]

theorem projective_klKernel :
    klKernel (fun S : Submodule K V=>finrank K S)=IncidenceAlgebra.zeta (Polynomial ℤ) := by
  classical
  apply IncidenceAlgebra.ext
  intro A B hab
  rw [klKernel_apply,projective_interval_kl A B hab,zeta_of_le hab]

theorem projective_klInverseKernel :
    klInverseKernel (fun S : Submodule K V=>finrank K S)=constantMu := by
  classical
  have hmu : (constantMu*IncidenceAlgebra.zeta (Polynomial ℤ) :
      IncidenceAlgebra (Polynomial ℤ) (Submodule K V))=1 := by
    apply incidence_rightInverse_of_leftInverse _ _ _ zeta_mul_constantMu
    intro U
    simp [constantMu]
  apply incidence_leftInverse_unique (IncidenceAlgebra.zeta (Polynomial ℤ))
  · intro U
    simp
  · rw [← projective_klKernel (K:=K) (V:=V),klInverseKernel_mul_klKernel]
  · exact hmu

end BoseBurton
