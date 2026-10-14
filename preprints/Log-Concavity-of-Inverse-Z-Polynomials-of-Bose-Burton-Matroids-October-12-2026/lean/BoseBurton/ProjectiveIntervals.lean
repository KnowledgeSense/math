import BoseBurton.IntervalInvariants

noncomputable section
namespace BoseBurton
open Submodule Module MatroidInverseZ
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The full projective upper interval is the subspace lattice of the quotient. -/
theorem quotientSpace_fills (U : Submodule K V) (A B : Submodule K (V ⧸ U))
    (F : Submodule K V) (hA : U.comapMkQOrderEmbedding A ≤ F)
    (_hB : F ≤ U.comapMkQOrderEmbedding B) :
    ∃ S, U.comapMkQOrderEmbedding S = F := by
  have hUF : U ≤ F := (le_comap_mkQ U A).trans hA
  refine ⟨F.map U.mkQ, ?_⟩
  change (F.map U.mkQ).comap U.mkQ = F
  rw [comap_map_mkQ, sup_eq_right.mpr hUF]

/-- The full projective lower interval is the subspace lattice of the subspace. -/
theorem subspaceSpace_fills (U : Submodule K V) (A B : Submodule K U)
    (F : Submodule K V) (_hA : MapSubtype.orderEmbedding U A ≤ F)
    (hB : F ≤ MapSubtype.orderEmbedding U B) :
    ∃ S, MapSubtype.orderEmbedding U S = F := by
  have hFU : F ≤ U := hB.trans (map_subtype_le U B)
  refine ⟨F.comap U.subtype, ?_⟩
  change (F.comap U.subtype).map U.subtype = F
  rw [map_comap_subtype, inf_eq_right.mpr hFU]

variable [Module.Finite K V] [Finite V]

theorem projective_upper_kl (U : Submodule K V) :
    kl (fun S : Submodule K V => finrank K S) ⊤ U = projectiveP K (V ⧸ U) := by
  classical
  have h := kl_interval_transport U.comapMkQOrderEmbedding (quotientSpace_fills U)
    (fun S : Submodule K (V ⧸ U) => finrank K S)
    (fun S : Submodule K V => finrank K S) (finrank_comap_mkQ_sub U) ⊥ ⊤
  change kl (fun S : Submodule K V => finrank K S)
    ((⊤ : Submodule K (V ⧸ U)).comap U.mkQ)
    ((⊥ : Submodule K (V ⧸ U)).comap U.mkQ) = _ at h
  rw [comap_top, show (⊥ : Submodule K (V ⧸ U)).comap U.mkQ = U from U.ker_mkQ] at h
  exact h

theorem projective_upper_inverseZ (U : Submodule K V) :
    inverseZ (fun S : Submodule K V => finrank K S) U ⊤ = projectiveY K (V ⧸ U) := by
  classical
  have h := inverseZ_interval_transport U.comapMkQOrderEmbedding (quotientSpace_fills U)
    (fun S : Submodule K (V ⧸ U) => finrank K S)
    (fun S : Submodule K V => finrank K S) (finrank_comap_mkQ_sub U) ⊥ ⊤
  change inverseZ (fun S : Submodule K V => finrank K S)
    ((⊥ : Submodule K (V ⧸ U)).comap U.mkQ)
    ((⊤ : Submodule K (V ⧸ U)).comap U.mkQ) = _ at h
  rw [comap_top, show (⊥ : Submodule K (V ⧸ U)).comap U.mkQ = U from U.ker_mkQ] at h
  exact h

omit [Module.Finite K V] in
theorem projective_lower_inverseKL (U : Submodule K V) :
    inverseKL (fun S : Submodule K V => finrank K S) ⊥ U =
      inverseKL (fun S : Submodule K U => finrank K S) ⊥ ⊤ := by
  classical
  have hr (S : Submodule K U) : finrank K (MapSubtype.orderEmbedding U S) = finrank K S :=
    (Submodule.equivMapOfInjective U.subtype U.subtype_injective S).finrank_eq.symm
  have h := inverseKL_interval_transport (MapSubtype.orderEmbedding U) (subspaceSpace_fills U)
    (fun S : Submodule K U => finrank K S) (fun S : Submodule K V => finrank K S)
    (fun a b => by rw [hr a, hr b]) ⊥ ⊤
  change inverseKL (fun S : Submodule K V => finrank K S)
    ((⊥ : Submodule K U).map U.subtype) ((⊤ : Submodule K U).map U.subtype) = _ at h
  rw [Submodule.map_bot, Submodule.map_top, Submodule.range_subtype] at h
  exact h

end BoseBurton
