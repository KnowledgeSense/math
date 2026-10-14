import BoseBurton.Definitions

noncomputable section
namespace BoseBurton
open Set Submodule Module
open scoped LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem rep_mk_mem_iff (S : Submodule K V) (v : V) (hv : v ≠ 0) :
    (Projectivization.mk K v hv).rep ∈ S ↔ v ∈ S := by
  rw [← Submodule.span_singleton_le_iff_mem, ← Projectivization.submodule_eq,
    Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem]

theorem pointsIn_subset_ground (W U : Submodule K V) : pointsIn W U ⊆ survivingPoints W :=
  fun _ h => h.2

theorem pointsIn_span_le (W U : Submodule K V) :
    vectorSpan (K := K) Projectivization.rep (pointsIn W U) ≤ U := by
  apply span_le.mpr
  rintro _ ⟨p, hp, rfl⟩
  exact hp.1

theorem surviving_vector_mem_span (W U : Submodule K V) (v : V)
    (hvU : v ∈ U) (hvW : v ∉ W) :
    v ∈ vectorSpan (K := K) Projectivization.rep (pointsIn W U) := by
  have hv : v ≠ 0 := fun h => hvW (h ▸ W.zero_mem)
  let p := Projectivization.mk K v hv
  have hp : p ∈ pointsIn W U :=
    ⟨(rep_mk_mem_iff U v hv).mpr hvU, fun h => hvW ((rep_mk_mem_iff W v hv).mp h)⟩
  have hr : p.rep ∈ vectorSpan (K := K) Projectivization.rep (pointsIn W U) :=
    subset_span ⟨p, hp, rfl⟩
  exact (rep_mk_mem_iff _ v hv).mp hr

/-- Every nonempty surviving projective subspace spans the whole original vector subspace. -/
theorem pointsIn_span (W U : Submodule K V) (hU : ¬ U ≤ W) :
    vectorSpan (K := K) Projectivization.rep (pointsIn W U) = U := by
  apply le_antisymm (pointsIn_span_le W U)
  obtain ⟨u, huU, huW⟩ := SetLike.not_le_iff_exists.mp hU
  intro v hvU
  by_cases hvW : v ∈ W
  · have huvW : u + v ∉ W := by
      intro h
      exact huW (by simpa using W.sub_mem h hvW)
    have hu := surviving_vector_mem_span W U u huU huW
    have huv := surviving_vector_mem_span W U (u + v) (U.add_mem huU hvU) huvW
    simpa using (vectorSpan (K := K) Projectivization.rep (pointsIn W U)).sub_mem huv hu
  · exact surviving_vector_mem_span W U v hvU hvW

theorem pointsIn_nonempty_iff (W U : Submodule K V) :
    (pointsIn W U).Nonempty ↔ ¬ U ≤ W := by
  constructor
  · rintro ⟨p, hp⟩ h
    exact hp.2 (h hp.1)
  · intro h
    obtain ⟨u, huU, huW⟩ := SetLike.not_le_iff_exists.mp h
    have hu : u ≠ 0 := fun h => huW (h ▸ W.zero_mem)
    refine ⟨Projectivization.mk K u hu, ?_⟩
    exact ⟨(rep_mk_mem_iff U u hu).mpr huU, fun h => huW ((rep_mk_mem_iff W u hu).mp h)⟩

theorem pointsIn_mono (W : Submodule K V) {U T : Submodule K V} (h : U ≤ T) :
    pointsIn W U ⊆ pointsIn W T := fun _ hp => ⟨h hp.1, hp.2⟩

theorem pointsIn_le_iff (W U T : Submodule K V) (hU : ¬ U ≤ W) :
    pointsIn W U ⊆ pointsIn W T ↔ U ≤ T := by
  refine ⟨fun h => ?_, pointsIn_mono W⟩
  rw [← pointsIn_span W U hU]
  exact (span_mono (Set.image_mono h)).trans (pointsIn_span_le W T)

end BoseBurton
