import BoseBurton.Geometry

noncomputable section
namespace BoseBurton
open Set Submodule Module
open scoped LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V] [Finite V]

theorem pointsIn_isFlat (W U : Submodule K V) : (matroid W).IsFlat (pointsIn W U) := by
  apply Matroid.isFlat_iff_closure_eq.mpr
  apply Set.Subset.antisymm
  · intro p hp
    have h := (matroid_mem_closure W _ (pointsIn_subset_ground W U) p).mp hp
    exact ⟨pointsIn_span_le W U h.1, h.2⟩
  · exact (matroid W).subset_closure _ (pointsIn_subset_ground W U)

theorem flat_eq_pointsIn_span (W : Submodule K V) {F : Set (ℙ K V)}
    (hF : (matroid W).IsFlat F) :
    F = pointsIn W (vectorSpan (K := K) Projectivization.rep F) := by
  ext p
  conv_lhs => rw [← hF.closure]
  exact matroid_mem_closure W F hF.subset_ground p

theorem flat_span_not_le (W : Submodule K V) {F : Set (ℙ K V)}
    (hF : (matroid W).IsFlat F) (hne : F.Nonempty) :
    ¬ vectorSpan (K := K) Projectivization.rep F ≤ W := by
  obtain ⟨p, hp⟩ := hne
  intro h
  exact hF.subset_ground hp (h (subset_span ⟨p, hp, rfl⟩))

/-- Exact classification of every nonempty flat by its surviving vector subspace. -/
theorem nonempty_flat_iff (W : Submodule K V) (F : Set (ℙ K V)) :
    (matroid W).IsFlat F ∧ F.Nonempty ↔
      ∃ U : Submodule K V, ¬ U ≤ W ∧ F = pointsIn W U := by
  constructor
  · rintro ⟨hF, hne⟩
    exact ⟨_, flat_span_not_le W hF hne, flat_eq_pointsIn_span W hF⟩
  · rintro ⟨U, hU, rfl⟩
    exact ⟨pointsIn_isFlat W U, (pointsIn_nonempty_iff W U).mpr hU⟩

theorem pointsIn_eRk (W U : Submodule K V) (hU : ¬ U ≤ W) :
    (matroid W).eRk (pointsIn W U) = (finrank K U : ℕ∞) := by
  rw [matroid_eRk W _ (pointsIn_subset_ground W U), pointsIn_span W U hU]

omit [Module.Finite K V] [Finite V] in
@[simp] theorem pointsIn_top (W : Submodule K V) : pointsIn W ⊤ = survivingPoints W := by
  ext p
  simp [pointsIn, survivingPoints]

omit [Module.Finite K V] [Finite V] in
@[simp] theorem pointsIn_bot (W : Submodule K V) : pointsIn W ⊥ = ∅ := by
  ext p
  simp only [pointsIn, mem_ofPred_eq, Submodule.mem_bot, mem_empty_iff_false, iff_false,
    not_and]
  exact fun h => False.elim (Projectivization.rep_nonzero p h)

theorem matroid_empty_isFlat (W : Submodule K V) : (matroid W).IsFlat ∅ := by
  simpa using pointsIn_isFlat W ⊥

/-- Deleting a proper projective subspace retains the full ambient rank. -/
theorem matroid_eRank (W : Submodule K V) (hW : W ≠ ⊤) :
    (matroid W).eRank = (finrank K V : ℕ∞) := by
  rw [Matroid.eRank_def, matroid_ground, ← pointsIn_top W,
    pointsIn_eRk W ⊤ (by simpa using hW), finrank_top]

end BoseBurton
