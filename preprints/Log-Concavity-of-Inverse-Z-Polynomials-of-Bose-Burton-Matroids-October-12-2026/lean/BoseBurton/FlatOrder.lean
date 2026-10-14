import BoseBurton.Flats
import ThagomizerTuran.MatroidDefinitions

noncomputable section
namespace BoseBurton
open Set Submodule Module
open scoped LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V] [Finite V]

noncomputable instance projectiveFintype : Fintype (ℙ K V) := Fintype.ofFinite _

/-- The subspaces that survive as flat spans, including the separate empty flat. -/
abbrev FlatSpan (W : Submodule K V) := {U : Submodule K V // U = ⊥ ∨ ¬ U ≤ W}

instance flatSpanOrderBot (W : Submodule K V) : OrderBot (FlatSpan W) where
  bot := ⟨⊥, Or.inl rfl⟩
  bot_le U := show (⊥ : Submodule K V) ≤ U.1 from bot_le

instance flatSpanFinite (W : Submodule K V) : Finite (FlatSpan W) := inferInstance

noncomputable def flatSpanOrderIso (W : Submodule K V) :
    MatroidInverseZ.Flat (matroid W) ≃o FlatSpan W where
  toFun F := ⟨vectorSpan (K := K) Projectivization.rep F.1, by
    by_cases h : F.1.Nonempty
    · exact Or.inr (flat_span_not_le W F.2 h)
    · left
      have he : F.1 = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      simp [he, vectorSpan]⟩
  invFun U := ⟨pointsIn W U.1, pointsIn_isFlat W U.1⟩
  left_inv F := Subtype.ext (flat_eq_pointsIn_span W F.2).symm
  right_inv U := by
    apply Subtype.ext
    rcases U.2 with h | h
    · simp [h, vectorSpan]
    · exact pointsIn_span W U.1 h
  map_rel_iff' := by
    intro F G
    change vectorSpan (K := K) Projectivization.rep F.1 ≤
      vectorSpan (K := K) Projectivization.rep G.1 ↔ F.1 ⊆ G.1
    constructor
    · intro h
      rw [flat_eq_pointsIn_span W F.2, flat_eq_pointsIn_span W G.2]
      exact pointsIn_mono W h
    · exact fun h => span_mono (Set.image_mono h)

/-- This order correspondence preserves the genuine matroid rank on every flat. -/
theorem flatSpanOrderIso_rank (W : Submodule K V)
    (F : MatroidInverseZ.Flat (matroid W)) :
    MatroidInverseZ.flatRank (matroid W) F = finrank K (flatSpanOrderIso W F).1 := by
  change ((matroid W).eRk F.1).toNat = _
  rw [matroid_eRk W F.1 F.2.subset_ground, ENat.toNat_natCast]
  rfl

theorem flatSpanOrderIso_bottom (W : Submodule K V) :
    flatSpanOrderIso W (MatroidInverseZ.bottomFlat (matroid W)) = ⊥ := by
  apply Subtype.ext
  change vectorSpan (K := K) Projectivization.rep ((matroid W).closure ∅) = ⊥
  rw [(matroid_empty_isFlat W).closure]
  simp [vectorSpan]

theorem flatSpanOrderIso_top (W : Submodule K V) (hW : W ≠ ⊤) :
    (flatSpanOrderIso W (MatroidInverseZ.topFlat (matroid W))).1 = ⊤ := by
  change vectorSpan (K := K) Projectivization.rep (survivingPoints W) = ⊤
  rw [← pointsIn_top W, pointsIn_span W ⊤ (by simpa using hW)]

end BoseBurton
