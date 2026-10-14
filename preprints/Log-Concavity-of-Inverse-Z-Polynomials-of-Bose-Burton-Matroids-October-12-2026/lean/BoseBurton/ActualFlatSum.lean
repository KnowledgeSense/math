import BoseBurton.RestrictedZ
import BoseBurton.ZIncidenceRecurrence

noncomputable section
namespace BoseBurton
open Finset Submodule Module Polynomial MatroidInverseZ
open scoped Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V] [Finite V]

omit [Module.Finite K V] in
theorem sum_nonempty_flatSpan {R : Type*} [AddCancelCommMonoid R]
    (W : Submodule K V) (hW : W ≠ ⊤) (f : Submodule K V → R) :
    (∑ F ∈ Ioc (⊥ : FlatSpan W) (spanTop W hW), f F.1) =
      ∑ U ∈ univ.filter (fun U => ¬ U ≤ W), f U := by
  have h := sum_flatSpan W f
  rw [← span_interval_univ W hW, Icc_eq_cons_Ioc bot_le, sum_cons] at h
  exact add_left_cancel h

/-- Incidence inversion over the complete actual flat system, including its top flat. -/
theorem spanY_actual_flat_sum (W : Submodule K V) (hW : W ≠ ⊤) :
    spanY W hW = -(∑ U ∈ univ.filter (fun U : Submodule K V => ¬ U ≤ W),
      C ((-1 : ℤ)^(finrank K U)) * restrictedZRow W U * projectiveY K (V ⧸ U)) := by
  have hlt : (⊥ : FlatSpan W) < spanTop W hW :=
    lt_of_le_of_ne bot_le (span_bot_ne_top W hW)
  rw [spanY, inverseZ_from_zKernel (spanRank W) (spanRank_strictMono W).monotone _ _ hlt]
  congr 1
  rw [← sum_nonempty_flatSpan W hW]
  apply sum_congr rfl
  intro F hF
  have hne : F ≠ ⊥ := (mem_Ioc.mp hF).1.ne'
  have hU : ¬ F.1 ≤ W := F.2.resolve_left (fun h => hne (Subtype.ext h))
  have he : F = (⟨F.1, Or.inr hU⟩ : FlatSpan W) := rfl
  rw [he, lower_zKernel_eq_restrictedRow W F.1 hU,
    upper_inverseZ_projective W F.1 hW hU, spanRank_bot, Nat.sub_zero]
  rfl

theorem actual_inverseZ_flat_sum (W : Submodule K V) (hW : W ≠ ⊤) :
    matroidInverseZ (matroid W) = -(∑ U ∈ univ.filter (fun U : Submodule K V => ¬ U ≤ W),
      C ((-1 : ℤ)^(finrank K U)) * restrictedZRow W U * projectiveY K (V ⧸ U)) := by
  rw [actual_inverseZ_eq_spanY W hW, spanY_actual_flat_sum]

end BoseBurton
