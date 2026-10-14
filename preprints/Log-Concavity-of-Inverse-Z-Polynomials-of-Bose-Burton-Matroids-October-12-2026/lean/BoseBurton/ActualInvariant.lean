import BoseBurton.RankedSpaces
import ThagomizerTuran.IntervalTransport

noncomputable section
namespace BoseBurton
open Submodule Module MatroidInverseZ
open scoped LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V] [Finite V]

theorem actual_inverseZ_eq_spanY (W : Submodule K V) (hW : W ≠ ⊤) :
    matroidInverseZ (matroid W) = spanY W hW := by
  classical
  let e := flatSpanOrderIso W
  have h := inverseZ_interval_transport e.toOrderEmbedding
    (fun _ _ y _ _ => ⟨e.symm y, e.apply_symm_apply y⟩)
    (flatRank (matroid W)) (spanRank W)
    (fun a b => by rw [flatSpanOrderIso_rank W a, flatSpanOrderIso_rank W b]; rfl)
    (bottomFlat (matroid W)) (topFlat (matroid W))
  have hb : e (bottomFlat (matroid W)) = ⊥ := flatSpanOrderIso_bottom W
  have ht : e (topFlat (matroid W)) = spanTop W hW :=
    Subtype.ext (flatSpanOrderIso_top W hW)
  change inverseZ (spanRank W) (e (bottomFlat (matroid W)))
    (e (topFlat (matroid W))) = _ at h
  rw [hb, ht] at h
  exact h.symm

end BoseBurton
