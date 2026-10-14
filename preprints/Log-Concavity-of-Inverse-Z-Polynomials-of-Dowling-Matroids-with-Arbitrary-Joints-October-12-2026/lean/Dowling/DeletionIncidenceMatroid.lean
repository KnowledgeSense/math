import Dowling.DeletionIncidencePolynomial
import Dowling.DeletionIncidenceBoundaries
import Dowling.MatroidDeletionColoopPush

noncomputable section
namespace MatroidInverseZ
open Finset LaurentPolynomial Dowling
open scoped Classical
variable {α : Type*} [Fintype α]

/-- The actual deletion intertwiner, with every ranked-map hypothesis discharged. -/
theorem matroid_deletionKL_intertwiner (M : Matroid α) (e : α) (F : Flat M) :
    deletionPush (flatRank M) (flatRank (M.delete {e})) (deletionFlat M e)
      (deletionKLVector (flatRank M) F)=
        deletionKLCombination (flatRank (M.delete {e}))
          (deletionKLTransition (flatRank M) (flatRank (M.delete {e})) (deletionFlat M e) F) := by
  apply deletionKLTransition_intertwiner _ _ _ (closureFlat M e)
    (flatRank_monotone M) (flatRank_monotone (M.delete {e}))
    (fun x a=>closureFlat_le_iff M e a x) (closureFlat_rank M e)
    (rank_le_deletionFlat_rank_add_one M e)
  intro b hb x
  have heb : e∈b.val := by
    by_contra h
    exact hb (deletionFlat_rank_eq_of_not_mem M e b h)
  have hfb : M.IsFlat (b.val\{e}) := by
    by_contra h
    exact hb (deletionFlat_rank_eq_of_not_flat M e b h)
  exact coloop_deletionPush M e b heb hfb x

/-- Genuine inverse-Z deletion before restricting the zero tau summands to correction flats. -/
theorem matroid_inverseZ_deletion_rank_sum (M : Matroid α) (e : α)
    (h0 : M.IsFlat ∅) (he : M.IsFlat {e}) (hc : ¬M.IsColoop e) :
    matroidInverseZ M=matroidInverseZ (M.delete {e})+
      (1+Polynomial.X)*inverseZ (flatRank M) (deletionSingletonFlat M e he) (topFlat M)-
      ∑ F,if flatRank (M.delete {e}) (deletionFlat M e F)=flatRank M F then
        Polynomial.C (deletionTau (flatRank M) (deletionSingletonFlat M e he) F)*
          Polynomial.X^(flatRank M F/2)*inverseZ (flatRank M) F (topFlat M) else 0 := by
  have h := deletionYCoordinate_transition (flatRank M) (flatRank (M.delete {e}))
    (flatRank_monotone M) (flatRank_monotone (M.delete {e}))
    (deletionFlat M e) (closureFlat M e) (fun b a=>closureFlat_le_iff M e a b)
    (deletionFlat_closureFlat M e) (topFlat M) (topFlat (M.delete {e}))
    (le_topFlat M) (le_topFlat (M.delete {e})) (closureFlat_top_of_not_coloop M e hc)
    (deletionKLTransition (flatRank M) (flatRank (M.delete {e})) (deletionFlat M e))
    (matroid_deletionKL_intertwiner M e) (bottomFlat (M.delete {e}))
  rw [deletionKLTransition_bottom_sum _ _ _ (flatRank_monotone M)
    (deletionFlat_rank_le M e) (rank_le_deletionFlat_rank_add_one M e)
    (bottomFlat M) (deletionSingletonFlat M e he) (bottomFlat (M.delete {e}))
    (flatRank_bottom M) (deletionSingletonFlat_rank M e h0 he) (flatRank_bottom _)
    (deletion_bottom_fiber M e h0 he)] at h
  exact deletion_inverseZ_of_coordinate_relation _ _ (flatRank_monotone M)
    (flatRank_monotone (M.delete {e})) (deletionFlat M e) (topFlat M) (bottomFlat M)
    (deletionSingletonFlat M e he) (topFlat (M.delete {e})) (bottomFlat (M.delete {e}))
    (le_topFlat M) (bottomFlat_le _ _) (flatRank_bottom M)
    (deletionSingletonFlat_rank M e h0 he) (flatRank_bottom _)
    (deletion_top_rank_of_not_coloop M e hc) h

/-- The inverse-Z deletion identity on genuine finite matroids with a singleton flat and no loops. -/
theorem matroid_inverseZ_deletion (M : Matroid α) (e : α)
    (h0 : M.IsFlat ∅) (he : M.IsFlat {e}) (hc : ¬M.IsColoop e) :
    matroidInverseZ M=matroidInverseZ (M.delete {e})+
      (1+Polynomial.X)*inverseZ (flatRank M) (deletionSingletonFlat M e he) (topFlat M)-
      ∑ F∈univ.filter (fun F : Flat M=>e∈F.val ∧ ¬M.IsFlat (F.val\{e})),
        Polynomial.C (deletionTau (flatRank M) (deletionSingletonFlat M e he) F)*
          Polynomial.X^(flatRank M F/2)*inverseZ (flatRank M) F (topFlat M) := by
  rw [matroid_inverseZ_deletion_rank_sum M e h0 he hc,sum_filter]
  congr 1
  apply sum_congr rfl
  intro F hF
  by_cases hem : e∈F.val
  · by_cases hf : M.IsFlat (F.val\{e})
    · have hn : flatRank (M.delete {e}) (deletionFlat M e F)≠flatRank M F := by
        have := deletionFlat_rank_drop M e F hem hf
        omega
      simp [hem,hf,hn]
    · simp [hem,hf,deletionFlat_rank_eq_of_not_flat M e F hf]
  · have hn : ¬deletionSingletonFlat M e he≤F := by
      simpa only [deletionSingletonFlat_le_iff] using hem
    simp [hem,deletionTau,hn]

end MatroidInverseZ
