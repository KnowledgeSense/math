import Dowling.BraidBlockUnitOrder

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {n : ℕ}

/-- Recover the trivial-group zero block by removing the distinguished vertex. -/
def unitFromRoots (R : Fin (n+1) → Fin (n+1)) (hR : ∀ i, R (R i)=R i)
    (hmin : ∀ i, R i ≤ i) : GainPartition Unit n where
  code i := if h : R i.succ=0 then none else some ((R i.succ).pred h,1)
  rooted := by
    intro i j g hij
    by_cases hi : R i.succ=0
    · simp only [dite_eq_left hi] at hij
      cases hij
    · rw [dite_eq_right hi] at hij
      have hj : (R i.succ).pred hi=j := congrArg Prod.fst (Option.some.inj hij)
      have he : j.succ=R i.succ := by rw [← hj]; exact Fin.succ_pred _ _
      have hr : R j.succ=j.succ := by rw [he,hR]
      simp [hr]
  least := by
    intro i j g hij
    by_cases hi : R i.succ=0
    · simp only [dite_eq_left hi] at hij
      cases hij
    · rw [dite_eq_right hi] at hij
      have hj : (R i.succ).pred hi=j := congrArg Prod.fst (Option.some.inj hij)
      apply Fin.succ_le_succ_iff.mp
      rw [← hj,Fin.succ_pred]
      exact hmin i.succ

 theorem unitBlockRoot_unitFromRoots (R : Fin (n+1) → Fin (n+1))
    (hR : ∀ i, R (R i)=R i) (hmin : ∀ i, R i ≤ i) :
    (unitFromRoots R hR hmin).unitBlockRoot=R := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (le_antisymm (hmin 0) (Fin.zero_le _)).symm
  · by_cases hj : R j.succ=0
    · simp [unitBlockRoot,unitFromRoots,hj]
    · simp [unitBlockRoot,unitFromRoots,hj,Fin.succ_pred]

end Dowling.GainPartition
