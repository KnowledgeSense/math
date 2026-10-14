import MainTheorems.PreorderGamma.Macaulay.BallotStep
import MainTheorems.PreorderGamma.Macaulay.BallotNumbers
import Mathlib.Data.Finset.Max

namespace ResearchMain.PreorderGamma.Macaulay

variable {V : Type*} [DecidableEq V]

theorem ballotSets_card {index : V → ℕ} (hinj : Function.Injective index)
    (U : Finset V) (r : ℕ) : (ballotSets index U r).card = ballotNumber U.card r := by
  classical
  revert r
  refine Finset.strongInductionOn U ?_
  intro U ih r
  by_cases hu : U = ∅
  · subst U
    cases r with
    | zero => simp
    | succ r =>
      rw [ballotSets_empty_of_large index ∅ (r + 1) (by simp)]
      simp
  · have hne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hu
    obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image U index hne
    have hsmall : U.erase v ⊂ U := Finset.erase_ssubset hv
    have hstrict : ∀ u ∈ U.erase v, index u < index v := by
      intro u hu
      obtain ⟨hne, hu⟩ := Finset.mem_erase.mp hu
      have hle := hmax u hu
      have hneq : index u ≠ index v := fun h => hne (hinj h)
      omega
    cases r with
    | zero => simp
    | succ r =>
      have hs := ballotSets_succ_insert_card hstrict (Finset.notMem_erase v U) r
      rw [Finset.insert_erase hv, ih (U.erase v) hsmall (r + 1),
        ih (U.erase v) hsmall r] at hs
      rw [hs, ← ballotNumber_step]
      rw [Finset.card_erase_add_one hv]

end ResearchMain.PreorderGamma.Macaulay
