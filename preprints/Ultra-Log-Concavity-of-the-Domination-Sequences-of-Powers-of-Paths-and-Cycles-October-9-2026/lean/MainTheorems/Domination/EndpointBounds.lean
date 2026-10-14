import MainTheorems.Domination.PathCounts
import MainTheorems.Domination.PairExpansion
import MainTheorems.Domination.UniformCompositions

namespace ResearchMain.Domination

def endpointBounds (r q m : ℕ) : Fin (r + 2) → ℕ :=
  Fin.lastCases q (Fin.lastCases q (fun _ : Fin r => m))

theorem endpointBounds_value (r q m : ℕ) (i : Fin (r + 2)) :
    endpointBounds r q m i = if i.val < r then m else q := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [endpointBounds, Fin.lastCases_last, Fin.val_last]
    rw [ite_eq_right (by omega)]
  · refine Fin.lastCases ?_ (fun t => ?_) j
    · simp only [endpointBounds, Fin.lastCases_castSucc, Fin.lastCases_last,
        Fin.val_castSucc, Fin.val_last]
      rw [ite_eq_right (by omega)]
    · simp only [endpointBounds, Fin.lastCases_castSucc, Fin.val_castSucc]
      rw [ite_eq_left t.isLt]

theorem endpointBounds_path_reindex (r ℓ : ℕ) :
    endpointBounds r (ℓ + 1) (2 * ℓ + 1) =
      pathBounds (r + 2) ℓ ∘ Equiv.swap 0 (Fin.last r).castSucc := by
  funext i
  rw [endpointBounds_value]
  simp only [Function.comp_apply]
  by_cases hi0 : i = 0
  · subst i
    rw [Equiv.swap_apply_left]
    simp only [pathBounds, Fin.val_zero, Fin.val_castSucc, Fin.val_last]
    by_cases hr : r = 0
    · simp only [hr, lt_self_iff_false, zero_add, true_or, ite_true, ite_false]
    · have hlt : 0 < r := by omega
      simp only [hlt, hr, show r + 1 ≠ r + 2 by omega, false_or, ite_false, ite_true]
  · by_cases himid : i = (Fin.last r).castSucc
    · subst i
      rw [Equiv.swap_apply_right]
      simp only [pathBounds, Fin.val_castSucc, Fin.val_last, Fin.val_zero,
        lt_self_iff_false, ite_false, true_or, ite_true]
    · rw [Equiv.swap_apply_of_ne_of_ne hi0 himid]
      have hv0 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
      have hvm : i.val ≠ r := fun h => himid (Fin.ext h)
      have hi := i.isLt
      unfold pathBounds
      by_cases hilast : i.val + 1 = r + 2
      · rw [ite_eq_right (by omega), ite_eq_left (Or.inr hilast)]
      · rw [ite_eq_left (by omega), ite_eq_right (by tauto)]

noncomputable def pathCompositionCount (r q m : ℕ) (N : ℤ) : ℤ :=
  compositionCountZ (endpointBounds r q m) N

theorem pathPower_count_endpoints (n r ℓ : ℕ) :
    (dominationCount (pathPower n ℓ) (r + 1) : ℤ) =
      pathCompositionCount r (ℓ + 1) (2 * ℓ + 1) (n + 1) := by
  rw [dominationCount_pathPower, ← compositionCountZ_nat]
  have h := compositionCountZ_reindex (Equiv.swap 0 (Fin.last r).castSucc)
    (pathBounds (r + 2) ℓ) (n + 1)
  rw [← endpointBounds_path_reindex] at h
  exact h.symm

end ResearchMain.Domination
