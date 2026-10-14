import MainTheorems.Domination.EndpointCoefficients

namespace ResearchMain.Domination

open Classical

theorem compositionMoment_eq_of_bound_eq {r : ℕ} (bounds : Fin r → ℕ) (N : ℤ)
    (i j : Fin r) (hij : bounds i = bounds j) :
    compositionMoment bounds N i = compositionMoment bounds N j := by
  have hb : bounds ∘ Equiv.swap i j = bounds := by
    funext t
    simp only [Function.comp_apply]
    by_cases hti : t = i
    · subst t
      rw [Equiv.swap_apply_left]
      exact hij.symm
    · by_cases htj : t = j
      · subst t
        rw [Equiv.swap_apply_right]
        exact hij
      · rw [Equiv.swap_apply_of_ne_of_ne hti htj]
  have h := compositionMoment_reindex (Equiv.swap i j) bounds N i
  simpa only [hb, Equiv.swap_apply_left] using h

theorem appendedEndpoint_value (r q m : ℕ) (i : Fin (r + 3)) :
    Fin.lastCases m (endpointBounds r q m) i =
      if i.val < r ∨ i.val = r + 2 then m else q := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.lastCases_last, Fin.val_last]
    simp only [or_true, ite_true]
  · simp only [Fin.lastCases_castSucc, endpointBounds_value,
      Fin.val_castSucc]
    have hne : j.val ≠ r + 2 := by have := j.isLt; omega
    simp only [hne, or_false]

theorem endpointBounds_append_reindex (r q m : ℕ) :
    endpointBounds (r + 1) q m =
      (Fin.lastCases m (endpointBounds r q m)) ∘
        Equiv.swap (Fin.last r).castSucc.castSucc (Fin.last (r + 2)) := by
  funext i
  rw [endpointBounds_value]
  simp only [Function.comp_apply]
  by_cases himid : i = (Fin.last r).castSucc.castSucc
  · subst i
    rw [Equiv.swap_apply_left, appendedEndpoint_value]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ite_eq_left (by omega)]
    simp only [or_true, ite_true]
  · by_cases hilast : i = Fin.last (r + 2)
    · subst i
      rw [Equiv.swap_apply_right, appendedEndpoint_value]
      simp only [Fin.val_last, Fin.val_castSucc]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [Equiv.swap_apply_of_ne_of_ne himid hilast, appendedEndpoint_value]
      have hvm : i.val ≠ r := fun h => himid (Fin.ext h)
      have hvl : i.val ≠ r + 2 := fun h => hilast (Fin.ext h)
      have heq : i.val < r + 1 ↔ i.val < r ∨ i.val = r + 2 := by omega
      simp only [heq]

theorem interiorMergeCount_moment (r q m : ℕ) (hm : 1 ≤ m) (N : ℤ) :
    interiorMergeCount r q m N =
      compositionMoment (endpointBounds (r + 1) q m) N (Fin.last r).castSucc.castSucc -
        pathCompositionCount (r + 1) q m N := by
  rw [interiorMergeCount, pairNumerator_low m m hm le_rfl, endpointCount_append_interior]
  have h := compositionMoment_reindex
    (Equiv.swap (Fin.last r).castSucc.castSucc (Fin.last (r + 2)))
    (Fin.lastCases m (endpointBounds r q m)) N (Fin.last r).castSucc.castSucc
  rw [← endpointBounds_append_reindex, Equiv.swap_apply_left] at h
  rw [h]

theorem endpointMoment_sum (r q m : ℕ) (N : ℤ) :
    ((r + 1 : ℕ) : ℤ) *
        compositionMoment (endpointBounds (r + 1) q m) N (Fin.last r).castSucc.castSucc +
      2 * compositionMoment (endpointBounds (r + 1) q m) N (Fin.last (r + 2)) =
        N * pathCompositionCount (r + 1) q m N := by
  let bounds := endpointBounds (r + 1) q m
  have hinterior : ∀ i : Fin (r + 1),
      compositionMoment bounds N i.castSucc.castSucc =
        compositionMoment bounds N (Fin.last r).castSucc.castSucc := by
    intro i
    apply compositionMoment_eq_of_bound_eq
    simp only [bounds, endpointBounds_value, Fin.val_castSucc, Fin.val_last]
    rw [ite_eq_left i.isLt, ite_eq_left (by omega)]
  have hends : compositionMoment bounds N (Fin.last (r + 1)).castSucc =
      compositionMoment bounds N (Fin.last (r + 2)) := by
    apply compositionMoment_eq_of_bound_eq
    simp only [bounds, endpointBounds_value, Fin.val_castSucc, Fin.val_last]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hs : (∑ i : Fin (r + 1), compositionMoment bounds N i.castSucc.castSucc) =
      ((r + 1 : ℕ) : ℤ) * compositionMoment bounds N (Fin.last r).castSucc.castSucc := by
    calc
      _ = ∑ _i : Fin (r + 1), compositionMoment bounds N (Fin.last r).castSucc.castSucc := by
        apply Finset.sum_congr rfl
        intro i _
        exact hinterior i
      _ = _ := by simp
  have h := sum_compositionMoment bounds N
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, hs, hends] at h
  change _ = N * pathCompositionCount (r + 1) q m N at h
  nlinarith only [h]

theorem endpointMoment_sum_zero (q m : ℕ) (N : ℤ) :
    2 * compositionMoment (endpointBounds 0 q m) N (Fin.last 1) =
      N * pathCompositionCount 0 q m N := by
  have heq : compositionMoment (endpointBounds 0 q m) N 0 =
      compositionMoment (endpointBounds 0 q m) N (Fin.last 1) := by
    apply compositionMoment_eq_of_bound_eq
    simp only [endpointBounds_value, Fin.val_zero, Fin.val_last, not_lt_zero, ite_false]
  have h := sum_compositionMoment (endpointBounds 0 q m) N
  rw [Fin.sum_univ_two, heq] at h
  change compositionMoment (endpointBounds 0 q m) N (Fin.last 1) +
    compositionMoment (endpointBounds 0 q m) N (Fin.last 1) = N * pathCompositionCount 0 q m N at h
  nlinarith only [h]

theorem pathMergeCount_identity (r q m : ℕ) (hq : 1 ≤ q) (hqm : q ≤ m) (N : ℤ) :
    2 * endpointMergeCount (r + 1) q m N + ((r + 1 : ℕ) : ℤ) * interiorMergeCount r q m N =
      (N - (r + 3 : ℕ)) * pathCompositionCount (r + 1) q m N := by
  rw [endpointMergeCount_moment (r + 1) q m hq hqm,
    interiorMergeCount_moment r q m (by omega)]
  have h := endpointMoment_sum r q m N
  change 2 * (compositionMoment (endpointBounds (r + 1) q m) N (Fin.last (r + 2)) -
    pathCompositionCount (r + 1) q m N) + ((r + 1 : ℕ) : ℤ) *
    (compositionMoment (endpointBounds (r + 1) q m) N (Fin.last r).castSucc.castSucc -
      pathCompositionCount (r + 1) q m N) = _
  push_cast at h ⊢
  nlinarith only [h]

theorem pathMergeCount_identity_two (q m : ℕ) (hq : 1 ≤ q) (hqm : q ≤ m) (N : ℤ) :
    2 * endpointMergeCount 0 q m N = (N - 2) * pathCompositionCount 0 q m N := by
  rw [endpointMergeCount_moment 0 q m hq hqm]
  have h := endpointMoment_sum_zero q m N
  nlinarith only [h]

end ResearchMain.Domination
