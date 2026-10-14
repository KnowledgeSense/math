import MainTheorems.Domination.EndpointBounds

namespace ResearchMain.Domination

open Classical

theorem compositionCountZ_append_congr {r s : ℕ} (a : Fin r → ℕ) (b : Fin s → ℕ)
    (h : ∀ N, compositionCountZ a N = compositionCountZ b N) (d : ℕ) (N : ℤ) :
    compositionCountZ (Fin.lastCases d a) N = compositionCountZ (Fin.lastCases d b) N := by
  rw [compositionCountZ_append, compositionCountZ_append]
  apply Finset.sum_congr rfl
  intro j _
  exact h (N - j)

theorem pairDenominator_congr {r s : ℕ} (a b : ℕ) (u : Fin r → ℕ) (v : Fin s → ℕ)
    (h : ∀ N, compositionCountZ u N = compositionCountZ v N) (N : ℤ) :
    pairDenominator a b u N = pairDenominator a b v N := by
  apply Finset.sum_congr rfl
  intro j _
  rw [h]

theorem pairNumerator_congr {r s : ℕ} (a b : ℕ) (u : Fin r → ℕ) (v : Fin s → ℕ)
    (h : ∀ N, compositionCountZ u N = compositionCountZ v N) (N : ℤ) (t : ℕ) :
    pairNumerator a b u N t = pairNumerator a b v N t := by
  apply Finset.sum_congr rfl
  intro j _
  rw [h]

theorem endpointCount_append_interior (r q m : ℕ) (N : ℤ) :
    compositionCountZ (Fin.lastCases m (endpointBounds r q m)) N =
      pathCompositionCount (r + 1) q m N := by
  unfold pathCompositionCount endpointBounds
  rw [compositionCountZ_appends_comm, compositionCountZ_append, compositionCountZ_append]
  apply Finset.sum_congr rfl
  intro a _
  rw [compositionCountZ_appends_comm, lastCases_const]

theorem singleEndpoint_append_interior (r q m : ℕ) (N : ℤ) :
    compositionCountZ (Fin.lastCases m (Fin.lastCases q (fun _ : Fin r => m))) N =
      compositionCountZ (Fin.lastCases q (fun _ : Fin (r + 1) => m)) N := by
  rw [compositionCountZ_appends_comm, lastCases_const]

theorem endpointPair_denominator (r q m : ℕ) (N : ℤ) :
    pairDenominator q m (Fin.lastCases q (fun _ : Fin r => m)) N =
      pathCompositionCount (r + 1) q m N := by
  rw [pairDenominator_twoAppends]
  unfold pathCompositionCount endpointBounds
  rw [compositionCountZ_append, compositionCountZ_append]
  apply Finset.sum_congr rfl
  intro a _
  exact singleEndpoint_append_interior r q m (N - a)

theorem interiorPair_denominator (r q m : ℕ) (N : ℤ) :
    pairDenominator m m (endpointBounds r q m) N = pathCompositionCount (r + 2) q m N := by
  rw [pairDenominator_twoAppends]
  have h := compositionCountZ_append_congr (Fin.lastCases m (endpointBounds r q m))
    (endpointBounds (r + 1) q m) (endpointCount_append_interior r q m) m N
  rw [h, endpointCount_append_interior]

noncomputable def endpointMergeCount (r q m : ℕ) (N : ℤ) : ℤ :=
  pairNumerator q m (Fin.lastCases q (fun _ : Fin r => m)) N q

noncomputable def interiorMergeCount (r q m : ℕ) (N : ℤ) : ℤ :=
  pairNumerator m m (endpointBounds r q m) N m

theorem endpointMergeCount_moment (r q m : ℕ) (hq : 1 ≤ q) (hqm : q ≤ m) (N : ℤ) :
    endpointMergeCount r q m N =
      compositionMoment (endpointBounds r q m) N (Fin.last (r + 1)) - pathCompositionCount r q m N := by
  rw [endpointMergeCount, pairNumerator_low q m hq hqm]
  rfl

theorem endpointMergeCount_cross (r q m : ℕ) (hq : 1 ≤ q) (hm : 1 ≤ m) (N : ℤ) :
    endpointMergeCount r q m N * pathCompositionCount (r + 2) q m N ≤
      endpointMergeCount (r + 1) q m N * pathCompositionCount (r + 1) q m N := by
  have h := pairNumerator_append_cross q m (Fin.lastCases q (fun _ : Fin r => m))
    (fun i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hq
      · simpa using hm) m N q
  rw [pairDenominator_congr q m _ _ (singleEndpoint_append_interior r q m),
    pairNumerator_congr q m _ _ (singleEndpoint_append_interior r q m),
    endpointPair_denominator, endpointPair_denominator] at h
  change endpointMergeCount r q m N * pathCompositionCount (r + 1 + 1) q m N ≤
    endpointMergeCount (r + 1) q m N * pathCompositionCount (r + 1) q m N at h
  simpa only [Nat.add_assoc] using h

theorem interiorMergeCount_cross (r q m : ℕ) (hq : 1 ≤ q) (hm : 1 ≤ m) (N : ℤ) :
    interiorMergeCount r q m N * pathCompositionCount (r + 3) q m N ≤
      interiorMergeCount (r + 1) q m N * pathCompositionCount (r + 2) q m N := by
  have hpos : ∀ i, 1 ≤ endpointBounds r q m i := by
    intro i
    rw [endpointBounds_value]
    split <;> assumption
  have h := pairNumerator_append_cross m m (endpointBounds r q m) hpos m N m
  rw [pairDenominator_congr m m _ _ (endpointCount_append_interior r q m),
    pairNumerator_congr m m _ _ (endpointCount_append_interior r q m),
    interiorPair_denominator, interiorPair_denominator] at h
  change interiorMergeCount r q m N * pathCompositionCount (r + 1 + 2) q m N ≤
    interiorMergeCount (r + 1) q m N * pathCompositionCount (r + 2) q m N at h
  simpa only [Nat.add_assoc] using h

end ResearchMain.Domination
