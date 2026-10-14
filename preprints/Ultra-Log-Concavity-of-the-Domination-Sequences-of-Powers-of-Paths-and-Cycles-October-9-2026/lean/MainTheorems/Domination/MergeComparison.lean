import MainTheorems.Domination.EndpointMoments
import MainTheorems.Domination.PairComparison

namespace ResearchMain.Domination

open Classical

theorem endpointMergeCount_expanded (r q m : ℕ) (hq : 1 ≤ q) (hqm : q ≤ m) (N : ℤ) :
    endpointMergeCount r q m N =
      ∑ a ∈ Finset.Icc 1 q, ((a : ℤ) - 1) *
        compositionCountZ (Fin.lastCases q (fun _ : Fin r => m)) (N - a) := by
  rw [endpointMergeCount, pairNumerator_low q m hq hqm, compositionLowerMoment_append]

theorem interiorMergeCount_expanded (r q m : ℕ) (hm : 1 ≤ m) (N : ℤ) :
    interiorMergeCount r q m N =
      ∑ b ∈ Finset.Icc 1 m, ((b : ℤ) - 1) * pathCompositionCount r q m (N - b) := by
  rw [interiorMergeCount, pairNumerator_low m m hm le_rfl, compositionLowerMoment_append]
  rfl

theorem interiorMergeCount_ge_endpoint (r q m : ℕ) (hq : 1 ≤ q) (hqm : q ≤ m) (N : ℤ) :
    endpointMergeCount (r + 1) q m N ≤ interiorMergeCount r q m N := by
  let bounds : Fin (r + 1) → ℕ := Fin.lastCases q (fun _ : Fin r => m)
  have he : endpointMergeCount (r + 1) q m N =
      ∑ a ∈ Finset.Icc 1 q, ∑ b ∈ Finset.Icc 1 m,
        ((a : ℤ) - 1) * compositionCountZ bounds (N - a - b) := by
    rw [endpointMergeCount_expanded _ _ _ hq hqm]
    apply Finset.sum_congr rfl
    intro a _
    rw [← singleEndpoint_append_interior, compositionCountZ_append, Finset.mul_sum]
  have hi : interiorMergeCount r q m N =
      ∑ a ∈ Finset.Icc 1 q, ∑ b ∈ Finset.Icc 1 m,
        ((b : ℤ) - 1) * compositionCountZ bounds (N - a - b) := by
    have hnum : interiorMergeCount r q m N =
        ∑ b ∈ Finset.Icc 1 m, ∑ a ∈ Finset.Icc 1 q,
          ((b : ℤ) - 1) * compositionCountZ bounds (N - b - a) := by
      rw [interiorMergeCount_expanded _ _ _ (by omega)]
      apply Finset.sum_congr rfl
      intro b _
      change ((b : ℤ) - 1) * compositionCountZ (Fin.lastCases q bounds) (N - b) = _
      rw [compositionCountZ_append, Finset.mul_sum]
    rw [hnum, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [show N - (b : ℤ) - a = N - a - b by ring]
  have hd : interiorMergeCount r q m N - endpointMergeCount (r + 1) q m N =
      ∑ a ∈ Finset.Icc 1 q, ∑ b ∈ Finset.Icc 1 m,
        ((b : ℤ) - a) * compositionCountZ bounds (N - a - b) := by
    rw [he, hi, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  apply sub_nonneg.mp
  rw [hd]
  exact endpoint_interior_composition_difference_nonneg bounds q m hqm N

theorem pathCompositionCount_nonneg (r q m : ℕ) (N : ℤ) :
    0 ≤ pathCompositionCount r q m N := compositionCountZ_nonneg _ _

theorem pathMergeCount_cross (r q m : ℕ) (hq : 1 ≤ q) (hqm : q ≤ m) (N : ℤ) :
    ((r + 4 : ℕ) : ℤ) *
        (2 * endpointMergeCount (r + 1) q m N + ((r + 1 : ℕ) : ℤ) * interiorMergeCount r q m N) *
          pathCompositionCount (r + 3) q m N ≤
      ((r + 3 : ℕ) : ℤ) *
        (2 * endpointMergeCount (r + 2) q m N + ((r + 2 : ℕ) : ℤ) * interiorMergeCount (r + 1) q m N) *
          pathCompositionCount (r + 2) q m N := by
  have he := mul_le_mul_of_nonneg_left (endpointMergeCount_cross (r + 1) q m hq (by omega) N)
    (show (0 : ℤ) ≤ 2 * (r + 3 : ℕ) by positivity)
  have hi := mul_le_mul_of_nonneg_left (interiorMergeCount_cross r q m hq (by omega) N)
    (show (0 : ℤ) ≤ ((r + 3 : ℕ) : ℤ) * (r + 2 : ℕ) by positivity)
  have hd := mul_nonneg (sub_nonneg.mpr (interiorMergeCount_ge_endpoint r q m hq hqm N))
    (pathCompositionCount_nonneg (r + 3) q m N)
  simp only [Nat.add_assoc] at he
  push_cast at he hi ⊢
  nlinarith only [he, hi, hd]

theorem pathMergeCount_cross_two (q m : ℕ) (hq : 1 ≤ q) (hqm : q ≤ m) (N : ℤ) :
    3 * (2 * endpointMergeCount 0 q m N) * pathCompositionCount 2 q m N ≤
      2 * (2 * endpointMergeCount 1 q m N + interiorMergeCount 0 q m N) *
        pathCompositionCount 1 q m N := by
  have he := endpointMergeCount_cross 0 q m hq (by omega) N
  have hd := mul_nonneg (sub_nonneg.mpr (interiorMergeCount_ge_endpoint 0 q m hq hqm N))
    (pathCompositionCount_nonneg 1 q m N)
  norm_num only [Nat.zero_add] at he hd
  nlinarith only [he, hd]

theorem pathCompositionCount_weighted_lc (r q m : ℕ) (hq : 1 ≤ q) (hqm : q ≤ m) (N : ℤ) :
    (N - (r + 2 : ℕ)) * ((r + 3 : ℕ) : ℤ) * pathCompositionCount r q m N *
        pathCompositionCount (r + 2) q m N ≤
      (N - (r + 3 : ℕ)) * ((r + 2 : ℕ) : ℤ) * pathCompositionCount (r + 1) q m N ^ 2 := by
  cases r with
  | zero =>
    have htwo := pathMergeCount_identity_two q m hq hqm N
    have hthree := pathMergeCount_identity 0 q m hq hqm N
    norm_num only [Nat.zero_add, Nat.cast_one, one_mul, Nat.cast_ofNat] at hthree ⊢
    calc
      _ = 3 * (2 * endpointMergeCount 0 q m N) * pathCompositionCount 2 q m N := by
        rw [htwo]
        ring
      _ ≤ 2 * (2 * endpointMergeCount 1 q m N + interiorMergeCount 0 q m N) *
          pathCompositionCount 1 q m N := pathMergeCount_cross_two q m hq hqm N
      _ = _ := by rw [hthree]; ring
  | succ r =>
    have hfirst := pathMergeCount_identity r q m hq hqm N
    have hnext := pathMergeCount_identity (r + 1) q m hq hqm N
    simp only [Nat.add_assoc] at hnext ⊢
    calc
      _ = ((r + 4 : ℕ) : ℤ) *
          (2 * endpointMergeCount (r + 1) q m N + ((r + 1 : ℕ) : ℤ) * interiorMergeCount r q m N) *
            pathCompositionCount (r + 3) q m N := by rw [hfirst]; ring
      _ ≤ ((r + 3 : ℕ) : ℤ) *
          (2 * endpointMergeCount (r + 2) q m N + ((r + 2 : ℕ) : ℤ) * interiorMergeCount (r + 1) q m N) *
            pathCompositionCount (r + 2) q m N := pathMergeCount_cross r q m hq hqm N
      _ = _ := by rw [hnext]; ring

end ResearchMain.Domination
