import MainTheorems.Domination.CompositionPair
import MainTheorems.Domination.CompositionAppend

namespace ResearchMain.Domination

open Classical ResearchMain.LogConcavity

noncomputable def pairDenominator {r : ℕ} (a b : ℕ) (bounds : Fin r → ℕ) (N : ℤ) : ℤ :=
  ∑ s ∈ Finset.Icc 0 (a + b),
    compositionCountZ (twoBounds a b) s * compositionCountZ bounds (N - s)

noncomputable def pairNumerator {r : ℕ} (a b : ℕ) (bounds : Fin r → ℕ)
    (N : ℤ) (t : ℕ) : ℤ :=
  ∑ s ∈ (Finset.Icc 0 (a + b)).filter (· ≤ t),
    compositionCountZ (twoBounds a b) s * compositionCountZ bounds (N - s)

theorem pairDenominator_eq {r : ℕ} (a b : ℕ) (bounds : Fin r → ℕ) (N : ℤ) :
    pairDenominator a b bounds N =
      compositionCountZ (Fin.addCases (twoBounds a b) bounds) N := by
  rw [compositionCountZ_convolution]
  simp only [Fin.sum_univ_two, twoBounds, Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

theorem pairNumerator_nonneg {r : ℕ} (a b : ℕ) (bounds : Fin r → ℕ) (N : ℤ) (t : ℕ) :
    0 ≤ pairNumerator a b bounds N t := by
  apply Finset.sum_nonneg
  intro s _
  exact mul_nonneg (compositionCountZ_nonneg _ _) (compositionCountZ_nonneg _ _)

theorem pairDenominator_nonneg {r : ℕ} (a b : ℕ) (bounds : Fin r → ℕ) (N : ℤ) :
    0 ≤ pairDenominator a b bounds N := by
  apply Finset.sum_nonneg
  intro s _
  exact mul_nonneg (compositionCountZ_nonneg _ _) (compositionCountZ_nonneg _ _)

theorem pairNumerator_le_denominator {r : ℕ} (a b : ℕ) (bounds : Fin r → ℕ)
    (N : ℤ) (t : ℕ) : pairNumerator a b bounds N t ≤ pairDenominator a b bounds N := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro s _ _
  exact mul_nonneg (compositionCountZ_nonneg _ _) (compositionCountZ_nonneg _ _)

theorem pairNumerator_low {r : ℕ} (q m : ℕ) (hq : 1 ≤ q) (hqm : q ≤ m)
    (bounds : Fin r → ℕ) (N : ℤ) :
    pairNumerator q m bounds N q =
      compositionMoment (Fin.lastCases q bounds) N (Fin.last r) -
        compositionCountZ (Fin.lastCases q bounds) N := by
  have hfilter : (Finset.Icc 0 (q + m)).filter (· ≤ q) = Finset.Icc 0 q := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [pairNumerator, hfilter, compositionLowerMoment_append]
  calc
    (∑ s ∈ Finset.Icc 0 q,
        compositionCountZ (twoBounds q m) s * compositionCountZ bounds (N - s)) =
      ∑ s ∈ Finset.Icc 1 q,
        compositionCountZ (twoBounds q m) s * compositionCountZ bounds (N - s) := by
      symm
      apply Finset.sum_subset
      · intro s hs
        have h := Finset.mem_Icc.mp hs
        exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
      · intro s hs hsnot
        have hs0 : s = 0 := by
          have h := Finset.mem_Icc.mp hs
          have hnot : ¬ (1 ≤ s ∧ s ≤ q) := by simpa only [Finset.mem_Icc] using hsnot
          omega
        simp only [hs0, Nat.cast_zero, compositionCountZ_pair_zero q m hq (by omega), zero_mul]
    _ = ∑ s ∈ Finset.Icc 1 q, ((s : ℤ) - 1) * compositionCountZ bounds (N - s) := by
      apply Finset.sum_congr rfl
      intro s hs
      obtain ⟨hslo, hshi⟩ := Finset.mem_Icc.mp hs
      rw [compositionCountZ_pair_below q m s hslo hshi (by omega)]

theorem pairNumerator_append_cross {r : ℕ} (a b : ℕ) (bounds : Fin r → ℕ)
    (hpos : ∀ i, 1 ≤ bounds i) (d : ℕ) (N : ℤ) (t : ℕ) :
    pairNumerator a b bounds N t * pairDenominator a b (Fin.lastCases d bounds) N ≤
      pairNumerator a b (Fin.lastCases d bounds) N t * pairDenominator a b bounds N := by
  apply conditioning_cumulative_ordered (Finset.Icc 0 (a + b))
    (fun s _ => compositionCountZ_nonneg (twoBounds a b) s)
  intro s v hsv
  simpa only [mul_comm] using
    composition_append_minor bounds hpos d (N - v) (N - s) (by omega)

end ResearchMain.Domination
