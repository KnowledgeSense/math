import MeanMaximumForests.IndependenceCoefficients
import MeanMaximumForests.GraphRelabeling
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset

namespace MeanMaximumForests
open Finset

/-- A weak local peak, with the coefficient at index `-1` interpreted as zero.
The right coefficient vanishes automatically beyond the independence number. -/
def WeakLocalPeak {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k ≤ G.indepNum ∧
    (k = 0 ∨ independentSetCoefficient G univ (k - 1) ≤ independentSetCoefficient G univ k) ∧
    independentSetCoefficient G univ (k + 1) ≤ independentSetCoefficient G univ k

/-- Coefficients are preserved by relabeling, so the fixed `Fin n` domains
in the minimum sequences cover arbitrary finite vertex labels. -/
theorem independentSetCoefficient_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (k : ℕ) :
    independentSetCoefficient H univ k = independentSetCoefficient G univ k := by
  classical
  unfold independentSetCoefficient
  rw [independentSets_iso e, filter_image]
  simp only [card_map]
  exact card_image_of_injective _ (map_injective _)

theorem weakLocalPeak_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (k : ℕ) :
    WeakLocalPeak H k ↔ WeakLocalPeak G k := by
  simp only [WeakLocalPeak, indepNum_iso e, independentSetCoefficient_iso e]

/-- Every finite graph has a largest coefficient within its natural support. -/
theorem exists_maximum_coefficient {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ k ≤ G.indepNum, ∀ j, independentSetCoefficient G univ j ≤
      independentSetCoefficient G univ k := by
  classical
  obtain ⟨k, hk, hm⟩ := (range (G.indepNum + 1)).exists_max_image
    (independentSetCoefficient G univ) (nonempty_range_iff.mpr (by omega))
  refine ⟨k, by have := mem_range.mp hk; omega, fun j => ?_⟩
  by_cases hj : j ≤ G.indepNum
  · exact hm j (mem_range.mpr (by omega))
  · rw [coefficient_eq_zero_of_gt G univ j (by rw [independenceNumber_univ]; omega)]
    exact Nat.zero_le _

/-- Weak local peaks exist without any unimodality hypothesis. -/
theorem exists_weakLocalPeak {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ k, WeakLocalPeak G k := by
  obtain ⟨k, hk, hm⟩ := exists_maximum_coefficient G
  exact ⟨k, hk, Or.inr (hm (k - 1)), hm (k + 1)⟩

/-- All normalized weak local peak positions of forests of the specified order. -/
def forestPeakRatios (n : ℕ) : Set ℝ :=
  {r | ∃ (G : SimpleGraph (Fin n)) (k : ℕ), G.IsAcyclic ∧ WeakLocalPeak G k ∧
    r = (k : ℝ) / G.indepNum}

/-- All normalized weak local peak positions of trees of the specified order. -/
def treePeakRatios (n : ℕ) : Set ℝ :=
  {r | ∃ (G : SimpleGraph (Fin n)) (k : ℕ), G.IsTree ∧ WeakLocalPeak G k ∧
    r = (k : ℝ) / G.indepNum}

/-- The paper's forest peak-minimum sequence (the zero-order extension is harmless). -/
noncomputable def forestPeakMinimum (n : ℕ) : ℝ := sInf (forestPeakRatios n)

/-- The paper's tree peak-minimum sequence. Only positive orders enter the limit. -/
noncomputable def treePeakMinimum (n : ℕ) : ℝ := sInf (treePeakRatios n)

theorem treePeakRatios_subset (n : ℕ) : treePeakRatios n ⊆ forestPeakRatios n := by
  rintro r ⟨G, k, hG, hk, hr⟩
  exact ⟨G, k, hG.isAcyclic, hk, hr⟩

theorem forestPeakRatios_bddBelow (n : ℕ) : BddBelow (forestPeakRatios n) := by
  refine ⟨0, ?_⟩
  rintro r ⟨G, k, _, _, rfl⟩
  exact div_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg G.indepNum)

theorem treePeakRatios_nonempty {n : ℕ} (hn : 0 < n) : (treePeakRatios n).Nonempty := by
  let G := SimpleGraph.starGraph (⟨0, hn⟩ : Fin n)
  obtain ⟨k, hk⟩ := exists_weakLocalPeak G
  exact ⟨_, G, k, SimpleGraph.isTree_starGraph _, hk, rfl⟩

theorem forestPeakRatios_nonempty {n : ℕ} (hn : 0 < n) : (forestPeakRatios n).Nonempty :=
  (treePeakRatios_nonempty hn).mono (treePeakRatios_subset n)

theorem forestPeakMinimum_le_treePeakMinimum {n : ℕ} (hn : 0 < n) :
    forestPeakMinimum n ≤ treePeakMinimum n :=
  csInf_le_csInf (forestPeakRatios_bddBelow n) (treePeakRatios_nonempty hn)
    (treePeakRatios_subset n)

theorem forestPeakRatios_finite (n : ℕ) : (forestPeakRatios n).Finite := by
  let f : SimpleGraph (Fin n) × Fin (n + 1) → ℝ :=
    fun p => (p.2.val : ℝ) / p.1.indepNum
  apply (Set.finite_range f).subset
  rintro r ⟨G, k, _, hk, rfl⟩
  have ha : G.indepNum ≤ n := by
    obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
    calc G.indepNum = s.card := hs.card_eq.symm
         _ ≤ Fintype.card (Fin n) := card_le_univ s
         _ = n := Fintype.card_fin n
  exact ⟨(G, ⟨k, by have := hk.1; omega⟩), rfl⟩

theorem treePeakRatios_finite (n : ℕ) : (treePeakRatios n).Finite :=
  (forestPeakRatios_finite n).subset (treePeakRatios_subset n)

/-- The infimum notation really is an attained minimum, as in the paper. -/
theorem forestPeakMinimum_mem {n : ℕ} (hn : 0 < n) :
    forestPeakMinimum n ∈ forestPeakRatios n :=
  (forestPeakRatios_nonempty hn).csInf_mem (forestPeakRatios_finite n)

/-- The tree infimum is also attained for every positive order. -/
theorem treePeakMinimum_mem {n : ℕ} (hn : 0 < n) :
    treePeakMinimum n ∈ treePeakRatios n :=
  (treePeakRatios_nonempty hn).csInf_mem (treePeakRatios_finite n)

theorem forestPeakRatios_mem_unitInterval {n : ℕ} {r : ℝ}
    (hr : r ∈ forestPeakRatios n) : r ∈ Set.Icc 0 1 := by
  obtain ⟨G, k, _, hk, rfl⟩ := hr
  refine ⟨div_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg G.indepNum), ?_⟩
  by_cases ha : G.indepNum = 0
  · simp [ha]
  · have ha' : (0 : ℝ) < G.indepNum := Nat.cast_pos.mpr (Nat.pos_of_ne_zero ha)
    apply (div_le_iff₀ ha').mpr
    simpa using (Nat.cast_le.mpr hk.1 : (k : ℝ) ≤ G.indepNum)

theorem forestPeakMinimum_mem_unitInterval {n : ℕ} (hn : 0 < n) :
    forestPeakMinimum n ∈ Set.Icc 0 1 :=
  forestPeakRatios_mem_unitInterval (forestPeakMinimum_mem hn)

theorem treePeakMinimum_mem_unitInterval {n : ℕ} (hn : 0 < n) :
    treePeakMinimum n ∈ Set.Icc 0 1 :=
  forestPeakRatios_mem_unitInterval (treePeakRatios_subset n (treePeakMinimum_mem hn))

end MeanMaximumForests
