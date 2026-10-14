import HardCoreActivityThreshold.FiniteProbability
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat

/-! Elementary bounds for global modes of integer-valued finite probability laws.
These lemmas make no assertion that a weak local peak is a global mode. -/
namespace MeanMaximumForests
open Finset HardCoreActivityThreshold

/-- A set of integers in a real interval of radius `r` has at most `2*r+1` elements. -/
theorem nat_span_card (s : Finset ℕ) (m r : ℝ) (hr : 0 ≤ r)
    (hs : ∀ k ∈ s, |(k : ℝ) - m| ≤ r) : (s.card : ℝ) ≤ 2 * r + 1 := by
  classical
  by_cases he : s.Nonempty
  · let a := s.min' he
    let b := s.max' he
    have ha : a ∈ s := s.min'_mem he
    have hb : b ∈ s := s.max'_mem he
    have hab : a ≤ b := s.min'_le _ hb
    have hsub : s ⊆ Icc a b := by
      intro k hk
      exact mem_Icc.mpr ⟨s.min'_le _ hk, s.le_max' _ hk⟩
    have hc := card_le_card hsub
    rw [Nat.card_Icc] at hc
    have hcast : (s.card : ℝ) ≤ (b : ℝ) + 1 - a := by
      have hcast := (Nat.cast_le (α := ℝ)).mpr hc
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one] at hcast
      exact hcast
    have hla := (abs_le.mp (hs a ha)).1
    have hub := (abs_le.mp (hs b hb)).2
    linarith
  · rw [not_nonempty_iff_eq_empty.mp he]
    simp only [card_empty, Nat.cast_zero]
    linarith

theorem fin_span_card {N : ℕ} (s : Finset (Fin N)) (m r : ℝ) (hr : 0 ≤ r)
    (hs : ∀ k ∈ s, |(k.val : ℝ) - m| ≤ r) : (s.card : ℝ) ≤ 2 * r + 1 := by
  have hc := nat_span_card (s.image Fin.val) m r hr (by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hk
    exact hs j hj)
  rw [card_image_of_injective _ Fin.val_injective] at hc
  exact hc

/-- Chebyshev and a counting argument localize every global mode. -/
theorem global_mode_squared_distance {N : ℕ} (μ : FiniteLaw (Fin N)) (k : Fin N)
    (hmode : ∀ j, μ.mass j ≤ μ.mass k) (r : ℝ) (hr : 0 < r)
    (hvar : 2 * μ.variance (fun j => (j.val : ℝ)) ≤ r ^ 2) :
    ((k.val : ℝ) - μ.expectation (fun j => (j.val : ℝ))) ^ 2 ≤
      2 * (2 * r + 1) * μ.variance (fun j => (j.val : ℝ)) := by
  classical
  let m := μ.expectation (fun j => (j.val : ℝ))
  let S : Finset (Fin N) := univ.filter (fun j => |(j.val : ℝ) - m| ≤ r)
  let T : Finset (Fin N) := univ \ S
  have hmS : 0 ≤ ∑ j ∈ S, μ.mass j := sum_nonneg (fun j _ => μ.nonneg j)
  have hmT : 0 ≤ ∑ j ∈ T, μ.mass j := sum_nonneg (fun j _ => μ.nonneg j)
  have htotal : (∑ j ∈ S, μ.mass j) + (∑ j ∈ T, μ.mass j) = 1 := by
    rw [add_comm, sum_sdiff (subset_univ S), μ.sum_one]
  have htail : r ^ 2 * (∑ j ∈ T, μ.mass j) ≤ μ.variance (fun j => (j.val : ℝ)) := by
    calc
      _ = ∑ j ∈ T, μ.mass j * r ^ 2 := by rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ ≤ ∑ j ∈ T, μ.mass j * ((j.val : ℝ) - m) ^ 2 := by
        apply sum_le_sum
        intro j hj
        have hj' : r < |(j.val : ℝ) - m| := by
          have hnot := (mem_sdiff.mp hj).2
          simpa only [S, mem_filter, mem_univ, true_and, not_le] using hnot
        apply mul_le_mul_of_nonneg_left _ (μ.nonneg j)
        nlinarith [sq_abs ((j.val : ℝ) - m)]
      _ ≤ μ.variance (fun j => (j.val : ℝ)) := by
        exact sum_le_sum_of_subset_of_nonneg (subset_univ T) (fun j _ _ =>
          mul_nonneg (μ.nonneg j) (sq_nonneg _))
  have hhalf : 1 / 2 ≤ ∑ j ∈ S, μ.mass j := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
    nlinarith
  have hcard : (S.card : ℝ) ≤ 2 * r + 1 :=
    fin_span_card S m r hr.le (fun j hj => (mem_filter.mp hj).2)
  have hmass : 1 / 2 ≤ (2 * r + 1) * μ.mass k := by
    calc
      _ ≤ ∑ j ∈ S, μ.mass j := hhalf
      _ ≤ ∑ _j ∈ S, μ.mass k := sum_le_sum (fun j _ => hmode j)
      _ = (S.card : ℝ) * μ.mass k := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (μ.nonneg k)
  have hpoint : μ.mass k * ((k.val : ℝ) - m) ^ 2 ≤
      μ.variance (fun j => (j.val : ℝ)) := by
    change μ.mass k * ((k.val : ℝ) - m) ^ 2 ≤ ∑ j, μ.mass j * ((j.val : ℝ) - m) ^ 2
    exact single_le_sum (fun j _ => mul_nonneg (μ.nonneg j) (sq_nonneg ((j.val : ℝ) - m))) (mem_univ k)
  have hnonneg : 0 ≤ ((k.val : ℝ) - m) ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hmass hnonneg
  have hmul' := mul_le_mul_of_nonneg_left hpoint (by linarith : 0 ≤ 2 * r + 1)
  change ((k.val : ℝ) - m) ^ 2 ≤ _
  nlinarith

end MeanMaximumForests
