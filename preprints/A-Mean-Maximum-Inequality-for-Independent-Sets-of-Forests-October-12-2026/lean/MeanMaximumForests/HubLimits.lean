import MeanMaximumForests.HubTrees
import Mathlib.Analysis.SpecificLimits.Basic

namespace MeanMaximumForests.HubTrees
open Filter
open scoped Topology

theorem hubOccupation_nonneg (A : ForestExpr) (k r : ℕ) :
    0 ≤ hubOccupation A k r := by
  unfold hubOccupation
  have hq := pow_nonneg (rootAvoidance_pos A).le k
  exact div_nonneg hq (add_nonneg (by positivity) hq)

theorem hubOccupation_le (A : ForestExpr) (k r : ℕ) :
    hubOccupation A k r ≤ rootAvoidance A ^ k := by
  apply div_le_self (pow_nonneg (rootAvoidance_pos A).le _)
  have h : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  have hq : 0 ≤ rootAvoidance A ^ k := pow_nonneg (rootAvoidance_pos A).le _
  linarith

theorem hubOccupation_tendsto (A : ForestExpr) (hA : 0 < A.statistics.vertices)
    (k r : ℕ → ℕ) (hk : Tendsto k atTop atTop) :
    Tendsto (fun n => hubOccupation A (k n) (r n)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => hubOccupation_nonneg A (k n) (r n))
    (fun n => hubOccupation_le A (k n) (r n))
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (rootAvoidance_pos A).le
    (rootAvoidance_lt_one A hA)).comp hk

/-- A uniformly bounded number of padding leaves is negligible compared with the copies. -/
theorem bounded_padding_div_tendsto (k r : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (R : ℕ) (hr : ∀ n, r n ≤ R) :
    Tendsto (fun n => (r n : ℝ) / k n) atTop (𝓝 0) := by
  have hi : Tendsto (fun n => (k n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hk)
  apply squeeze_zero (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun n => div_le_div_of_nonneg_right (Nat.cast_le.mpr (hr n)) (Nat.cast_nonneg (k n)))
  simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul hi

theorem eventually_copies_pos (k : ℕ → ℕ) (hk : Tendsto k atTop atTop) :
    ∀ᶠ n in atTop, 0 < k n := hk.eventually (eventually_gt_atTop 0)

/-- The exact finite hub formula gives the desired mean per copy, with arbitrary bounded padding. -/
theorem hub_mean_per_copy_tendsto (A : ForestExpr) (hA : 0 < A.statistics.vertices)
    (k r : ℕ → ℕ) (hk : Tendsto k atTop atTop) (R : ℕ) (hr : ∀ n, r n ≤ R) :
    Tendsto (fun n => graphMean (hub A (k n) (r n)).graph / k n) atTop (𝓝 A.mean) := by
  have hi : Tendsto (fun n => (1 : ℝ) / k n) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hk) :
        Tendsto (fun n => (k n : ℝ)⁻¹) atTop (𝓝 0))
  have hp := (bounded_padding_div_tendsto k r hk R hr).div_const 2
  have ho := hubOccupation_tendsto A hA k r hk
  have ht : Tendsto (fun n => A.mean + (r n : ℝ) / k n / 2 +
      hubOccupation A (k n) (r n) *
        (1 / (k n : ℝ) + A.deletedMean - A.mean - (r n : ℝ) / k n / 2))
      atTop (𝓝 A.mean) := by
    simpa using (tendsto_const_nhds.add hp).add
      (ho.mul (((hi.add tendsto_const_nhds).sub tendsto_const_nhds).sub hp))
  apply ht.congr'
  filter_upwards [eventually_copies_pos k hk] with n hn
  have hn' : (k n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  rw [hub_mean]
  field_simp
  ring

/-- The hub changes the normalized independence number by a vanishing amount. -/
theorem hub_alpha_per_copy_tendsto (A : ForestExpr) (k r : ℕ → ℕ)
    (hk : Tendsto k atTop atTop) (R : ℕ) (hr : ∀ n, r n ≤ R) :
    Tendsto (fun n => ((hub A (k n) (r n)).graph.indepNum : ℝ) / k n)
      atTop (𝓝 (A.statistics.alpha : ℝ)) := by
  have hpad := bounded_padding_div_tendsto k (fun n => r n + 1) hk (R + 1)
    (fun n => Nat.add_le_add_right (hr n) 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using (tendsto_const_nhds.add hpad))
  · filter_upwards [eventually_copies_pos k hk] with n hn
    have hk' : (0 : ℝ) < k n := Nat.cast_pos.mpr hn
    apply (le_div_iff₀ hk').mpr
    have hb := (hub_alpha_bounds A (k n) (r n)).1
    have hb' : (k n : ℝ) * A.statistics.alpha + r n ≤ (hub A (k n) (r n)).graph.indepNum :=
      by exact_mod_cast hb
    nlinarith [(Nat.cast_nonneg (r n) : (0 : ℝ) ≤ r n)]
  · filter_upwards [eventually_copies_pos k hk] with n hn
    have hk' : (0 : ℝ) < k n := Nat.cast_pos.mpr hn
    apply (div_le_iff₀ hk').mpr
    have hb := (hub_alpha_bounds A (k n) (r n)).2
    have hb' : ((hub A (k n) (r n)).graph.indepNum : ℝ) ≤
        (k n : ℝ) * A.statistics.alpha + r n + 1 := by exact_mod_cast hb
    have hcancel : (A.statistics.alpha + ((r n : ℝ) + 1) / k n) * k n =
        (k n : ℝ) * A.statistics.alpha + r n + 1 := by
      field_simp
      ring
    rwa [hcancel]

/-- Hub trees asymptotically preserve the mean/maximum ratio of their component forest. -/
theorem hub_ratio_tendsto (A : ForestExpr) (hA : 0 < A.statistics.vertices)
    (ha : 0 < A.statistics.alpha) (k r : ℕ → ℕ)
    (hk : Tendsto k atTop atTop) (R : ℕ) (hr : ∀ n, r n ≤ R) :
    Tendsto (fun n => graphMean (hub A (k n) (r n)).graph /
      (hub A (k n) (r n)).graph.indepNum) atTop (𝓝 (A.mean / A.statistics.alpha)) := by
  have ht := (hub_mean_per_copy_tendsto A hA k r hk R hr).div
    (hub_alpha_per_copy_tendsto A k r hk R hr) (ne_of_gt (Nat.cast_pos.mpr ha))
  apply ht.congr'
  filter_upwards [eventually_copies_pos k hk] with n hn
  exact div_div_div_cancel_right₀ (ne_of_gt (Nat.cast_pos.mpr hn)) _ _

/-- The quotient-and-remainder hub construction has every positive integer order. -/
def allOrders (A : ForestExpr) (n : ℕ) : ForestExpr :=
  hub A ((n - 1) / A.statistics.vertices) ((n - 1) % A.statistics.vertices)

theorem allOrders_isTree (A : ForestExpr) (n : ℕ) : (allOrders A n).graph.IsTree :=
  hub_isTree A _ _

theorem allOrders_card (A : ForestExpr) (n : ℕ) (hn : 0 < n) :
    Fintype.card (allOrders A n).Vertex = n := by
  rw [allOrders, hub_vertices]
  have he : (n - 1) / A.statistics.vertices * A.statistics.vertices +
      (n - 1) % A.statistics.vertices = n - 1 := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod (n - 1) A.statistics.vertices
  omega

theorem allOrders_ratio_tendsto (A : ForestExpr) (hA : 0 < A.statistics.vertices)
    (ha : 0 < A.statistics.alpha) :
    Tendsto (fun n => graphMean (allOrders A n).graph / (allOrders A n).graph.indepNum)
      atTop (𝓝 (A.mean / A.statistics.alpha)) := by
  apply hub_ratio_tendsto A hA ha
    (fun n => (n - 1) / A.statistics.vertices) (fun n => (n - 1) % A.statistics.vertices)
  · exact (Nat.tendsto_div_const_atTop (Nat.ne_of_gt hA)).comp (tendsto_sub_atTop_nat 1)
  · intro n
    exact (Nat.mod_lt (n - 1) hA).le

end MeanMaximumForests.HubTrees
