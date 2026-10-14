import ArithmeticSections.CylinderExclusions

namespace ArithmeticSections
open Set Filter
open scoped Topology

/-- A cylinder's diameter tends to zero with its convergent denominator. -/
theorem dist_le_inv_denominator_of_mem_digitCylinder {b : ℕ → ℕ}
    (hb : ∀ n, 1 ≤ b (n + 1)) (n : ℕ) {x y : ℝ}
    (hx : x ∈ digitCylinder b (n + 1)) (hy : y ∈ digitCylinder b (n + 1)) :
    dist x y ≤ 1 / (denominator b (n + 1) : ℝ) := by
  rw [digitCylinder_eq_cylinderInterval hb n] at hx hy
  have hd := Real.dist_le_of_mem_uIcc (Set.Ioo_subset_Icc_self hx.1) (Set.Ioo_subset_Icc_self hy.1)
  have hq : (0 : ℝ) < denominator b (n + 1) := by exact_mod_cast denominator_pos hb (n + 1)
  have hq1 : (1 : ℝ) ≤ denominator b (n + 1) := by exact_mod_cast denominator_pos hb (n + 1)
  have hr : (0 : ℝ) ≤ denominator b n := by positivity
  calc
    dist x y ≤ |cylinderMap b n 1 - cylinderMap b n 0| := by
      simpa only [Real.dist_eq, abs_sub_comm] using hd
    _ = 1 / ((denominator b (n + 1) : ℝ) *
        ((denominator b (n + 1) : ℝ) + denominator b n)) := by
      simpa only [mul_one] using cylinderMap_initial_length hb n (show (0 : ℝ) ≤ 1 by norm_num)
    _ ≤ 1 / (denominator b (n + 1) : ℝ) := by
      apply (div_le_div_iff₀ (by positivity) hq).mpr
      nlinarith

/-- Arbitrarily deep cylinders of the actual digits fit in every neighborhood. -/
theorem exists_digitCylinder_subset_nhds {θ : ℝ} (hθ : Irrational θ)
    (hθ01 : θ ∈ Ioo (0 : ℝ) 1) {V : Set ℝ} (hV : V ∈ 𝓝 θ) (N : ℕ) :
    ∃ L, N ≤ L ∧ digitCylinder (actualDigit θ) L ⊆ V := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  let n := 2 * (m + N)
  have hb := one_le_actualDigit_succ hθ
  have hq : m + 1 ≤ denominator (actualDigit θ) (n + 1) := by
    have hg := exponential_le_denominator hb (n + 1)
    have he : (n + 1) / 2 = m + N := by dsimp [n]; omega
    rw [he] at hg
    have hp := (m + N).lt_two_pow_self
    omega
  have hc : θ ∈ digitCylinder (actualDigit θ) (n + 1) :=
    ⟨hθ, hθ01, fun _ _ _ => rfl⟩
  refine ⟨n + 1, by dsimp [n]; omega, ?_⟩
  intro x hx
  apply hball
  apply lt_of_le_of_lt (dist_le_inv_denominator_of_mem_digitCylinder hb n hx hc)
  apply lt_of_le_of_lt _ hm
  have hq' : (m : ℝ) + 1 ≤ denominator (actualDigit θ) (n + 1) := by exact_mod_cast hq
  exact one_div_le_one_div_of_le (by positivity) hq'

/-- Every neighborhood contains a Borel positive-measure set whose actual later digits
satisfy the quadratic bound, with an arbitrarily long fixed initial prefix. -/
theorem exists_positive_boundedTailCylinder_subset_nhds {θ : ℝ} (hθ : Irrational θ)
    (hθ01 : θ ∈ Ioo (0 : ℝ) 1) {V : Set ℝ} (hV : V ∈ 𝓝 θ) (N : ℕ) :
    ∃ L, N ≤ L ∧ 3 ≤ L ∧
      MeasurableSet (boundedTailCylinder (actualDigit θ) L) ∧
      0 < MeasureTheory.volume (boundedTailCylinder (actualDigit θ) L) ∧
      boundedTailCylinder (actualDigit θ) L ⊆ V := by
  obtain ⟨L, hL, hsub⟩ := exists_digitCylinder_subset_nhds hθ hθ01 hV (max N 3)
  have hN : N ≤ L := (le_max_left _ _).trans hL
  have h3 : 3 ≤ L := (le_max_right _ _).trans hL
  exact ⟨L, hN, h3, measurableSet_boundedTailCylinder _ _,
    volume_boundedTailCylinder_pos (one_le_actualDigit_succ hθ) h3,
    fun _ hx => hsub hx.1⟩

end ArithmeticSections
