import ArithmeticSections.OddDistances
import Mathlib.Topology.Order.Lattice

namespace ArithmeticSections

/-- The smallest of δ₁,…,δₖ; the unused empty case is zero. -/
noncomputable def firstDistance (γ : ℝ) (k : ℕ) : ℝ :=
  if hk : 0 < k then
    (Finset.range k).inf' (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hk)) (fun i => oddDistance γ (i + 1))
  else 0

noncomputable def rotationRadius (γ : ℝ) : ℝ := (Real.cos (Real.pi * γ))⁻¹

theorem firstDistance_le {γ : ℝ} {k r : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) :
    firstDistance γ k ≤ oddDistance γ r := by
  have hk : 0 < k := by omega
  unfold firstDistance
  rw [dite_eq_left hk]
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  exact Finset.inf'_le _ (Finset.mem_range.mpr (by omega))

theorem firstDistance_pos {γ : ℝ} (hγ : Irrational γ) {k : ℕ} (hk : 1 ≤ k) :
    0 < firstDistance γ k := by
  unfold firstDistance
  rw [dite_eq_left (show 0 < k by omega), Finset.lt_inf'_iff]
  intro i _
  exact (oddDistance_bounds hγ (by omega : 1 ≤ i + 1)).1

theorem firstDistance_attained {γ : ℝ} {k : ℕ} (hk : 1 ≤ k) :
    ∃ i, i < k ∧ firstDistance γ k = oddDistance γ (i + 1) := by
  have hk' : 0 < k := by omega
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf'
    (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hk')) (fun i => oddDistance γ (i + 1))
  exact ⟨i, Finset.mem_range.mp hi, by simpa only [firstDistance, dite_eq_left hk'] using he⟩

theorem continuous_firstDistance (k : ℕ) : Continuous (fun γ => firstDistance γ k) := by
  by_cases hk : 0 < k
  · simp only [firstDistance, dite_eq_left hk]
    exact Continuous.finset_inf'_apply _ (fun _ _ => continuous_oddDistance _)
  · simpa only [firstDistance, dite_eq_right hk] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))

/-- The order-statistic and radius assertions of Lemma 2.1(2), in γ coordinates. -/
theorem firstDistance_bounds_and_radius {γ : ℝ} (hγ : Irrational γ)
    (hlo : 1 / 3 < γ) (hhi : γ < 1 / 2) {k : ℕ} (hk : 2 ≤ k) :
    firstDistance γ k ≤ oddDistance γ 2 ∧
    oddDistance γ 2 < oddDistance γ 1 ∧
    oddDistance γ 1 = Real.pi * γ ∧
    1 < rotationRadius γ * Real.cos (firstDistance γ k) := by
  have hs := firstDistance_le (γ := γ) (by omega : 1 ≤ 2) hk
  have ho := oddDistance_two_lt_one hlo hhi
  have he := oddDistance_one hlo hhi
  have hpos := firstDistance_pos hγ (by omega : 1 ≤ k)
  have hangle : firstDistance γ k < Real.pi * γ := by linarith
  have hanglehalf : Real.pi * γ < Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hcospos : 0 < Real.cos (Real.pi * γ) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hanglehalf⟩
  refine ⟨hs, ho, he, ?_⟩
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two hpos.le hanglehalf.le hangle
  unfold rotationRadius
  rw [mul_comm, ← div_eq_mul_inv]
  exact (one_lt_div hcospos).mpr hcos

end ArithmeticSections
