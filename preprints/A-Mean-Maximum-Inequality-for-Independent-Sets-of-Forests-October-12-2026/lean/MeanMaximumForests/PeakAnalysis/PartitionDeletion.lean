import HardCoreActivityThreshold.ForestMarginalBounds

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V]

theorem partition_delete_bound (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (hcap : ∀ v, activity v ≤ 1)
    (s U : Finset V) (hU : U ⊆ s) :
    partitionWithin G activity s ≤ (2 : ℝ) ^ U.card * partitionWithin G activity (s \ U) := by
  induction U using Finset.induction_on generalizing s with
  | empty => simp
  | @insert r U hr ih =>
    have hrs : r ∈ s := hU (mem_insert_self _ _)
    have hUs : U ⊆ s.erase r := by
      intro v hv
      exact mem_erase.mpr ⟨by intro he; subst v; exact hr hv, hU (mem_insert_of_mem hv)⟩
    have hm : partitionWithin G activity (Forest.compatibleVertices G s r) ≤
        partitionWithin G activity (s.erase r) :=
      partitionWithin_mono G activity ha (by
        intro v hv
        have h := (Forest.mem_compatibleVertices G).mp hv
        exact mem_erase.mpr ⟨h.1, h.2.1⟩)
    have hmul := mul_le_mul (hcap r) hm (partitionWithin_pos G activity ha _).le (by norm_num : (0 : ℝ) ≤ 1)
    have hstep : partitionWithin G activity s ≤ 2 * partitionWithin G activity (s.erase r) := by
      rw [partitionWithin_recursion G activity s r hrs]
      nlinarith only [hmul]
    have hind := mul_le_mul_of_nonneg_left (ih (s.erase r) hUs) (by norm_num : (0 : ℝ) ≤ 2)
    have hsets : s.erase r \ U = s \ insert r U := by ext v; simp; tauto
    rw [hsets] at hind
    rw [card_insert_of_notMem hr, pow_succ]
    nlinarith only [hstep, hind]

variable [Fintype V]

theorem hardCore_marginal_partition (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (v : V) :
    marginal (hardCoreLaw G activity ha) v = activity v *
      partitionWithin G activity (Forest.compatibleVertices G univ v) / partitionFunction G activity := by
  have hr := partitionWithin_recursion G activity univ v (mem_univ v)
  rw [partitionWithin_univ] at hr
  have habs := hardCore_absence_partition G activity ha v
  rw [absent_eventMass] at habs
  have hz := (partitionFunction_pos G activity (fun v => (ha v).le)).ne'
  field_simp [hz] at habs ⊢
  nlinarith only [hr, habs]

/-- A low-degree vertex remains uniformly occupied under all bounded positive activities. -/
theorem hardCore_low_degree_marginal (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (hlo : ∀ v, (1 / 8 : ℝ) ≤ activity v)
    (hcap : ∀ v, activity v ≤ 1) (v : V) (hdeg : G.degree v ≤ 3) :
    (1 / 128 : ℝ) ≤ marginal (hardCoreLaw G activity ha) v := by
  classical
  let U := insert v (G.neighborFinset v)
  have hcard : U.card ≤ 4 := by
    have hv : v ∉ G.neighborFinset v := by simp
    dsimp [U]
    rw [card_insert_of_notMem hv]
    change G.degree v + 1 ≤ 4
    omega
  have hsets : univ \ U = Forest.compatibleVertices G univ v := by
    ext w
    simp only [mem_sdiff, mem_univ, true_and, U, mem_insert, G.mem_neighborFinset,
      Forest.mem_compatibleVertices]
    tauto
  have hz := partition_delete_bound G activity ha hcap univ U (subset_univ U)
  rw [partitionWithin_univ, hsets] at hz
  have hpow : (2 : ℝ) ^ U.card ≤ 16 := by
    calc
      _ ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hcard
      _ = _ := by norm_num
  have hpart := partitionWithin_pos G activity ha (Forest.compatibleVertices G univ v)
  have hzbound : partitionFunction G activity ≤ 16 * partitionWithin G activity
      (Forest.compatibleVertices G univ v) :=
    hz.trans (mul_le_mul_of_nonneg_right hpow hpart.le)
  rw [hardCore_marginal_partition]
  apply (le_div_iff₀ (partitionFunction_pos G activity (fun v => (ha v).le))).mpr
  have hlo' := mul_le_mul_of_nonneg_right (hlo v) hpart.le
  nlinarith only [hlo', hzbound]

end MeanMaximumForests.PeakAnalysis
