import MeanMaximumForests.PeakAnalysis.ActivityBlockTilt
import MeanMaximumForests.PeakAnalysis.BipartitePartition

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem blockActivity_bounds (activity : V → ℝ) (L : Finset V) (t : ℝ)
    (hlo : ∀ v, (1 / 4 : ℝ) ≤ activity v) (hcap : ∀ v, activity v ≤ 1)
    (ht : t ∈ Set.Icc (-Real.log 2) 0) :
    ∀ v, (1 / 8 : ℝ) ≤ blockActivity activity L t v ∧ blockActivity activity L t v ≤ 1 := by
  have he : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hlow : (1 / 2 : ℝ) ≤ Real.exp t := by rw [← he]; exact Real.exp_le_exp.mpr ht.1
  have hupp : Real.exp t ≤ 1 := Real.exp_le_one_iff.mpr ht.2
  intro v
  by_cases hv : v ∈ L
  · change (1 / 8 : ℝ) ≤ activity v * (if v ∈ L then Real.exp t else 1) ∧ _
    rw [ite_eq_left hv]
    have ha : 0 ≤ activity v := by linarith [hlo v]
    constructor
    · have h := mul_le_mul (hlo v) hlow (by norm_num : (0 : ℝ) ≤ 1 / 2) ha
      norm_num at h
      exact h
    · simpa only [blockActivity, hv, ↓reduceIte, one_mul] using
        (mul_le_mul (hcap v) hupp (Real.exp_pos t).le (by norm_num : (0 : ℝ) ≤ 1))
  · simp only [blockActivity, hv, ↓reduceIte, mul_one]
    constructor
    · linarith [hlo v]
    · exact hcap v

theorem hardCore_block_mean_lower (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (hlo : ∀ v, (1 / 8 : ℝ) ≤ activity v)
    (hcap : ∀ v, activity v ≤ 1) (L : Finset V)
    (hcount : Fintype.card V ≤ 4 * (L.filter (fun v => G.degree v ≤ 3)).card) :
    (Fintype.card V : ℝ) / 512 ≤ (hardCoreLaw G activity ha).expectation (blockCard L) := by
  rw [expectation_blockCard]
  let D := L.filter (fun v => G.degree v ≤ 3)
  have hsum : (D.card : ℝ) / 128 ≤ ∑ v ∈ D, marginal (hardCoreLaw G activity ha) v := by
    have h := sum_le_sum (s := D) (f := fun _ => (1 / 128 : ℝ))
      (g := fun v => marginal (hardCoreLaw G activity ha) v) (fun v hv =>
        hardCore_low_degree_marginal G activity ha hlo hcap v (mem_filter.mp hv).2)
    simpa only [sum_const, nsmul_eq_mul, div_eq_mul_inv, one_mul] using h
  have hsum' : (∑ v ∈ D, marginal (hardCoreLaw G activity ha) v) ≤
      ∑ v ∈ L, marginal (hardCoreLaw G activity ha) v :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun v _ _ => marginal_nonneg _ v)
  have hcount' : (Fintype.card V : ℝ) ≤ 4 * (D.card : ℝ) := by exact_mod_cast hcount
  linarith

/-- Halving the activities on a color class with many low-degree vertices costs an exponential factor. -/
theorem partition_halving_bound (G : SimpleGraph V) (L : Finset V) (z : ℝ)
    (hz : (1 / 4 : ℝ) ≤ z) (hz1 : z ≤ 1)
    (hcount : Fintype.card V ≤ 4 * (L.filter (fun v => G.degree v ≤ 3)).card) :
    partitionFunction G (twoColorActivity L (z / 2) z) /
      partitionFunction G (fun _ => z) ≤ Real.exp (-Real.log 2 * (Fintype.card V : ℝ) / 512) := by
  have hz0 : 0 < z := by linarith
  let activity : V → ℝ := fun _ => z
  have ha : ∀ v, 0 < activity v := fun _ => hz0
  have ht0 : -Real.log 2 ≤ (0 : ℝ) := by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
  have hmean : ∀ t ∈ Set.Icc (-Real.log 2) 0,
      (Fintype.card V : ℝ) / 512 ≤ (finiteTilt (hardCoreLaw G activity ha) (blockCard L) t).expectation (blockCard L) := by
    intro t ht
    rw [finiteTilt_blockActivity]
    have hb := blockActivity_bounds activity L t (fun _ => hz) (fun _ => hz1) ht
    exact hardCore_block_mean_lower G _ (blockActivity_pos activity ha L t)
      (fun v => (hb v).1) (fun v => (hb v).2) L hcount
  have h := tiltPartition_le_exp_of_mean_lower (hardCoreLaw G activity ha) (blockCard L)
    (-Real.log 2) ((Fintype.card V : ℝ) / 512) ht0 hmean
  rw [block_tiltPartition] at h
  have he : blockActivity activity L (-Real.log 2) = twoColorActivity L (z / 2) z := by
    funext v
    unfold blockActivity twoColorActivity
    dsimp [activity]
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    split_ifs <;> ring
  rw [he] at h
  convert h using 1
  congr 1
  ring

end MeanMaximumForests.PeakAnalysis
