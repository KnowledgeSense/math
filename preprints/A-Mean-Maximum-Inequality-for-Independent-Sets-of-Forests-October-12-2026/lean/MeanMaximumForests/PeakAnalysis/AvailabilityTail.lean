import MeanMaximumForests.PeakAnalysis.BipartiteMixture
import MeanMaximumForests.PeakAnalysis.PartitionHalving
import MeanMaximumForests.PeakAnalysis.FiniteConcentration

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem availability_partition_ratio (G : SimpleGraph V) (L R : Finset V)
    (hL : Independent G L) (hR : Independent G R) (hd : Disjoint L R) (hc : L ∪ R = univ)
    (z : ℝ) (hz : 0 < z) :
    (bipartiteMixLaw G L R hL hR hd hc z hz).expectation
      (fun r => ((1 + z / 2) / (1 + z)) ^ (availableIn G L r.val).card) =
      partitionFunction G (twoColorActivity L (z / 2) z) / partitionFunction G (fun _ => z) := by
  unfold FiniteLaw.expectation bipartiteMixLaw
  simp only [div_mul_eq_mul_div, ← sum_div]
  congr 1
  rw [finite_subtype_sum (fun r : Finset V => r ⊆ R)
    (fun r => z ^ r.card * (1 + z) ^ (availableIn G L r).card *
      ((1 + z / 2) / (1 + z)) ^ (availableIn G L r).card), sum_subsets,
    bipartite_partition G L R hL hR hd hc (z / 2) z]
  apply sum_congr rfl
  intro r _
  rw [div_pow]
  field_simp

/-- With exponentially high probability, the conditional binomial block contains a linear number of vertices. -/
theorem availability_small_probability (G : SimpleGraph V) (L R : Finset V)
    (hL : Independent G L) (hR : Independent G R) (hd : Disjoint L R) (hc : L ∪ R = univ)
    (z : ℝ) (hz : (1 / 4 : ℝ) ≤ z) (hz1 : z ≤ 1)
    (hcount : Fintype.card V ≤ 4 * (L.filter (fun v => G.degree v ≤ 3)).card) :
    (bipartiteMixLaw G L R hL hR hd hc z (by linarith)).eventMass
      (fun r => ((availableIn G L r.val).card : ℝ) ≤ (Fintype.card V : ℝ) / 1024) ≤
        Real.exp (-Real.log 2 * (Fintype.card V : ℝ) / 1024) := by
  have hz0 : 0 < z := by linarith
  let μ := bipartiteMixLaw G L R hL hR hd hc z hz0
  let θ := (1 + z / 2) / (1 + z)
  let a := Real.exp (-Real.log 2 * (Fintype.card V : ℝ) / 1024)
  have ha : 0 < a := Real.exp_pos _
  have hθ : (1 / 2 : ℝ) ≤ θ := by
    dsimp [θ]
    apply (le_div_iff₀ (by positivity : 0 < 1 + z)).mpr
    linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hehalf : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  let E := fun r : {r : Finset V // r ⊆ R} =>
    ((availableIn G L r.val).card : ℝ) ≤ (Fintype.card V : ℝ) / 1024
  have hpoint (r : {r : Finset V // r ⊆ R}) :
      a * (if E r then 1 else 0) ≤ θ ^ (availableIn G L r.val).card := by
    by_cases hr : E r
    · rw [ite_eq_left hr, mul_one]
      calc
        a ≤ Real.exp (-Real.log 2 * (availableIn G L r.val).card) := by
          apply Real.exp_le_exp.mpr
          dsimp [a, E] at *
          nlinarith only [mul_le_mul_of_nonneg_left hr hlog.le]
        _ = (1 / 2 : ℝ) ^ (availableIn G L r.val).card := by
          rw [mul_comm, Real.exp_nat_mul, hehalf]
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) hθ _
    · rw [ite_eq_right hr, mul_zero]
      exact pow_nonneg (by linarith) _
  have hE := μ.expectation_mono hpoint
  rw [FiniteLaw.expectation_smul, ← eventMass_eq_indicator] at hE
  have hratio := availability_partition_ratio G L R hL hR hd hc z hz0
  have htail := partition_halving_bound G L z hz hz1 hcount
  have hpow : Real.exp (-Real.log 2 * (Fintype.card V : ℝ) / 512) = a * a := by
    dsimp [a]
    rw [← Real.exp_add]
    congr 1
    ring
  have hm : a * μ.eventMass E ≤ a * a := hE.trans (by
    change μ.expectation (fun r => θ ^ (availableIn G L r.val).card) ≤ _
    rw [hratio]
    exact htail.trans_eq hpow)
  exact (mul_le_mul_iff_right₀ ha).mp hm

end MeanMaximumForests.PeakAnalysis
