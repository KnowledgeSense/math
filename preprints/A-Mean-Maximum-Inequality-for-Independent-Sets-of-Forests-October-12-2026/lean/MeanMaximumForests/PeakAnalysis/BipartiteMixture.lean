import MeanMaximumForests.PeakAnalysis.BipartitePartition
import MeanMaximumForests.PeakAnalysis.BinomialMoments

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem binomial_expectation_powerset (S : Finset V) (z : ℝ) (hz : 0 < z) (f : ℕ → ℝ) :
    (∑ l ∈ S.powerset, z ^ l.card * f l.card) =
      (1 + z) ^ S.card * (binomialSizeLaw S.card z hz).expectation (fun k => f k.val) := by
  rw [sum_powerset_apply_card (fun j => z ^ j * f j)]
  unfold FiniteLaw.expectation binomialSizeLaw binomialSizeMass
  rw [Finset.sum_fin_eq_sum_range, mul_sum]
  apply sum_congr rfl
  intro k hk
  simp only [dite_eq_left (mem_range.mp hk), nsmul_eq_mul]
  field_simp

omit [Fintype V] in
theorem twoColorActivity_same (L : Finset V) (z : ℝ) : twoColorActivity L z z = fun _ => z := by
  funext v
  simp [twoColorActivity]

noncomputable def bipartiteMixLaw (G : SimpleGraph V) (L R : Finset V)
    (hL : Independent G L) (hR : Independent G R) (hd : Disjoint L R) (hc : L ∪ R = univ)
    (z : ℝ) (hz : 0 < z) : FiniteLaw {r : Finset V // r ⊆ R} where
  mass r := z ^ r.val.card * (1 + z) ^ (availableIn G L r.val).card / partitionFunction G (fun _ => z)
  nonneg r := by
    have hZ := partitionFunction_pos G (fun _ => z) (fun _ => hz.le)
    positivity
  sum_one := by
    rw [← sum_div, finite_subtype_sum (fun r : Finset V => r ⊆ R)
      (fun r => z ^ r.card * (1 + z) ^ (availableIn G L r).card), sum_subsets]
    rw [← bipartite_partition G L R hL hR hd hc z z, twoColorActivity_same]
    exact div_self (partitionFunction_pos G (fun _ => z) (fun _ => hz.le)).ne'

/-- An exact mixture identity for every function of the genuine independent-set cardinality. -/
theorem bipartite_cardinality_mixture (G : SimpleGraph V) (L R : Finset V)
    (hL : Independent G L) (hR : Independent G R) (hd : Disjoint L R) (hc : L ∪ R = univ)
    (z : ℝ) (hz : 0 < z) (f : ℕ → ℝ) :
    (hardCoreLaw G (fun _ => z) (fun _ => hz)).expectation (fun I => f I.card) =
      (bipartiteMixLaw G L R hL hR hd hc z hz).expectation
        (fun r => (binomialSizeLaw (availableIn G L r.val).card z hz).expectation
          (fun k => f (r.val.card + k.val))) := by
  let b : Finset V → ℝ := fun r =>
    (binomialSizeLaw (availableIn G L r).card z hz).expectation (fun k => f (r.card + k.val))
  have hleft : (hardCoreLaw G (fun _ => z) (fun _ => hz)).expectation (fun I => f I.card) =
      (∑ I : Finset V, configurationWeight G (fun _ => z) I * f I.card) /
        partitionFunction G (fun _ => z) := by
    unfold FiniteLaw.expectation
    simp only [hardCoreLaw_mass, div_mul_eq_mul_div, ← sum_div]
  rw [hleft]
  change _ = ∑ r : {r : Finset V // r ⊆ R},
    (z ^ r.val.card * (1 + z) ^ (availableIn G L r.val).card /
      partitionFunction G (fun _ => z)) * b r.val
  simp_rw [div_mul_eq_mul_div]
  rw [← sum_div]
  congr 1
  rw [finite_subtype_sum (fun r : Finset V => r ⊆ R)
    (fun r => z ^ r.card * (1 + z) ^ (availableIn G L r).card * b r), sum_subsets]
  have he : (fun _ : V => z) = twoColorActivity L z z := (twoColorActivity_same L z).symm
  rw [he, bipartite_weighted_sum G L R hL hR hd hc]
  apply sum_congr rfl
  intro r _
  rw [binomial_expectation_powerset (availableIn G L r) z hz (fun k => f (r.card + k))]
  dsimp [b]
  ring

end MeanMaximumForests.PeakAnalysis
