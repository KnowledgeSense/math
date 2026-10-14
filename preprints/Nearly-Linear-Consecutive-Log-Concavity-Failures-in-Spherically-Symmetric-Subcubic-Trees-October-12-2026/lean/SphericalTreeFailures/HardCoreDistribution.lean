import SphericalTreeFailures.HardCoreWeights
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace SphericalTreeFailures
set_option backward.isDefEq.respectTransparency false
open Finset

variable {V : Type*} [Fintype V]

/-- All independent vertex subsets of a finite graph. -/
abbrev IndependentConfiguration (G : SimpleGraph V) :=
  {s : Finset V // s ∈ independentSetsWithin G univ}

noncomputable instance (G : SimpleGraph V) : Fintype (IndependentConfiguration G) := by
  classical
  unfold IndependentConfiguration
  infer_instance

noncomputable def emptyConfiguration (G : SimpleGraph V) : IndependentConfiguration G := by
  classical
  exact ⟨∅, (mem_independentSetsWithin G).mpr ⟨empty_subset _, independent_empty G⟩⟩

noncomputable def configurationPartition (G : SimpleGraph V) (activity : ℝ) : ℝ :=
  ∑ s : IndependentConfiguration G, activity ^ s.val.card

theorem configurationPartition_pos (G : SimpleGraph V) {activity : ℝ} (ha : 0 < activity) :
    0 < configurationPartition G activity := by
  classical
  apply sum_pos'
  · intro s hs
    exact le_of_lt (pow_pos ha _)
  · exact ⟨emptyConfiguration G, mem_univ _, by simp [emptyConfiguration]⟩

theorem configurationPartition_polynomial (G : SimpleGraph V) (activity : ℝ) :
    configurationPartition G activity =
      (independencePolynomial G univ).eval₂ (Nat.castRingHom ℝ) activity := by
  classical
  simp only [configurationPartition, IndependentConfiguration,
    independencePolynomial, Polynomial.eval₂_finsetSum, Polynomial.eval₂_X_pow]
  exact Finset.sum_coe_sort (independentSetsWithin G univ) (fun s : Finset V => activity ^ s.card)

/-- The hard-core distribution on actual independent subsets, normalized by its partition function. -/
noncomputable def hardCore (G : SimpleGraph V) (activity : ℝ) (ha : 0 < activity) :
    PMF (IndependentConfiguration G) := by
  classical
  apply PMF.ofFintype (fun s => ENNReal.ofReal (activity ^ s.val.card / configurationPartition G activity))
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rw [← Finset.sum_div]
    change ENNReal.ofReal (configurationPartition G activity / configurationPartition G activity) = 1
    rw [div_self (ne_of_gt (configurationPartition_pos G ha)), ENNReal.ofReal_one]
  · intro s hs
    exact div_nonneg (le_of_lt (pow_pos ha _)) (le_of_lt (configurationPartition_pos G ha))

theorem hardCore_apply (G : SimpleGraph V) (activity : ℝ) (ha : 0 < activity)
    (s : IndependentConfiguration G) :
    hardCore G activity ha s = ENNReal.ofReal
      (activity ^ s.val.card / configurationPartition G activity) := rfl

/-- The size law of the hard-core distribution has the actual graph coefficients. -/
theorem hardCore_size_probability (G : SimpleGraph V) (activity : ℝ) (ha : 0 < activity) (j : ℕ) :
    ((hardCore G activity ha).map (fun s => s.val.card)) j =
      ENNReal.ofReal (((independencePolynomial G univ).coeff j : ℝ) * activity ^ j /
        configurationPartition G activity) := by
  classical
  have hz := configurationPartition_pos G ha
  rw [PMF.map_apply, tsum_fintype]
  simp only [hardCore_apply]
  have ht (s : IndependentConfiguration G) :
      (if j = s.val.card then ENNReal.ofReal (activity ^ s.val.card / configurationPartition G activity) else 0) =
      ENNReal.ofReal (if s.val.card = j then activity ^ j / configurationPartition G activity else 0) := by
    by_cases h : s.val.card = j
    · simp [h]
    · rw [ite_eq_right (Ne.symm h), ite_eq_right h, ENNReal.ofReal_zero]
  simp_rw [ht]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun s hs => by
    split_ifs <;> positivity)]
  apply congrArg ENNReal.ofReal
  rw [independencePolynomial_coeff]
  change (∑ s : IndependentConfiguration G,
    if s.val.card = j then activity ^ j / configurationPartition G activity else 0) = _
  rw [show (∑ s : IndependentConfiguration G,
      if s.val.card = j then activity ^ j / configurationPartition G activity else 0) =
      ∑ s ∈ independentSetsWithin G univ,
        if s.card = j then activity ^ j / configurationPartition G activity else 0 from
    Finset.sum_coe_sort (independentSetsWithin G univ)
      (fun s : Finset V => if s.card = j then activity ^ j / configurationPartition G activity else 0)]
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul]
  ring

end SphericalTreeFailures
