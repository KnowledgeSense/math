import R34.CountsCoefficients
import R34.FourStateReduction
import R34.NormalizedWords
import R34.ExpandedCharge

/-! Log-concavity of the independent-set counts of caterpillar graphs. -/

noncomputable section

namespace R34

open scoped BigOperators

/-- Binomial expansion transfers positivity from every normalized word to every caterpillar. -/
theorem caterpillar_product_schurPositive_of_normalized
    (hZ : ∀ word : List ℕ, SchurPositive (Transfer.normalizedModel word))
    (n : ℕ) (m : Fin n → ℕ) :
    SchurPositive (CaterpillarCounts.independencePolynomial n m S *
      CaterpillarCounts.independencePolynomial n m T) := by
  classical
  change SchurPositive (CaterpillarCounts.independencePolynomial n m CaterpillarCounts.S *
    CaterpillarCounts.independencePolynomial n m CaterpillarCounts.T)
  rw [CaterpillarCounts.independencePolynomial_product_binomial]
  apply schurPositive_sum Finset.univ
  intro j hj
  have hc : 0 ≤ ∏ i : Fin n, (Nat.choose (m i) (j i).val : ℝ) :=
    Finset.prod_nonneg (fun i hi => Nat.cast_nonneg _)
  have hp := schurPositive_scale (∏ i : Fin n, (Nat.choose (m i) (j i).val : ℝ)) hc
    (FourStateReduction.Aword_schurPositive (ModelReduction.Gword_schur hZ)
      (fun i => (j i).val))
  simpa only [map_prod, map_natCast] using hp

/-- Every normalized transfer word is Schur-positive. -/
theorem normalizedModel_schurPositive (word : List ℕ) :
    SchurPositive (Transfer.normalizedModel word) :=
  NormalizedWords.normalized_schur_of_expanded
    ExpandedCharge.expandedWord_schurPositive word

/-- The product of the two independence polynomials is Schur-positive. -/
theorem caterpillar_product_schurPositive (n : ℕ) (m : Fin n → ℕ) :
    SchurPositive (CaterpillarCounts.independencePolynomial n m S *
      CaterpillarCounts.independencePolynomial n m T) :=
  caterpillar_product_schurPositive_of_normalized normalizedModel_schurPositive n m

/-- Independent-set counts are log-concave for every spine length and every leaf multiplicity. -/
theorem caterpillar_independentCounts_logConcave (n : ℕ) (m : Fin n → ℕ)
    (k : ℕ) (hk : 1 ≤ k) :
    CaterpillarCounts.independentCounts n m (k - 1) *
      CaterpillarCounts.independentCounts n m (k + 1) ≤
        CaterpillarCounts.independentCounts n m k ^ 2 :=
  CaterpillarCounts.actual_counts_logConcave_of_schurPositive n m
    (caterpillar_product_schurPositive n m) k hk

end R34
