import MeanMaximumForests.IndependentSetLaw
import MeanMaximumForests.FiniteLawImage
import MeanMaximumForests.IndependenceCoefficients

namespace MeanMaximumForests
open Finset HardCoreActivityThreshold
variable {V : Type*} [Fintype V]

/-- Cardinality of a vertex subset, as an element of its finite natural range. -/
def boundedCardinality (s : Finset V) : Fin (Fintype.card V + 1) :=
  ⟨s.card, Nat.lt_succ_of_le (card_le_univ s)⟩

/-- The actual independent-set size distribution, with no analytic assumptions. -/
noncomputable def independentSizeLaw (G : SimpleGraph V) : FiniteLaw (Fin (Fintype.card V + 1)) :=
  finiteLawImage (uniformIndependentSetLaw G) boundedCardinality

theorem independentSizeLaw_mass (G : SimpleGraph V) (k : Fin (Fintype.card V + 1)) :
    (independentSizeLaw G).mass k =
      (independentSetCoefficient G univ k.val : ℝ) / independentSetCount G univ := by
  classical
  rw [independentSizeLaw, finiteLawImage_mass, uniformIndependentSetLaw_expectation]
  congr 1
  have he (s : Finset V) : boundedCardinality s = k ↔ s.card = k.val := Fin.ext_iff
  simp only [he, independentSetCoefficient]
  simp

theorem independentSizeLaw_mean (G : SimpleGraph V) :
    (independentSizeLaw G).expectation (fun k => (k.val : ℝ)) = graphMean G := by
  rw [independentSizeLaw, finiteLawImage_expectation]
  exact uniformIndependentSetLaw_mean G

theorem independentSizeLaw_variance (G : SimpleGraph V) :
    (independentSizeLaw G).variance (fun k => (k.val : ℝ)) = graphVariance G := by
  rw [independentSizeLaw, finiteLawImage_variance]
  exact uniformIndependentSetLaw_variance G

theorem independentSizeLaw_mode (G : SimpleGraph V) (k : Fin (Fintype.card V + 1))
    (hk : ∀ j, independentSetCoefficient G univ j ≤ independentSetCoefficient G univ k.val) :
    ∀ j, (independentSizeLaw G).mass j ≤ (independentSizeLaw G).mass k := by
  intro j
  rw [independentSizeLaw_mass, independentSizeLaw_mass]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast hk j.val

end MeanMaximumForests
