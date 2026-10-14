import HardCoreActivityThreshold.ConstantActivityBlowup
import HardCoreActivityThreshold.CorrelationRowSpectrum

/-! The complete supercritical assertion of the original threshold theorem. -/
namespace HardCoreActivityThreshold
open Finset Forest
attribute [local instance] Classical.propDecidable

/-- At every constant activity at least `criticalActivity`, one finite unpinned tree simultaneously
has arbitrarily large actual influence spectral radius and arbitrarily small size-scaled heat-bath gap. -/
theorem supercritical_tree (a : ℝ) (ha : criticalActivity ≤ a) (K ε : ℝ)
    (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ A : ForestExpr,
      let μ := hardCoreLaw A.root.graph (fun _ => a) (fun _ => lt_of_lt_of_le criticalActivity_pos ha)
      A.root.graph.IsTree ∧ ENNReal.ofReal K < influenceSpectralRadius μ ∧
        (Fintype.card A.root.Vertex : ℝ) * heatBathGap μ < ε := by
  have hap : 0 < a := lt_of_lt_of_le criticalActivity_pos ha
  obtain ⟨A, hrow⟩ := supercritical_correlation_row_unbounded ha (max (K^2+1) (1/ε))
  let μ := hardCoreLaw A.root.graph (fun _ => a) (fun _ => hap)
  have hvar : ∀ v, 0 < occupationVariance μ v := fun v => hardCore_occupation_variance_pos _ _ _ v
  have hspec : ENNReal.ofReal K < influenceSpectralRadius μ :=
    influenceSpectralRadius_gt_of_row μ hvar none hK (lt_of_le_of_lt (le_max_left _ _) hrow)
  have heig : 1/ε < largestCorrelationEigenvalue μ :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hrow)
      (correlation_row_square_le_largest μ hvar none)
  have hn : 0 < (Fintype.card A.root.Vertex : ℝ) := by exact_mod_cast Fintype.card_pos
  have hl : 0 < largestCorrelationEigenvalue μ := lt_trans (by positivity) heig
  have hgap := heatBathGap_le_inverse_largestCorrelationEigenvalue μ hvar
  have hg : (Fintype.card A.root.Vertex : ℝ) * heatBathGap μ ≤ 1/largestCorrelationEigenvalue μ := by
    have hh := mul_le_mul_of_nonneg_left hgap hn.le
    convert hh using 1
    field_simp
  have hsmall : 1/largestCorrelationEigenvalue μ < ε := by
    apply (div_lt_iff₀ hl).mpr
    have he := (div_lt_iff₀ hε).mp heig
    nlinarith
  exact ⟨A, A.root_graph_isTree, hspec, lt_of_le_of_lt hg hsmall⟩

/-- Part (b) of the frozen October 12 theorem, with the original simultaneous quantifiers. -/
theorem main_b (a : ℝ) (ha : criticalActivity ≤ a) (M : ℝ) (hM : 0 < M) :
    ∃ A : ForestExpr,
      let μ := hardCoreLaw A.root.graph (fun _ => a) (fun _ => lt_of_lt_of_le criticalActivity_pos ha)
      A.root.graph.IsTree ∧ ENNReal.ofReal M ≤ influenceSpectralRadius μ ∧
        (Fintype.card A.root.Vertex : ℝ) * heatBathGap μ ≤ 1/M := by
  obtain ⟨A, htree, hspec, hgap⟩ := supercritical_tree a ha M (1/M) hM.le (by positivity)
  exact ⟨A, htree, hspec.le, hgap.le⟩

end HardCoreActivityThreshold
