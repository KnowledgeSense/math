import HardCoreActivityThreshold.ParentColumnBounds
import HardCoreActivityThreshold.PotentialEnvelope
import HardCoreActivityThreshold.TriangularFactorization
import HardCoreActivityThreshold.CovarianceResponse

/-! Uniform correlation bounds for actual heterogeneous hard-core laws on finite rooted forests. -/
namespace HardCoreActivityThreshold
open Finset Forest Matrix
attribute [local instance] Classical.propDecidable

theorem childSum_subtype (A : ForestExpr) (f : A.Vertex → ℝ) (v : A.Vertex) :
    childSum A f v = ∑ u : {u : A.Vertex // forestParent A u = some v}, f u.val := by
  unfold childSum
  rw [← sum_filter, Finset.sum_subtype (p := fun u => forestParent A u = some v) _ (fun _ => by simp) f]

theorem local_potential_contraction (Λ : ℝ) (hΛ : 0 < Λ) (hL : Λ < criticalActivity) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ ∀ (A : ForestExpr) (activity : A.Vertex → ℝ)
      (_ha : ∀ v, 0 < activity v), (∀ v, activity v ≤ Λ) → ∀ v,
      childSum A (fun u => (vertexMessage A activity u)^2 * potential (vertexLogPotential A activity u)) v ≤
        γ * potential (vertexLogPotential A activity v) := by
  obtain ⟨γ, hγ, hγ1, hc⟩ := activity_contraction Λ hΛ hL
  refine ⟨γ, hγ, hγ1, ?_⟩
  intro A activity ha hcap v
  let W := {u : A.Vertex // forestParent A u = some v}
  let e : Fin (Fintype.card W) ≃ W := Fintype.equivOfCardEq (Fintype.card_fin _)
  have he := hc (Fintype.card W) (fun i => vertexOdds A activity (e i).val)
    (fun i => vertexLogPotential A activity (e i).val)
    (fun i => ⟨vertexOdds_pos A activity ha _, (vertexOdds_le_activity A activity ha _).trans (hcap _)⟩)
    (fun i => ⟨vertexLogPotential_nonneg A activity ha _, vertexLogPotential_cap A activity ha hΛ hcap _⟩)
  have hs (f : A.Vertex → ℝ) : (∑ i : Fin (Fintype.card W), f (e i).val) = childSum A f v := by
    rw [childSum_subtype]
    exact e.sum_comp (fun u : W => f u.val)
  simp_rw [← vertexMessage_eq_odds A activity ha] at he
  rw [hs (fun u => (vertexMessage A activity u)^2 * potential (vertexLogPotential A activity u)),
    hs (fun u => Real.log (1+vertexOdds A activity u)), ← vertexLogPotential_children] at he
  exact he

theorem forestPotentialWeight_bound (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) {Λ : ℝ} (hΛ : 0 < Λ) (hcap : ∀ v, activity v ≤ Λ) (v : A.Vertex) :
    forestPotentialWeight A activity ha v ≤ 2*Λ := by
  have hm := (forest_marginal_message_bounds A activity ha hΛ hcap v).2
  have ho := vertexOdds_pos A activity ha v
  have hqr : vertexMessage A activity v ≤ vertexOdds A activity v := by
    rw [vertexMessage_eq_odds A activity ha v]
    apply div_le_self ho.le
    linarith
  have hs : occupationVariance (forestHC A activity ha) v ≤ marginal (forestHC A activity ha) v := by
    unfold occupationVariance
    rw [occupation_variance]
    nlinarith [sq_nonneg (marginal (forestHC A activity ha) v)]
  have hr : vertexOdds A activity v ≤ Λ*Real.exp (-vertexLogPotential A activity v) := by
    rw [vertexOdds_exp A activity ha v]
    exact mul_le_mul_of_nonneg_right (hcap v) (Real.exp_pos _).le
  have hs' := hs.trans (hm.trans (hqr.trans hr))
  have hy := vertexLogPotential_nonneg A activity ha v
  have hphi : 0 ≤ potential (vertexLogPotential A activity v) := cubicPotential_nonneg _ _ hy
  have he := mul_le_mul_of_nonneg_right hs' hphi
  have hb := mul_le_mul_of_nonneg_left (potential_exponential_envelope _ hy) hΛ.le
  unfold forestPotentialWeight
  nlinarith

noncomputable def forestCorrelationConstant (Λ γ : ℝ) : ℝ :=
  (1+Λ)^2 * (1 + Real.sqrt ((1+Λ)^2*(2*Λ))/(1-Real.sqrt γ))^2

/-- Uniform quadratic correlation bound, independent of size and degree, for actual forest laws. -/
theorem subcritical_forest_correlation (Λ : ℝ) (hΛ : 0 < Λ) (hL : Λ < criticalActivity) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : ForestExpr) (activity : A.Vertex → ℝ)
      (ha : ∀ v, 0 < activity v), (∀ v, activity v ≤ Λ) →
      CorrelationBound (forestHC A activity ha) C := by
  obtain ⟨γ, hγ, hγ1, hc⟩ := local_potential_contraction Λ hΛ hL
  refine ⟨forestCorrelationConstant Λ γ, ?_, ?_⟩
  · have hg : 0 < 1-Real.sqrt γ := by
      have hs := Real.sqrt_lt_sqrt hγ.le hγ1
      simpa using sub_pos.mpr hs
    unfold forestCorrelationConstant
    positivity
  · intro A activity ha hcap x
    let B := parentCorrelationMatrix A activity ha
    let w := forestPotentialWeight A activity ha
    have hcol := weighted_column_uniform B w ((1+Λ)^2) (2*Λ) γ (sq_nonneg _) hγ.le
      (forestPotentialWeight_bound A activity ha hΛ hcap)
      (parentCorrelationMatrix_unique A activity ha)
      (parentColumn_first_bound A activity ha hΛ hcap)
      (fun v => ?_)
    · have hfac := nilpotent_triangular_factorization (correlationMatrix (forestHC A activity ha)) B
        (innovationDiagonal A activity ha) (univ.sup A.depth)
        (parentCorrelationMatrix_nilpotent A activity ha) (forest_correlation_factorization A activity ha)
      have hb := bounded_triangular_correlation_quadratic_bound
        (correlationMatrix (forestHC A activity ha)) B (innovationDiagonal A activity ha)
        ((1+Λ)^2) ((1+Λ)^2*(2*Λ)) γ (sq_nonneg _) (by positivity) hγ.le hγ1
        (fun h _ => parent_power_sparse B (parentCorrelationMatrix_unique A activity ha) h)
        hcol (univ.sup A.depth) (innovationDiagonal_bound A activity ha hΛ hcap) hfac x
      simpa only [dotProduct, mulVec, mul_sum, mul_assoc, forestCorrelationConstant] using hb
    · dsimp [B, w]
      rw [parentColumn_weighted_sum]
      have hv : 0 ≤ occupationVariance (forestHC A activity ha) v := (hardCore_occupation_variance_pos _ _ ha v).le
      have hm := mul_le_mul_of_nonneg_left (hc A activity ha hcap v) hv
      unfold forestPotentialWeight
      nlinarith

end HardCoreActivityThreshold
