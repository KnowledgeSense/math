import HardCoreActivityThreshold.ForestMarginalBounds
import HardCoreActivityThreshold.CorrelationQuadratic

/-! The actual correlation matrix admits the parent-innovation factorization. -/
namespace HardCoreActivityThreshold
open Finset Forest Matrix
attribute [local instance] Classical.propDecidable

noncomputable def forestHC (A : ForestExpr) (activity : A.Vertex → ℝ) (ha : ∀ v, 0 < activity v) :
    FiniteLaw (Finset A.Vertex) := hardCoreLaw A.graph activity ha

noncomputable def parentCorrelationMatrix (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) : Matrix A.Vertex A.Vertex ℝ := Matrix.of (fun u v =>
  if forestParent A u = some v then
    -vertexMessage A activity u * Real.sqrt (occupationVariance (forestHC A activity ha) v) /
      Real.sqrt (occupationVariance (forestHC A activity ha) u) else 0)

noncomputable def normalizedInnovation (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) (s : Finset A.Vertex) : ℝ :=
  innovation A activity false v (configurationEquiv s) /
    Real.sqrt (occupationVariance (forestHC A activity ha) v)

noncomputable def innovationDiagonal (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) : ℝ :=
  (forestLaw A activity ha false).expectation (fun x => (innovation A activity false v x)^2) /
    occupationVariance (forestHC A activity ha) v

theorem innovation_centered_identity (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) (s : Finset A.Vertex) :
    innovation A activity false v (configurationEquiv s) =
      (occupation v s - marginal (forestHC A activity ha) v) + vertexMessage A activity v *
        (forestParent A v).elim 0 (fun w => occupation w s - marginal (forestHC A activity ha) w) := by
  rw [innovation_identity, boolOccupation_configurationEquiv]
  have hm := forest_parent_marginal A activity ha v
  simp only [forestMarginal_free_actual] at hm
  unfold parentOccupation
  cases hp : forestParent A v
  · simp only [Option.elim_none, boolValue, Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero] at *
    rw [hp] at hm
    simp only [Option.elim_none, sub_zero, mul_one] at hm
    exact congrArg (fun z => occupation v s-z) hm.symm
  · rw [hp] at hm
    simp only [Option.elim_some, boolOccupation_configurationEquiv] at *
    change marginal (forestHC A activity ha) v = vertexMessage A activity v *
      (1-marginal (forestHC A activity ha) _) at hm
    rw [hm]
    ring

theorem normalizedInnovation_linear (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (u : A.Vertex) (s : Finset A.Vertex) :
    normalizedInnovation A activity ha u s = normalizedOccupation (forestHC A activity ha) u s -
      ∑ v, parentCorrelationMatrix A activity ha u v * normalizedOccupation (forestHC A activity ha) v s := by
  have hvar (v : A.Vertex) : 0 < occupationVariance (forestHC A activity ha) v := hardCore_occupation_variance_pos _ _ ha v
  unfold normalizedInnovation
  rw [innovation_centered_identity A activity ha]
  unfold parentCorrelationMatrix
  simp only [Matrix.of_apply]
  cases hp : forestParent A u with
  | none => simp [normalizedOccupation]
  | some v =>
    simp only [Option.some.injEq, ite_mul, zero_mul, sum_ite_eq, mem_univ,
      ↓reduceIte, Option.elim_some, normalizedOccupation]
    have hu : Real.sqrt (occupationVariance (forestHC A activity ha) u) ≠ 0 :=
      (Real.sqrt_pos.mpr (hvar u)).ne'
    have hv : Real.sqrt (occupationVariance (forestHC A activity ha) v) ≠ 0 :=
      (Real.sqrt_pos.mpr (hvar v)).ne'
    field_simp
    ring

theorem normalizedInnovation_matrix (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (u : A.Vertex) (s : Finset A.Vertex) :
    normalizedInnovation A activity ha u s =
      ∑ v, (1-parentCorrelationMatrix A activity ha) u v * normalizedOccupation (forestHC A activity ha) v s := by
  rw [normalizedInnovation_linear]
  simp only [Matrix.sub_apply, sub_mul, sum_sub_distrib, Matrix.one_apply, ite_mul,
    one_mul, zero_mul, sum_ite_eq, mem_univ, ↓reduceIte]

section GeneralGram
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem correlation_congruence_gram (μ : FiniteLaw (Finset V)) (C : Matrix V V ℝ) (u v : V) :
    μ.expectation (fun s => (∑ i, C u i * normalizedOccupation μ i s) *
      (∑ j, C v j * normalizedOccupation μ j s)) = (C * correlationMatrix μ * C.transpose) u v := by
  simp_rw [sum_mul_sum]
  rw [FiniteLaw.expectation_sum]
  simp_rw [FiniteLaw.expectation_sum]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  have he : (fun s => (C u j * normalizedOccupation μ j s) * (C v i * normalizedOccupation μ i s)) =
      (fun s => (C u j * C v i) * (normalizedOccupation μ j s * normalizedOccupation μ i s)) := by funext s; ring
  rw [he, FiniteLaw.expectation_smul, normalizedOccupation_product]
  ring

end GeneralGram

theorem normalizedInnovation_product (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (u v : A.Vertex) :
    (forestHC A activity ha).expectation (fun s => normalizedInnovation A activity ha u s *
      normalizedInnovation A activity ha v s) = if u = v then innovationDiagonal A activity ha u else 0 := by
  have hvar (v : A.Vertex) : 0 < occupationVariance (forestHC A activity ha) v := hardCore_occupation_variance_pos _ _ ha v
  have he (s : Finset A.Vertex) : normalizedInnovation A activity ha u s * normalizedInnovation A activity ha v s =
      (Real.sqrt (occupationVariance (forestHC A activity ha) u) *
        Real.sqrt (occupationVariance (forestHC A activity ha) v))⁻¹ *
      (innovation A activity false u (configurationEquiv s) * innovation A activity false v (configurationEquiv s)) := by
    unfold normalizedInnovation
    ring
  simp_rw [he]
  rw [FiniteLaw.expectation_smul]
  unfold forestHC
  dsimp only [forestHC] at hvar
  rw [← forest_free_expectation_actual A activity ha
    (fun x => innovation A activity false u x * innovation A activity false v x)]
  by_cases huv : u = v
  · subst v
    simp only [↓reduceIte, ← sq, Real.sq_sqrt (hvar u).le]
    unfold innovationDiagonal forestHC
    ring
  · rw [innovation_orthogonal A activity ha false u v huv]
    simp [huv]

theorem innovationDiagonal_nonneg (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) : 0 ≤ innovationDiagonal A activity ha v := by
  apply div_nonneg
  · exact FiniteLaw.expectation_nonneg _ (fun _ => sq_nonneg _)
  · exact (hardCore_occupation_variance_pos _ _ ha v).le

theorem innovationDiagonal_bound (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) {Λ : ℝ} (hΛ : 0 < Λ) (hcap : ∀ v, activity v ≤ Λ) (v : A.Vertex) :
    innovationDiagonal A activity ha v ≤ (1+Λ)^2 := by
  unfold innovationDiagonal
  apply (div_le_iff₀ (hardCore_occupation_variance_pos _ _ ha v)).mpr
  have he := innovation_second_moment_le A activity ha false v
  have hs := (div_le_iff₀ (by positivity : 0 < (1+Λ)^2)).mp
    (forest_variance_message_lower A activity ha hΛ hcap v)
  unfold occupationVariance at hs
  nlinarith

/-- Full covariance factorization for the actual finite hard-core measure. -/
theorem forest_correlation_factorization (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) :
    (1-parentCorrelationMatrix A activity ha) * correlationMatrix (forestHC A activity ha) *
      (1-parentCorrelationMatrix A activity ha).transpose = diagonal (innovationDiagonal A activity ha) := by
  ext u v
  rw [← correlation_congruence_gram]
  simp_rw [← normalizedInnovation_matrix]
  rw [normalizedInnovation_product]
  rfl

end HardCoreActivityThreshold
