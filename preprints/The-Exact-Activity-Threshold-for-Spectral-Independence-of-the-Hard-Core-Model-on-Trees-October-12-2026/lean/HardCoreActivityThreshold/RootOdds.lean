import HardCoreActivityThreshold.Pinning
import HardCoreActivityThreshold.Forest.GraphPolynomial

/-! Actual root odds of recursively constructed finite trees. -/
namespace HardCoreActivityThreshold
open Finset Polynomial Forest
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem partitionFunction_constant_polynomial (G : SimpleGraph V) (a : ℝ) :
    partitionFunction G (fun _ => a) =
      (Forest.independencePolynomial G univ).eval₂ (Nat.castRingHom ℝ) a := by
  unfold partitionFunction configurationWeight Forest.independencePolynomial
  simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_X_pow, prod_const]
  have he : Forest.independentSetsWithin G univ = univ.filter (Independent G) := by
    ext s
    simp only [Forest.mem_independentSetsWithin, subset_univ, true_and, mem_filter, mem_univ]
    rfl
  rw [he, sum_filter]

theorem hardCore_absence_polynomial (G : SimpleGraph V) (a : ℝ) (ha : 0 < a) (v : V) :
    (hardCoreLaw G (fun _ => a) (fun _ => ha)).eventMass (fun s => v ∉ s) =
      (Forest.independencePolynomial G (univ.erase v)).eval₂ (Nat.castRingHom ℝ) a /
        partitionFunction G (fun _ => a) := by
  unfold FiniteLaw.eventMass
  have he : Forest.independentSetsWithin G (univ.erase v) =
      univ.filter (fun s => Independent G s ∧ v ∉ s) := by
    ext s
    simp only [Forest.mem_independentSetsWithin, mem_filter, mem_univ, true_and]
    have hsub : s ⊆ univ.erase v ↔ v ∉ s := by simp [subset_erase]
    rw [hsub]
    change (v ∉ s ∧ Independent G s) ↔ (Independent G s ∧ v ∉ s)
    tauto
  unfold Forest.independencePolynomial
  simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_X_pow]
  rw [he, sum_filter, sum_div]
  apply sum_congr rfl
  intro s _
  by_cases hi : Independent G s <;> by_cases hv : v ∈ s <;>
    simp [hardCoreLaw_mass, configurationWeight, hi, hv]

noncomputable def forestTotal (A : ForestExpr) (a : ℝ) : ℝ :=
  A.polynomials.1.eval₂ (Nat.castRingHom ℝ) a

noncomputable def forestAvoid (A : ForestExpr) (a : ℝ) : ℝ :=
  A.polynomials.2.eval₂ (Nat.castRingHom ℝ) a

theorem forest_evaluations_pos (A : ForestExpr) {a : ℝ} (ha : 0 < a) :
    0 < forestTotal A a ∧ 0 < forestAvoid A a := by
  induction A with
  | empty => norm_num [forestTotal, forestAvoid, ForestExpr.polynomials]
  | union A B hA hB =>
    simpa only [forestTotal, forestAvoid, ForestExpr.polynomials, Polynomial.eval₂_mul]
      using And.intro (mul_pos hA.1 hB.1) (mul_pos hA.2 hB.2)
  | root A hA =>
    simpa only [forestTotal, forestAvoid, ForestExpr.polynomials, Polynomial.eval₂_add,
      Polynomial.eval₂_mul, Polynomial.eval₂_X] using
      And.intro (add_pos hA.1 (mul_pos ha hA.2)) hA.1

/-- Occupation odds at the root of the actual tree obtained by adjoining a root to `A`. -/
noncomputable def rootOdds (A : ForestExpr) (a : ℝ) : ℝ := a * forestAvoid A a / forestTotal A a

theorem rootOdds_pos (A : ForestExpr) {a : ℝ} (ha : 0 < a) : 0 < rootOdds A a :=
  div_pos (mul_pos ha (forest_evaluations_pos A ha).2) (forest_evaluations_pos A ha).1

theorem forestAvoid_le_total (A : ForestExpr) {a : ℝ} (ha : 0 < a) :
    forestAvoid A a ≤ forestTotal A a := by
  induction A with
  | empty => rfl
  | union A B hA hB =>
    simpa only [forestAvoid, forestTotal, ForestExpr.polynomials, Polynomial.eval₂_mul] using
      mul_le_mul hA hB (forest_evaluations_pos B ha).2.le (forest_evaluations_pos A ha).1.le
  | root A hA =>
    simp only [forestAvoid, forestTotal, ForestExpr.polynomials, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X]
    change forestTotal A a ≤ forestTotal A a + a * forestAvoid A a
    exact le_add_of_nonneg_right (mul_pos ha (forest_evaluations_pos A ha).2).le

theorem rootOdds_le_activity (A : ForestExpr) {a : ℝ} (ha : 0 < a) : rootOdds A a ≤ a := by
  unfold rootOdds
  apply (div_le_iff₀ (forest_evaluations_pos A ha).1).mpr
  exact mul_le_mul_of_nonneg_left (forestAvoid_le_total A ha) ha.le

theorem root_unoccupied_probability (A : ForestExpr) {a : ℝ} (ha : 0 < a) :
    1 - marginal (hardCoreLaw (ForestExpr.root A).graph (fun _ => a) (fun _ => ha)) none =
      1 / (1 + rootOdds A a) := by
  rw [← absent_eventMass, hardCore_absence_polynomial,
    partitionFunction_constant_polynomial, ForestExpr.graph_polynomial, A.root_deleted_polynomial]
  simp only [ForestExpr.polynomials, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X]
  change forestTotal A a / (forestTotal A a + a * forestAvoid A a) = _
  unfold rootOdds
  have hz := (forest_evaluations_pos A ha).1.ne'
  field_simp

/-- The recursively evaluated odds coincide with the odds of the actual finite-graph law. -/
theorem rootOdds_actual (A : ForestExpr) {a : ℝ} (ha : 0 < a) :
    let μ := hardCoreLaw (ForestExpr.root A).graph (fun _ => a) (fun _ => ha)
    marginal μ none / (1 - marginal μ none) = rootOdds A a := by
  dsimp only
  have h := root_unoccupied_probability A ha
  have ho := rootOdds_pos A ha
  have hm := hardCore_marginal_lt_one (ForestExpr.root A).graph (fun _ => a) (fun _ => ha) none
  have hden : 1 + rootOdds A a ≠ 0 := by positivity
  have hmden : 1 - marginal (hardCoreLaw (ForestExpr.root A).graph (fun _ => a) (fun _ => ha)) none ≠ 0 := by linarith
  apply (div_eq_iff hmden).mpr
  field_simp at h
  nlinarith

theorem root_marginal_from_odds (A : ForestExpr) {a : ℝ} (ha : 0 < a) :
    marginal (hardCoreLaw (ForestExpr.root A).graph (fun _ => a) (fun _ => ha)) none =
      rootOdds A a / (1 + rootOdds A a) := by
  have h := root_unoccupied_probability A ha
  have ho := rootOdds_pos A ha
  have hden : 1 + rootOdds A a ≠ 0 := by positivity
  field_simp at h ⊢
  nlinarith

end HardCoreActivityThreshold
