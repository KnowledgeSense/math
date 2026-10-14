import EdgeColoringMixing.ConditionalInjections
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

namespace EdgeColoringMixing
open Finset

/-- The sum of absolute coordinate differences on a finite index set. -/
noncomputable def coordinateDistance {ι : Type*} [Fintype ι] (p p' : ι → ℝ) : ℝ :=
  ∑ x, |p x - p' x|

namespace coordinateDistance
variable {ι β : Type*} [Fintype ι] [Fintype β]

theorem nonneg (p p' : ι → ℝ) : 0 ≤ coordinateDistance p p' :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem symm (p p' : ι → ℝ) : coordinateDistance p p' = coordinateDistance p' p := by
  unfold coordinateDistance
  simp_rw [abs_sub_comm]

theorem triangle (p p' p'' : ι → ℝ) :
    coordinateDistance p p'' ≤ coordinateDistance p p' + coordinateDistance p' p'' := by
  unfold coordinateDistance
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun x _ => abs_sub_le (p x) (p' x) (p'' x))

theorem probabilities_le_two (p p' : ι → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hp' : ∀ x, 0 ≤ p' x)
    (hs : ∑ x, p x = 1) (hs' : ∑ x, p' x = 1) :
    coordinateDistance p p' ≤ 2 := by
  calc
    _ ≤ ∑ x, (p x + p' x) := Finset.sum_le_sum (fun x _ =>
      abs_le.mpr ⟨by linarith [hp x], by linarith [hp' x]⟩)
    _ = 2 := by rw [Finset.sum_add_distrib, hs, hs']; norm_num

/-- Convex mixtures do not increase the average coordinate distance. -/
theorem mixture_right (p : ι → ℝ) (Q : β → ι → ℝ) (w : β → ℝ)
    (hw : ∀ b, 0 ≤ w b) (hs : ∑ b, w b = 1) :
    coordinateDistance p (fun x => ∑ b, w b * Q b x) ≤
      ∑ b, w b * coordinateDistance p (Q b) := by
  have hp (x : ι) : p x - ∑ b, w b * Q b x =
      ∑ b, w b * (p x - Q b x) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul]
  unfold coordinateDistance
  simp_rw [hp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  calc
    _ ≤ ∑ b, |w b * (p x - Q b x)| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp_rw [abs_mul, abs_of_nonneg (hw _)]

/-- A decomposition with a common part gives a bound only in terms of the remaining part. -/
theorem common_part (p p' : ι → ℝ) (Q : β → ι → ℝ) (w : β → ℝ)
    (hw : ∀ b, 0 ≤ w b)
    (heq : ∀ x, p x = (1 - ∑ b, w b) * p' x + ∑ b, w b * Q b x) :
    coordinateDistance p p' ≤ ∑ b, w b * coordinateDistance (Q b) p' := by
  have hp (x : ι) : p x - p' x = ∑ b, w b * (Q b x - p' x) := by
    rw [heq]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  unfold coordinateDistance
  simp_rw [hp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  calc
    _ ≤ ∑ b, |w b * (Q b x - p' x)| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp_rw [abs_mul, abs_of_nonneg (hw _)]

end coordinateDistance

namespace WeightedInjection
variable {d q : ℕ}

/-- The normalized conditional moment identity also holds when the conditioning cell is null. -/
theorem mean_mul_conditionalMean (μ : FiniteLaw (Injection d q))
    (x y : Fin d × Fin q) :
    mean μ x.1 x.2 * conditionalMean μ x y =
      mean μ x.1 x.2 * mean μ y.1 y.2 + covariance μ y x := by
  by_cases hx : mean μ x.1 x.2 = 0
  · simp [hx, covariance_eq_zero_of_mean_zero μ y x hx]
  · unfold conditionalMean
    field_simp

/-- Decompose a cell marginal by the color in any specified row. -/
theorem mean_row_mixture (μ : FiniteLaw (Injection d q)) (i : Fin d) (y : Fin d × Fin q) :
    mean μ y.1 y.2 = ∑ c, mean μ i c * conditionalMean μ (i,c) y := by
  simp_rw [mean_mul_conditionalMean μ (i,_) y]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, mean_row_sum, covariance_row_sum]
  ring

theorem conditionalMean_row_sum (μ : FiniteLaw (Injection d q))
    (x : Fin d × Fin q) (hx : 0 < mean μ x.1 x.2) (i : Fin d) :
    ∑ c, conditionalMean μ x (i,c) = 1 := by
  simp_rw [conditionalMean_eq_mixed_div μ x _ hx]
  rw [← Finset.sum_div, ← FiniteLaw.expectation_sum]
  have hsum (σ : Injection d q) :
      (∑ c, cell x.1 x.2 σ * cell i c σ) = cell x.1 x.2 σ := by
    rw [← Finset.mul_sum, row_sum, mul_one]
  simp_rw [hsum]
  exact div_self hx.ne'

/-- Forbidding a color is exactly restriction to its unused event, before normalization. -/
theorem numerator_withoutColor (W : Fin d → Fin q → ℝ) (c : Fin q)
    (f : Injection d q → ℝ) :
    numerator (withoutColor W c) f =
      numerator W (fun σ => (if c ∉ Set.range σ then 1 else 0) * f σ) := by
  classical
  unfold numerator
  apply Finset.sum_congr rfl
  intro σ _
  rw [weight_withoutColor]
  by_cases hc : c ∈ Set.range σ <;> simp [hc]

/-- Decompose every actual marginal into the unused-color event and the possible occupied rows. -/
theorem mean_color_mixture (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (hs : 1 < s) (c : Fin q) (y : Fin d × Fin q) :
    let μ := law W hW.nonneg (partition_pos W hW)
    let hWc := hW.forbid W hs c
    let μc := law (withoutColor W c) hWc.nonneg (partition_pos _ hWc)
    mean μ y.1 y.2 = (1 - colorMean μ c) * mean μc y.1 y.2 +
      ∑ i, mean μ i c * conditionalMean μ (i,c) y := by
  classical
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  let hWc := hW.forbid W hs c
  let μc := law (withoutColor W c) hWc.nonneg (partition_pos _ hWc)
  have hZ := partition_pos W hW
  have hZc := partition_pos _ hWc
  have hunused : (1 - colorMean μ c) * mean μc y.1 y.2 =
      μ.expectation (fun σ => (if c ∉ Set.range σ then 1 else 0) * cell y.1 y.2 σ) := by
    rw [← color_unused_probability W hW.nonneg (partition_pos W hW) c]
    change (partition (withoutColor W c) / partition W) *
      μc.expectation (cell y.1 y.2) = _
    rw [← weightedExpectation_eq, ← weightedExpectation_eq]
    unfold weightedExpectation
    rw [numerator_withoutColor]
    field_simp
  have hused (i : Fin d) : mean μ i c * conditionalMean μ (i,c) y =
      μ.expectation (fun σ => cell i c σ * cell y.1 y.2 σ) := by
    rw [mean_mul_conditionalMean μ (i,c) y, covariance, FiniteLaw.covariance_eq_mixed_moment]
    change mean μ i c * mean μ y.1 y.2 +
      (μ.expectation (fun σ => cell y.1 y.2 σ * cell i c σ) -
        mean μ y.1 y.2 * mean μ i c) = _
    simp_rw [mul_comm (cell y.1 y.2 _)]
    ring
  change mean μ y.1 y.2 = (1 - colorMean μ c) * mean μc y.1 y.2 +
    ∑ i, mean μ i c * conditionalMean μ (i,c) y
  rw [hunused]
  simp_rw [hused]
  rw [← FiniteLaw.expectation_sum, ← FiniteLaw.expectation_add]
  unfold mean
  congr 1
  ext σ
  rw [← Finset.sum_mul, sum_cells_eq_used]
  by_cases hc : c ∈ Set.range σ <;> simp [hc]

end WeightedInjection
end EdgeColoringMixing
