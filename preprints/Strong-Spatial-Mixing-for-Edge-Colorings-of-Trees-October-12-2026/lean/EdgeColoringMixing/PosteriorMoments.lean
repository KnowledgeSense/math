import EdgeColoringMixing.WeightedInjections

set_option autoImplicit false

namespace EdgeColoringMixing.WeightedInjection
open Finset

variable {d q : ℕ}

/-- The active cells are exactly those with positive marginal mass. -/
noncomputable def active (μ : FiniteLaw (Injection d q)) : Finset (Fin d × Fin q) := by
  classical
  exact univ.filter (fun x => 0 < mean μ x.1 x.2)

@[simp] theorem mem_active (μ : FiniteLaw (Injection d q)) (x : Fin d × Fin q) :
    x ∈ active μ ↔ 0 < mean μ x.1 x.2 := by simp [active]

theorem mean_eq_zero_of_not_active (μ : FiniteLaw (Injection d q))
    {x : Fin d × Fin q} (hx : x ∉ active μ) : mean μ x.1 x.2 = 0 := by
  exact le_antisymm (le_of_not_gt (by simpa using hx)) (mean_nonneg μ x.1 x.2)

theorem covariance_eq_zero_of_mean_zero (μ : FiniteLaw (Injection d q))
    (x y : Fin d × Fin q) (hy : mean μ y.1 y.2 = 0) : covariance μ x y = 0 := by
  have hzero (σ : Injection d q) : μ.mass σ * cell y.1 y.2 σ = 0 := by
    have h : ∑ σ, μ.mass σ * cell y.1 y.2 σ = 0 := hy
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun τ _ => mul_nonneg (μ.nonneg τ) (cell_nonneg y.1 y.2 τ))).mp h σ (mem_univ σ)
  rw [covariance, FiniteLaw.covariance_eq_mixed_moment]
  change μ.expectation (fun σ => cell x.1 x.2 σ * cell y.1 y.2 σ) -
    mean μ x.1 x.2 * mean μ y.1 y.2 = 0
  rw [hy, mul_zero, sub_zero]
  unfold FiniteLaw.expectation
  apply Finset.sum_eq_zero
  intro σ _
  calc
    μ.mass σ * (cell x.1 x.2 σ * cell y.1 y.2 σ) =
      cell x.1 x.2 σ * (μ.mass σ * cell y.1 y.2 σ) := by ring
    _ = 0 := by rw [hzero, mul_zero]

theorem active_mean_total (μ : FiniteLaw (Injection d q)) :
    ∑ x ∈ active μ, mean μ x.1 x.2 = d := by
  rw [← mean_total μ]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro x _ hx
  exact mean_eq_zero_of_not_active μ hx

theorem active_covariance_total (μ : FiniteLaw (Injection d q)) (y : Fin d × Fin q) :
    ∑ x ∈ active μ, covariance μ y x = 0 := by
  rw [← covariance_total μ y]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro x _ hx
  exact covariance_eq_zero_of_mean_zero μ y x (mean_eq_zero_of_not_active μ hx)

/-- The occupancy of a remaining cell after conditioning on x and deleting x.
It is expressed using the actual original finite probability law. -/
noncomputable def posteriorMean (μ : FiniteLaw (Injection d q))
    (x y : Fin d × Fin q) : ℝ :=
  μ.expectation (fun σ => cell x.1 x.2 σ *
    (cell y.1 y.2 σ - if x = y then 1 else 0)) / mean μ x.1 x.2

theorem mean_eq_eventMass (μ : FiniteLaw (Injection d q)) (x : Fin d × Fin q) :
    mean μ x.1 x.2 = μ.eventMass (fun σ => σ x.1 = x.2) := by
  unfold mean FiniteLaw.expectation FiniteLaw.eventMass cell
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

/-- The posterior definition is exactly conditional expectation in the normalized finite law. -/
theorem posteriorMean_eq_condition (μ : FiniteLaw (Injection d q))
    (x y : Fin d × Fin q) (hE : 0 < μ.eventMass (fun σ => σ x.1 = x.2)) :
    posteriorMean μ x y =
      (μ.condition (fun σ => σ x.1 = x.2) hE).expectation
        (fun σ => cell y.1 y.2 σ - if x = y then 1 else 0) := by
  unfold posteriorMean FiniteLaw.expectation
  simp only [FiniteLaw.condition_mass, div_mul_eq_mul_div]
  rw [← Finset.sum_div, mean_eq_eventMass]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  unfold cell
  split_ifs <;> ring

/-- The exact posterior first-moment formula, including the deleted occupied cell. -/
theorem posteriorMean_eq (μ : FiniteLaw (Injection d q))
    (x y : Fin d × Fin q) (hx : x ∈ active μ) :
    posteriorMean μ x y = mean μ y.1 y.2 + covariance μ y x / mean μ x.1 x.2 -
      if x = y then 1 else 0 := by
  have hp : mean μ x.1 x.2 ≠ 0 := (mem_active μ x |>.mp hx).ne'
  have hsplit (σ : Injection d q) :
      cell x.1 x.2 σ * (cell y.1 y.2 σ - if x = y then 1 else 0) =
      cell y.1 y.2 σ * cell x.1 x.2 σ -
        (if x = y then 1 else 0) * cell x.1 x.2 σ := by ring
  simp only [posteriorMean, hsplit, FiniteLaw.expectation_sub, FiniteLaw.expectation_smul,
    covariance, FiniteLaw.covariance_eq_mixed_moment, mean]
  change μ.expectation (cell x.1 x.2) ≠ 0 at hp
  field_simp [hp]
  ring

/-- The undeleted posterior occupancy. -/
noncomputable def conditionalMean (μ : FiniteLaw (Injection d q))
    (x y : Fin d × Fin q) : ℝ :=
  mean μ y.1 y.2 + covariance μ y x / mean μ x.1 x.2

/-- A color cannot be occupied twice, even after conditioning. -/
theorem conditionalMean_same_color (μ : FiniteLaw (Injection d q))
    (x y : Fin d × Fin q) (hx : x ∈ active μ) (hcolor : x.2 = y.2) :
    conditionalMean μ x y = if x = y then 1 else 0 := by
  obtain ⟨i, c⟩ := x
  obtain ⟨j, b⟩ := y
  simp only at hcolor
  subst b
  have hp : mean μ i c ≠ 0 := (mem_active μ (i,c) |>.mp hx).ne'
  by_cases hij : i = j
  · subst j
    simp only [conditionalMean, covariance_diagonal, ite_true]
    field_simp
    ring
  · have hji : j ≠ i := Ne.symm hij
    simp only [conditionalMean, covariance_same_color μ hji, Prod.mk.injEq,
      and_true, hij, ite_false]
    field_simp
    ring

private theorem conditional_product_expand (μ : FiniteLaw (Injection d q))
    (x y z : Fin d × Fin q) (hx : x ∈ active μ) :
    mean μ x.1 x.2 * conditionalMean μ x y * conditionalMean μ x z =
      mean μ x.1 x.2 * mean μ y.1 y.2 * mean μ z.1 z.2 +
        mean μ y.1 y.2 * covariance μ z x +
        mean μ z.1 z.2 * covariance μ y x +
        covariance μ y x * covariance μ z x / mean μ x.1 x.2 := by
  have hp : mean μ x.1 x.2 ≠ 0 := (mem_active μ x |>.mp hx).ne'
  unfold conditionalMean
  field_simp
  ring

private theorem posterior_product (μ : FiniteLaw (Injection d q))
    (x y z : Fin d × Fin q) (hx : x ∈ active μ) (hcolor : y.2 = z.2) :
    mean μ x.1 x.2 * posteriorMean μ x y * posteriorMean μ x z =
      mean μ x.1 x.2 * conditionalMean μ x y * conditionalMean μ x z -
        if x = y ∧ y = z then mean μ x.1 x.2 else 0 := by
  rw [posteriorMean_eq μ x y hx, posteriorMean_eq μ x z hx]
  change mean μ x.1 x.2 * (conditionalMean μ x y - if x = y then 1 else 0) *
    (conditionalMean μ x z - if x = z then 1 else 0) = _
  by_cases hxy : x = y
  · subst y
    rw [conditionalMean_same_color μ x x hx rfl,
      conditionalMean_same_color μ x z hx hcolor]
    simp only [ite_true, sub_self, mul_zero, true_and]
    split_ifs <;> ring
  · by_cases hxz : x = z
    · subst z
      rw [conditionalMean_same_color μ x y hx hcolor.symm,
        conditionalMean_same_color μ x x hx rfl]
      simp [hxy]
    · simp only [hxy, hxz, ite_false, sub_zero, false_and]

/-- Exact posterior second moments retain the negative same-color correction.
This is the entrywise content of Lemma 4.5, with the expectation multiplied by d. -/
theorem posterior_second_moment (μ : FiniteLaw (Injection d q))
    (y z : Fin d × Fin q) (hcolor : y.2 = z.2) :
    ∑ x ∈ active μ, mean μ x.1 x.2 * posteriorMean μ x y * posteriorMean μ x z =
      (d : ℝ) * mean μ y.1 y.2 * mean μ z.1 z.2 +
      (∑ x ∈ active μ, covariance μ y x * covariance μ z x / mean μ x.1 x.2) -
      if y = z then mean μ y.1 y.2 else 0 := by
  classical
  have hcorrect : (∑ x ∈ active μ,
      if x = y ∧ y = z then mean μ x.1 x.2 else 0) =
      if y = z then mean μ y.1 y.2 else 0 := by
    by_cases hyz : y = z
    · subst z
      by_cases hy : y ∈ active μ
      · simp [hy]
      · simp [hy, mean_eq_zero_of_not_active μ hy]
    · simp [hyz]
  calc
    _ = (∑ x ∈ active μ,
        mean μ x.1 x.2 * conditionalMean μ x y * conditionalMean μ x z) -
        if y = z then mean μ y.1 y.2 else 0 := by
      rw [← hcorrect, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      exact posterior_product μ x y z hx hcolor
    _ = _ := by
      congr 1
      calc
        _ = ∑ x ∈ active μ,
            (mean μ x.1 x.2 * mean μ y.1 y.2 * mean μ z.1 z.2 +
              mean μ y.1 y.2 * covariance μ z x +
              mean μ z.1 z.2 * covariance μ y x +
              covariance μ y x * covariance μ z x / mean μ x.1 x.2) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact conditional_product_expand μ x y z hx
        _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
            active_mean_total, active_covariance_total, mul_zero, add_zero]

end EdgeColoringMixing.WeightedInjection
