import HardCoreActivityThreshold.HeatBath

/-! Conditional resampling is a self-adjoint projection in the actual probability inner product. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def siteOperator (μ : FiniteLaw (Finset V)) (v : V)
    (f : Finset V → ℝ) (s : Finset V) : ℝ := ∑ t, singleSiteKernel μ v s t * f t

noncomputable def probabilityInner (μ : FiniteLaw (Finset V))
    (f g : Finset V → ℝ) : ℝ := μ.expectation (fun s => f s * g s)

omit [DecidableEq V] in
theorem probabilityInner_symm (μ : FiniteLaw (Finset V)) (f g : Finset V → ℝ) :
    probabilityInner μ f g = probabilityInner μ g f := by
  unfold probabilityInner
  simp_rw [mul_comm]

theorem siteOperator_selfAdjoint (μ : FiniteLaw (Finset V)) (v : V)
    (f g : Finset V → ℝ) :
    probabilityInner μ f (siteOperator μ v g) =
      probabilityInner μ (siteOperator μ v f) g := by
  unfold probabilityInner FiniteLaw.expectation siteOperator
  simp_rw [mul_sum, sum_mul]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  apply sum_congr rfl
  intro t _
  have h := singleSiteKernel_reversible μ v s t
  calc
    μ.mass t * (f t * (singleSiteKernel μ v t s * g s)) =
        (μ.mass t * singleSiteKernel μ v t s) * (f t * g s) := by ring
    _ = (μ.mass s * singleSiteKernel μ v s t) * (f t * g s) := by rw [h]
    _ = μ.mass s * (singleSiteKernel μ v s t * f t * g s) := by ring

theorem siteOperator_zeroFiber (μ : FiniteLaw (Finset V)) (v : V)
    (f : Finset V → ℝ) (s : Finset V) (hz : fiberMass μ v s = 0) :
    siteOperator μ v f s = f s := by
  have hk (t : Finset V) : singleSiteKernel μ v s t = if t = s then 1 else 0 := by
    by_cases h : t = s
    · subst t
      simp [singleSiteKernel, hz]
    · simp [singleSiteKernel, hz, h, Ne.symm h]
  unfold siteOperator
  simp_rw [hk]
  simp

theorem siteOperator_sameOutside (μ : FiniteLaw (Finset V)) (v : V)
    (f : Finset V → ℝ) {s t : Finset V} (hst : sameOutside v s t)
    (hz : fiberMass μ v s ≠ 0) : siteOperator μ v f s = siteOperator μ v f t := by
  have hm := fiberMass_eq μ hst
  unfold siteOperator
  apply sum_congr rfl
  intro u _
  have he : sameOutside v s u ↔ sameOutside v t u := by
    unfold sameOutside at *
    rw [hst]
  simp only [singleSiteKernel, ← hm, hz, ite_false, he]

theorem siteOperator_idempotent (μ : FiniteLaw (Finset V)) (v : V)
    (f : Finset V → ℝ) : siteOperator μ v (siteOperator μ v f) = siteOperator μ v f := by
  funext s
  by_cases hz : fiberMass μ v s = 0
  · rw [siteOperator_zeroFiber μ v (siteOperator μ v f) s hz]
  · change (∑ t, singleSiteKernel μ v s t * siteOperator μ v f t) = _
    calc
      (∑ t, singleSiteKernel μ v s t * siteOperator μ v f t) =
          ∑ t, singleSiteKernel μ v s t * siteOperator μ v f s := by
        apply sum_congr rfl
        intro t _
        by_cases hst : sameOutside v s t
        · rw [siteOperator_sameOutside μ v f hst hz]
        · simp [singleSiteKernel, hst]
      _ = siteOperator μ v f s := by rw [← sum_mul, singleSiteKernel_row_sum, one_mul]

theorem siteOperator_quadratic_eq_sq (μ : FiniteLaw (Finset V)) (v : V)
    (f : Finset V → ℝ) :
    probabilityInner μ f (siteOperator μ v f) =
      probabilityInner μ (siteOperator μ v f) (siteOperator μ v f) := by
  have h := siteOperator_selfAdjoint μ v f (siteOperator μ v f)
  rw [siteOperator_idempotent] at h
  exact h

theorem siteOperator_positive (μ : FiniteLaw (Finset V)) (v : V)
    (f : Finset V → ℝ) : 0 ≤ probabilityInner μ f (siteOperator μ v f) := by
  rw [siteOperator_quadratic_eq_sq]
  exact μ.expectation_nonneg (fun s => mul_self_nonneg _)

/-- Expected conditional variance for a single heat-bath update. -/
noncomputable def siteConditionalVariance (μ : FiniteLaw (Finset V)) (v : V)
    (f : Finset V → ℝ) : ℝ :=
  μ.expectation (fun s => (f s - siteOperator μ v f s) ^ 2)

theorem siteConditionalVariance_nonneg (μ : FiniteLaw (Finset V)) (v : V)
    (f : Finset V → ℝ) : 0 ≤ siteConditionalVariance μ v f :=
  μ.expectation_nonneg (fun _ => sq_nonneg _)

theorem siteOperator_expectation (μ : FiniteLaw (Finset V)) (v : V)
    (f : Finset V → ℝ) : μ.expectation (siteOperator μ v f) = μ.expectation f := by
  unfold FiniteLaw.expectation siteOperator
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  calc
    (∑ s, μ.mass s * (singleSiteKernel μ v s t * f t)) =
        ∑ s, (μ.mass t * singleSiteKernel μ v t s) * f t := by
      apply sum_congr rfl
      intro s _
      rw [← mul_assoc, singleSiteKernel_reversible]
    _ = μ.mass t * f t := by
      rw [← sum_mul, ← mul_sum, singleSiteKernel_row_sum, mul_one]

theorem siteConditionalVariance_eq_moments (μ : FiniteLaw (Finset V)) (v : V)
    (f : Finset V → ℝ) :
    siteConditionalVariance μ v f = μ.expectation (fun s => f s ^ 2) -
      probabilityInner μ f (siteOperator μ v f) := by
  unfold siteConditionalVariance
  have h (s : Finset V) : (f s - siteOperator μ v f s)^2 =
      f s ^ 2 - 2 * (f s * siteOperator μ v f s) + (siteOperator μ v f s)^2 := by ring
  simp_rw [h]
  rw [FiniteLaw.expectation_add, FiniteLaw.expectation_sub, FiniteLaw.expectation_smul]
  have hsq : μ.expectation (fun s => siteOperator μ v f s ^ 2) =
      probabilityInner μ f (siteOperator μ v f) := by
    rw [siteOperator_quadratic_eq_sq]
    simp only [probabilityInner, pow_two]
  rw [hsq]
  change _ - 2 * probabilityInner μ f (siteOperator μ v f) + _ = _
  ring

/-- The law of total variance for the explicitly constructed conditional projection. -/
theorem siteConditionalVariance_eq_variance_sub (μ : FiniteLaw (Finset V)) (v : V)
    (f : Finset V → ℝ) :
    siteConditionalVariance μ v f = μ.variance f - μ.variance (siteOperator μ v f) := by
  rw [siteConditionalVariance_eq_moments, μ.variance_eq_second_moment,
    μ.variance_eq_second_moment, siteOperator_expectation,
    siteOperator_quadratic_eq_sq]
  simp only [probabilityInner, pow_two]
  ring

theorem siteConditionalVariance_le_variance (μ : FiniteLaw (Finset V)) (v : V)
    (f : Finset V → ℝ) : siteConditionalVariance μ v f ≤ μ.variance f := by
  rw [siteConditionalVariance_eq_variance_sub]
  exact sub_le_self _ (μ.variance_nonneg _)

noncomputable def siteDirichletForm (μ : FiniteLaw (Finset V)) (v : V)
    (f : Finset V → ℝ) : ℝ :=
  (∑ s, ∑ t, μ.mass s * singleSiteKernel μ v s t * (f s - f t)^2) / 2

theorem siteDirichletForm_eq_conditionalVariance (μ : FiniteLaw (Finset V)) (v : V)
    (f : Finset V → ℝ) : siteDirichletForm μ v f = siteConditionalVariance μ v f := by
  have ha : (∑ s, ∑ t, μ.mass s * singleSiteKernel μ v s t * f s ^ 2) =
      μ.expectation (fun s => f s ^ 2) := by
    unfold FiniteLaw.expectation
    apply sum_congr rfl
    intro s _
    rw [← sum_mul, ← mul_sum, singleSiteKernel_row_sum, mul_one]
  have hb : (∑ s, ∑ t, μ.mass s * singleSiteKernel μ v s t * f t ^ 2) =
      μ.expectation (fun s => f s ^ 2) := by
    rw [sum_comm]
    simp_rw [singleSiteKernel_reversible]
    exact ha
  have hc : (∑ s, ∑ t, μ.mass s * singleSiteKernel μ v s t * (f s * f t)) =
      probabilityInner μ f (siteOperator μ v f) := by
    unfold probabilityInner FiniteLaw.expectation siteOperator
    simp_rw [mul_sum]
    apply sum_congr rfl
    intro s _
    apply sum_congr rfl
    intro t _
    ring
  have hsplit : (∑ s, ∑ t, μ.mass s * singleSiteKernel μ v s t * (f s - f t)^2) =
      (∑ s, ∑ t, μ.mass s * singleSiteKernel μ v s t * f s ^ 2) -
      2 * (∑ s, ∑ t, μ.mass s * singleSiteKernel μ v s t * (f s * f t)) +
      (∑ s, ∑ t, μ.mass s * singleSiteKernel μ v s t * f t ^ 2) := by
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro s _
    apply sum_congr rfl
    intro t _
    ring
  unfold siteDirichletForm
  rw [hsplit, ha, hb, hc, siteConditionalVariance_eq_moments]
  ring

/-- The Markov-chain Dirichlet form is exactly the mean of the single-site conditional variances. -/
theorem dirichletForm_eq_mean_conditionalVariance (μ : FiniteLaw (Finset V))
    (f : Finset V → ℝ) :
    dirichletForm μ f = (∑ v : V, siteConditionalVariance μ v f) / Fintype.card V := by
  have ht (s t : Finset V) : μ.mass s * heatBathKernel μ s t * (f s - f t)^2 =
      (∑ v, μ.mass s * singleSiteKernel μ v s t * (f s - f t)^2) / Fintype.card V := by
    unfold heatBathKernel
    rw [← mul_div_assoc, div_mul_eq_mul_div, mul_sum, sum_mul]
  have hswap : (∑ s, ∑ t, ∑ v, μ.mass s * singleSiteKernel μ v s t * (f s - f t)^2) =
      ∑ v, ∑ s, ∑ t, μ.mass s * singleSiteKernel μ v s t * (f s - f t)^2 := by
    calc
      _ = ∑ s, ∑ v, ∑ t, μ.mass s * singleSiteKernel μ v s t * (f s - f t)^2 := by
        apply sum_congr rfl
        intro s _
        exact sum_comm
      _ = _ := sum_comm
  unfold dirichletForm
  simp_rw [ht, ← sum_div]
  rw [hswap]
  simp_rw [← siteDirichletForm_eq_conditionalVariance]
  unfold siteDirichletForm
  rw [← sum_div]
  ring

theorem dirichletForm_le_variance [Nonempty V] (μ : FiniteLaw (Finset V))
    (f : Finset V → ℝ) : dirichletForm μ f ≤ μ.variance f := by
  rw [dirichletForm_eq_mean_conditionalVariance]
  have hn : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hn).mpr
  calc
    (∑ v : V, siteConditionalVariance μ v f) ≤ ∑ _v : V, μ.variance f :=
      sum_le_sum (fun v _ => siteConditionalVariance_le_variance μ v f)
    _ = μ.variance f * Fintype.card V := by simp [mul_comm]

theorem heatBathGap_le_one [Nonempty V] (μ : FiniteLaw (Finset V)) : heatBathGap μ ≤ 1 := by
  by_cases h : ∃ f : Finset V → ℝ, 0 < μ.variance f
  · obtain ⟨f, hf⟩ := h
    calc
      heatBathGap μ ≤ dirichletForm μ f / μ.variance f := heatBathGap_le_rayleigh μ f hf
      _ ≤ 1 := (div_le_one hf).mpr (dirichletForm_le_variance μ f)
  · simp [heatBathGap, h]

end HardCoreActivityThreshold
