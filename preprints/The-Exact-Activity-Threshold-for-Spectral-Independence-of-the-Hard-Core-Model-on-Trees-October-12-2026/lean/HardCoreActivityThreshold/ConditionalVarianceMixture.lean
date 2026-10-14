import HardCoreActivityThreshold.HeatBathVariance
import HardCoreActivityThreshold.FiniteObservation
import HardCoreActivityThreshold.GapLower

/-! Single-site conditional variance is concave under finite mixtures of genuine laws. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def ConstantOutsideOn (μ : FiniteLaw (Finset V)) (v : V) (g : Finset V → ℝ) : Prop :=
  ∀ s t, 0 < μ.mass s → 0 < μ.mass t → sameOutside v s t → g s = g t

theorem fiberMass_pos_of_mass_pos (μ : FiniteLaw (Finset V)) (v : V)
    {s : Finset V} (hs : 0 < μ.mass s) : 0 < fiberMass μ v s :=
  lt_of_lt_of_le hs (μ.mass_le_eventMass (sameOutside_refl v s))

theorem siteOperator_constantOutsideOn (μ : FiniteLaw (Finset V)) (v : V)
    (f : Finset V → ℝ) : ConstantOutsideOn μ v (siteOperator μ v f) := by
  intro s t hs _ hst
  exact siteOperator_sameOutside μ v f hst (fiberMass_pos_of_mass_pos μ v hs).ne'

theorem siteOperator_eq_of_constantOutsideOn (μ : FiniteLaw (Finset V)) (v : V)
    (g : Finset V → ℝ) (hg : ConstantOutsideOn μ v g)
    {s : Finset V} (hs : 0 < μ.mass s) : siteOperator μ v g s = g s := by
  have hz := (fiberMass_pos_of_mass_pos μ v hs).ne'
  calc
    siteOperator μ v g s = ∑ t, singleSiteKernel μ v s t * g s := by
      apply sum_congr rfl
      intro t _
      by_cases hst : sameOutside v s t
      · by_cases ht : 0 < μ.mass t
        · rw [hg s t hs ht hst]
        · have ht0 : μ.mass t = 0 := le_antisymm (le_of_not_gt ht) (μ.nonneg t)
          simp [singleSiteKernel, hst, hz, ht0]
      · simp [singleSiteKernel, hst]
    _ = g s := by rw [← sum_mul, singleSiteKernel_row_sum, one_mul]

theorem siteOperator_inner_eq_of_constantOutsideOn (μ : FiniteLaw (Finset V))
    (v : V) (f g : Finset V → ℝ) (hg : ConstantOutsideOn μ v g) :
    probabilityInner μ (siteOperator μ v f) g = probabilityInner μ f g := by
  rw [← siteOperator_selfAdjoint]
  apply μ.expectation_congr_on_support
  intro s hs
  rw [siteOperator_eq_of_constantOutsideOn μ v g hg hs]

/-- The conditional mean minimizes the true mean squared error among outside-measurable functions. -/
theorem siteOperator_bestApproximation (μ : FiniteLaw (Finset V)) (v : V)
    (f g : Finset V → ℝ) (hg : ConstantOutsideOn μ v g) :
    μ.expectation (fun s => (f s - g s)^2) = siteConditionalVariance μ v f +
      μ.expectation (fun s => (siteOperator μ v f s - g s)^2) := by
  have hsq (a b : ℝ) : (a - b)^2 = a^2 - 2*(a*b) + b^2 := by ring
  simp_rw [hsq]
  rw [μ.expectation_add, μ.expectation_sub, μ.expectation_smul,
    μ.expectation_add, μ.expectation_sub, μ.expectation_smul,
    siteConditionalVariance_eq_moments]
  have hcross : μ.expectation (fun s => siteOperator μ v f s * g s) =
      μ.expectation (fun s => f s * g s) :=
    siteOperator_inner_eq_of_constantOutsideOn μ v f g hg
  have hself : μ.expectation (fun s => siteOperator μ v f s ^ 2) =
      probabilityInner μ f (siteOperator μ v f) := by
    rw [siteOperator_quadratic_eq_sq]
    simp only [probabilityInner, pow_two]
  rw [hcross, hself]
  ring

theorem siteConditionalVariance_le_approximation (μ : FiniteLaw (Finset V)) (v : V)
    (f g : Finset V → ℝ) (hg : ConstantOutsideOn μ v g) :
    siteConditionalVariance μ v f ≤ μ.expectation (fun s => (f s - g s)^2) := by
  rw [siteOperator_bestApproximation μ v f g hg]
  exact le_add_of_nonneg_right (μ.expectation_nonneg (fun _ => sq_nonneg _))

/-- Conditioning on any additional finite observation decreases each expected single-site variance. -/
theorem siteConditionalVariance_mixture_le {ι : Type*} [Fintype ι]
    (μ : FiniteLaw (Finset V)) (ν : ι → FiniteLaw (Finset V)) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmix : ∀ s, μ.mass s = ∑ i, w i * (ν i).mass s)
    (v : V) (f : Finset V → ℝ) :
    (∑ i, w i * siteConditionalVariance (ν i) v f) ≤ siteConditionalVariance μ v f := by
  have hsupp (i : ι) (hi : 0 < w i) (s : Finset V) (hs : 0 < (ν i).mass s) :
      0 < μ.mass s := by
    rw [hmix]
    exact lt_of_lt_of_le (mul_pos hi hs)
      (single_le_sum (fun j _ => mul_nonneg (hw j) ((ν j).nonneg s)) (mem_univ i))
  calc
    _ ≤ ∑ i, w i * (ν i).expectation (fun s => (f s - siteOperator μ v f s)^2) := by
      apply sum_le_sum
      intro i _
      by_cases hi : 0 < w i
      · apply mul_le_mul_of_nonneg_left _ (hw i)
        apply siteConditionalVariance_le_approximation
        intro s t hs _ hst
        exact siteOperator_sameOutside μ v f hst
          (fiberMass_pos_of_mass_pos μ v (hsupp i hi s hs)).ne'
      · have hz : w i = 0 := le_antisymm (le_of_not_gt hi) (hw i)
        rw [hz, zero_mul, zero_mul]
    _ = _ := (μ.expectation_mixture ν w hmix _).symm

namespace ObservationChannel
variable {A : Type*} [Fintype A]

theorem posterior_siteVariance_le (K : ObservationChannel (Finset V) A)
    (μ : FiniteLaw (Finset V)) (v : V) (f : Finset V → ℝ) :
    (∑ a, (K.output μ).mass a * siteConditionalVariance (K.posterior μ a) v f) ≤
      siteConditionalVariance μ v f :=
  siteConditionalVariance_mixture_le μ (K.posterior μ) (K.output μ).mass
    (K.output μ).nonneg (K.posterior_mixture μ) v f

/-- Tensorization of every nonnull posterior transfers through any retained-variance lower bound. -/
theorem tensorization_of_retainedVariance (K : ObservationChannel (Finset V) A)
    (μ : FiniteLaw (Finset V)) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hret : ∀ f, c * μ.variance f ≤ K.retainedVariance μ f)
    (hpost : ∀ a, 0 < (K.output μ).mass a → VarianceTensorization (K.posterior μ a) C) :
    VarianceTensorization μ (C / c) := by
  intro f
  have hbound : K.retainedVariance μ f ≤ C * ∑ v, siteConditionalVariance μ v f := by
    calc
      _ ≤ ∑ a, (K.output μ).mass a * (C * ∑ v, siteConditionalVariance (K.posterior μ a) v f) := by
        apply sum_le_sum
        intro a _
        by_cases ha : 0 < (K.output μ).mass a
        · exact mul_le_mul_of_nonneg_left (hpost a ha f) ((K.output μ).nonneg a)
        · have hz : (K.output μ).mass a = 0 :=
            le_antisymm (le_of_not_gt ha) ((K.output μ).nonneg a)
          rw [hz, zero_mul, zero_mul]
      _ = C * ∑ v, ∑ a, (K.output μ).mass a * siteConditionalVariance (K.posterior μ a) v f := by
        calc
          _ = C * ∑ a, ∑ v, (K.output μ).mass a *
              siteConditionalVariance (K.posterior μ a) v f := by
            simp only [mul_sum]
            apply sum_congr rfl
            intro a _
            apply sum_congr rfl
            intro v _
            ring
          _ = _ := by rw [sum_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_le_sum (fun v _ => K.posterior_siteVariance_le μ v f)) hC
  have hh := (hret f).trans hbound
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hc).mpr (by nlinarith)

end ObservationChannel
end HardCoreActivityThreshold
