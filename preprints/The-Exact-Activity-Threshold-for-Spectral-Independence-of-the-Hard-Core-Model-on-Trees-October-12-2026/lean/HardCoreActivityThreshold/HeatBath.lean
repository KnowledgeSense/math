import HardCoreActivityThreshold.HardCoreLaw
import Mathlib.Data.Matrix.Basic

/-! The heat-bath chain is constructed by conditioning on all coordinates except one. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem mass_le_eventMass (μ : FiniteLaw Ω) {E : Ω → Prop} {x : Ω} (hx : E x) :
    μ.mass x ≤ μ.eventMass E := by
  classical
  calc
    μ.mass x = (if E x then μ.mass x else 0) := by simp [hx]
    _ ≤ ∑ y, if E y then μ.mass y else 0 := by
      apply single_le_sum _ (mem_univ x)
      intro y _
      split_ifs
      · exact μ.nonneg y
      · rfl

theorem mass_zero_of_eventMass_zero (μ : FiniteLaw Ω) {E : Ω → Prop} {x : Ω}
    (hx : E x) (h : μ.eventMass E = 0) : μ.mass x = 0 := by
  have hm := μ.mass_le_eventMass hx
  rw [h] at hm
  exact le_antisymm hm (μ.nonneg x)

end FiniteLaw

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All coordinates other than the selected vertex agree. -/
def sameOutside (v : V) (s t : Finset V) : Prop := s.erase v = t.erase v

omit [Fintype V] in
@[simp] theorem sameOutside_refl (v : V) (s : Finset V) : sameOutside v s s := rfl

omit [Fintype V] in
theorem sameOutside_symm (v : V) (s t : Finset V) :
    sameOutside v s t ↔ sameOutside v t s := eq_comm

noncomputable def fiberMass (μ : FiniteLaw (Finset V)) (v : V) (s : Finset V) : ℝ :=
  μ.eventMass (sameOutside v s)

theorem fiberMass_eq (μ : FiniteLaw (Finset V)) {v : V} {s t : Finset V}
    (h : sameOutside v s t) : fiberMass μ v s = fiberMass μ v t := by
  unfold fiberMass FiniteLaw.eventMass
  apply sum_congr rfl
  intro u _
  have he : sameOutside v s u ↔ sameOutside v t u := by
    unfold sameOutside at *
    rw [h]
  simp only [he]

/-- Conditional resampling at one vertex. Null-probability rows are completed by self-loops. -/
noncomputable def singleSiteKernel (μ : FiniteLaw (Finset V)) (v : V) :
    Matrix (Finset V) (Finset V) ℝ := fun s t =>
  if sameOutside v s t then
    if fiberMass μ v s = 0 then (if s = t then 1 else 0)
    else μ.mass t / fiberMass μ v s
  else 0

theorem singleSiteKernel_nonneg (μ : FiniteLaw (Finset V)) (v : V) (s t : Finset V) :
    0 ≤ singleSiteKernel μ v s t := by
  unfold singleSiteKernel
  split_ifs
  · norm_num
  · rfl
  · exact div_nonneg (μ.nonneg t) (μ.eventMass_nonneg _)
  · rfl

theorem singleSiteKernel_row_sum (μ : FiniteLaw (Finset V)) (v : V) (s : Finset V) :
    ∑ t, singleSiteKernel μ v s t = 1 := by
  classical
  by_cases hzero : fiberMass μ v s = 0
  · have ht (t : Finset V) : singleSiteKernel μ v s t = if t = s then 1 else 0 := by
      by_cases hts : t = s
      · subst t
        simp [singleSiteKernel, hzero]
      · simp [singleSiteKernel, hzero, hts, Ne.symm hts]
    simp_rw [ht]
    simp
  · have ht (t : Finset V) : singleSiteKernel μ v s t =
        (if sameOutside v s t then μ.mass t else 0) / fiberMass μ v s := by
      unfold singleSiteKernel
      split_ifs <;> simp_all
    simp_rw [ht]
    rw [← sum_div]
    exact div_self hzero

/-- Detailed balance for the actual conditional-resampling kernel. -/
theorem singleSiteKernel_reversible (μ : FiniteLaw (Finset V)) (v : V)
    (s t : Finset V) :
    μ.mass s * singleSiteKernel μ v s t = μ.mass t * singleSiteKernel μ v t s := by
  by_cases hst : sameOutside v s t
  · have hts := (sameOutside_symm v s t).mp hst
    have hf := fiberMass_eq μ hst
    by_cases hz : fiberMass μ v s = 0
    · have hs0 : μ.mass s = 0 := μ.mass_zero_of_eventMass_zero (sameOutside_refl v s) hz
      have ht0 : μ.mass t = 0 := μ.mass_zero_of_eventMass_zero hst hz
      simp [hs0, ht0]
    · simp only [singleSiteKernel, hst, hts, ite_true, ← hf, hz, ite_false]
      ring
  · have hts : ¬ sameOutside v t s := by
      simpa only [sameOutside_symm v s t] using hst
    simp [singleSiteKernel, hst, hts]

/-- Uniformly choose one of all vertices and resample its occupation. -/
noncomputable def heatBathKernel (μ : FiniteLaw (Finset V)) :
    Matrix (Finset V) (Finset V) ℝ := fun s t =>
  (∑ v : V, singleSiteKernel μ v s t) / Fintype.card V

theorem heatBathKernel_nonneg (μ : FiniteLaw (Finset V)) (s t : Finset V) :
    0 ≤ heatBathKernel μ s t :=
  div_nonneg (sum_nonneg (fun v _ => singleSiteKernel_nonneg μ v s t)) (Nat.cast_nonneg _)

theorem heatBathKernel_row_sum [Nonempty V] (μ : FiniteLaw (Finset V)) (s : Finset V) :
    ∑ t, heatBathKernel μ s t = 1 := by
  unfold heatBathKernel
  rw [← sum_div, sum_comm]
  simp_rw [singleSiteKernel_row_sum]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero (α := V))

theorem heatBathKernel_reversible (μ : FiniteLaw (Finset V)) (s t : Finset V) :
    μ.mass s * heatBathKernel μ s t = μ.mass t * heatBathKernel μ t s := by
  unfold heatBathKernel
  rw [← mul_div_assoc, ← mul_div_assoc, mul_sum, mul_sum]
  congr 1
  exact sum_congr rfl (fun v _ => singleSiteKernel_reversible μ v s t)

theorem heatBathKernel_stationary [Nonempty V] (μ : FiniteLaw (Finset V)) (t : Finset V) :
    ∑ s, μ.mass s * heatBathKernel μ s t = μ.mass t := by
  simp_rw [heatBathKernel_reversible]
  rw [← mul_sum, heatBathKernel_row_sum, mul_one]

/-- Dirichlet form of the explicitly constructed transition matrix. -/
noncomputable def dirichletForm (μ : FiniteLaw (Finset V)) (f : Finset V → ℝ) : ℝ :=
  (∑ s, ∑ t, μ.mass s * heatBathKernel μ s t * (f s - f t) ^ 2) / 2

theorem dirichletForm_nonneg (μ : FiniteLaw (Finset V)) (f : Finset V → ℝ) :
    0 ≤ dirichletForm μ f := by
  apply div_nonneg _ (by norm_num)
  apply sum_nonneg
  intro s _
  apply sum_nonneg
  intro t _
  exact mul_nonneg (mul_nonneg (μ.nonneg s) (heatBathKernel_nonneg μ s t)) (sq_nonneg _)

/-- The variational spectral gap of the actual heat-bath chain.
The singleton-support case has value one, as in the source manuscript. -/
noncomputable def heatBathGap (μ : FiniteLaw (Finset V)) : ℝ :=
  if ∃ f : Finset V → ℝ, 0 < μ.variance f then
    sInf {r : ℝ | ∃ f : Finset V → ℝ, 0 < μ.variance f ∧ r = dirichletForm μ f / μ.variance f}
  else 1

theorem heatBathGap_nonneg (μ : FiniteLaw (Finset V)) : 0 ≤ heatBathGap μ := by
  unfold heatBathGap
  split_ifs with h
  · apply Real.sInf_nonneg
    rintro r ⟨f, hf, rfl⟩
    exact div_nonneg (dirichletForm_nonneg μ f) hf.le
  · norm_num

theorem heatBathGap_le_rayleigh (μ : FiniteLaw (Finset V)) (f : Finset V → ℝ)
    (hf : 0 < μ.variance f) : heatBathGap μ ≤ dirichletForm μ f / μ.variance f := by
  unfold heatBathGap
  rw [ite_eq_left ⟨f, hf⟩]
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨g, hg, rfl⟩
    exact div_nonneg (dirichletForm_nonneg μ g) hg.le
  · exact ⟨f, hf, rfl⟩

end HardCoreActivityThreshold
