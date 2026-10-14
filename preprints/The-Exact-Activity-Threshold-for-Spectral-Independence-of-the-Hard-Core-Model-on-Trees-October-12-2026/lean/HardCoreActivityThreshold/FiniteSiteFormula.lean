import HardCoreActivityThreshold.ConditionalVarianceMixture
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Exact two-point formulae for conditional resampling on finite subset configurations. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sum_config_split (v : V) (f : Finset V → ℝ) :
    (∑ s, f s) = ∑ s, if v ∉ s then f s + f (insert v s) else 0 := by
  have hp : (univ : Finset (Finset V)) = (univ : Finset V).powerset := by
    ext s
    simp
  have he : ((univ : Finset V).erase v).powerset =
      (univ : Finset (Finset V)).filter (fun s => v ∉ s) := by
    ext s
    simp [subset_erase]
  calc
    (∑ s, f s) = ∑ s ∈ (univ : Finset V).powerset, f s := by rw [← hp]
    _ = ∑ s ∈ ((univ : Finset V).erase v).powerset, (f s + f (insert v s)) := by
      conv_lhs => rw [← insert_erase (mem_univ v)]
      rw [sum_powerset_insert (notMem_erase v univ), sum_add_distrib]
    _ = _ := by rw [he, sum_filter]

omit [Fintype V] in
theorem sameOutside_iff_two (v : V) (s t : Finset V) :
    sameOutside v s t ↔ t = s.erase v ∨ t = insert v s := by
  constructor
  · intro h
    by_cases ht : v ∈ t
    · right
      calc
        t = insert v (t.erase v) := (insert_erase ht).symm
        _ = insert v (s.erase v) := by rw [h]
        _ = insert v s := by simp
    · left
      rw [← erase_eq_of_notMem ht, ← h]
  · rintro (rfl | rfl) <;> simp [sameOutside]

theorem sum_sameOutside (v : V) (s : Finset V) (f : Finset V → ℝ) :
    (∑ t, if sameOutside v s t then f t else 0) = f (s.erase v) + f (insert v s) := by
  have he : (univ : Finset (Finset V)).filter (sameOutside v s) =
      {s.erase v, insert v s} := by
    ext t
    simp [sameOutside_iff_two]
  have hn : s.erase v ≠ insert v s := by
    intro h
    have : v ∈ s.erase v := by rw [h]; exact mem_insert_self _ _
    exact notMem_erase v s this
  rw [← sum_filter, he, sum_pair hn]

theorem fiberMass_eq_two (μ : FiniteLaw (Finset V)) (v : V) (s : Finset V) :
    fiberMass μ v s = μ.mass (s.erase v) + μ.mass (insert v s) :=
  sum_sameOutside v s μ.mass

theorem siteOperator_eq_two (μ : FiniteLaw (Finset V)) (v : V)
    (f : Finset V → ℝ) (s : Finset V) (hz : fiberMass μ v s ≠ 0) :
    siteOperator μ v f s =
      (μ.mass (s.erase v) * f (s.erase v) + μ.mass (insert v s) * f (insert v s)) /
        (μ.mass (s.erase v) + μ.mass (insert v s)) := by
  have he (t : Finset V) : singleSiteKernel μ v s t * f t =
      (if sameOutside v s t then μ.mass t * f t else 0) / fiberMass μ v s := by
    by_cases ht : sameOutside v s t <;> simp [singleSiteKernel, ht, hz, div_mul_eq_mul_div]
  unfold siteOperator
  simp_rw [he]
  rw [← sum_div, sum_sameOutside, fiberMass_eq_two]

theorem siteDirichlet_row_two (μ : FiniteLaw (Finset V)) (v : V)
    (f : Finset V → ℝ) (s : Finset V) :
    (∑ t, μ.mass s * singleSiteKernel μ v s t * (f s - f t)^2) =
      μ.mass s / fiberMass μ v s *
        (μ.mass (s.erase v) * (f s - f (s.erase v))^2 +
          μ.mass (insert v s) * (f s - f (insert v s))^2) := by
  by_cases hz : fiberMass μ v s = 0
  · have hm : μ.mass s = 0 := μ.mass_zero_of_eventMass_zero (sameOutside_refl v s) hz
    simp [hm]
  · have he (t : Finset V) :
        μ.mass s * singleSiteKernel μ v s t * (f s - f t)^2 =
        μ.mass s / fiberMass μ v s *
          (if sameOutside v s t then μ.mass t * (f s - f t)^2 else 0) := by
      by_cases ht : sameOutside v s t
      · simp only [singleSiteKernel, ht, ite_true, hz, ite_false]
        ring
      · simp [singleSiteKernel, ht]
    simp_rw [he]
    rw [← mul_sum, sum_sameOutside]

/-- One summand per vacant configuration, valid also on zero-mass fibers. -/
theorem siteConditionalVariance_eq_pairs (μ : FiniteLaw (Finset V)) (v : V)
    (f : Finset V → ℝ) :
    siteConditionalVariance μ v f =
      ∑ s, if v ∉ s then μ.mass s * μ.mass (insert v s) /
        (μ.mass s + μ.mass (insert v s)) * (f s - f (insert v s))^2 else 0 := by
  rw [← siteDirichletForm_eq_conditionalVariance]
  unfold siteDirichletForm
  simp_rw [siteDirichlet_row_two]
  rw [sum_config_split v, sum_div]
  apply sum_congr rfl
  intro s _
  by_cases hs : v ∉ s
  · simp only [hs, not_false_eq_true, ite_true, fiberMass_eq_two, erase_eq_of_notMem hs,
      erase_insert hs, insert_idem, sub_self, zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_add, add_zero]
    have he : (f (insert v s) - f s)^2 = (f s - f (insert v s))^2 := by ring
    rw [he]
    ring
  · simp [hs]

end HardCoreActivityThreshold
