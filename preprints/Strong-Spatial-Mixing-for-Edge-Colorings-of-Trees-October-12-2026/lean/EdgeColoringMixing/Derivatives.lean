import EdgeColoringMixing.WeightedInjections
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option autoImplicit false

namespace EdgeColoringMixing.WeightedInjection
open Finset

variable {d q : ℕ}

/-- Change exactly one entry of the actual weight matrix. -/
def replaceEntry (W : Fin d → Fin q → ℝ) (i : Fin d) (c : Fin q) (a : ℝ) :
    Fin d → Fin q → ℝ := Function.update W i (Function.update (W i) c a)

@[simp] theorem replaceEntry_self (W : Fin d → Fin q → ℝ) (i : Fin d) (c : Fin q) :
    replaceEntry W i c (W i c) = W := by
  simp [replaceEntry]

theorem weight_replaceEntry (W : Fin d → Fin q → ℝ) (i : Fin d) (c : Fin q)
    (hW : W i c ≠ 0) (a : ℝ) (σ : Injection d q) :
    weight (replaceEntry W i c a) σ =
      if σ i = c then a * weight W σ / W i c else weight W σ := by
  classical
  by_cases hc : σ i = c
  · have hf : (fun j => replaceEntry W i c a j (σ j)) =
        Function.update (fun j => W j (σ j)) i a := by
      ext j
      by_cases hji : j = i <;> simp [replaceEntry, hji, hc]
    simp only [hc, ite_true, weight, hf]
    rw [Finset.prod_update_of_mem (mem_univ i)]
    have hp := Finset.mul_prod_erase univ (fun j => W j (σ j)) (mem_univ i)
    rw [hc] at hp
    rw [← hp]
    field_simp
    rw [Finset.sdiff_singleton_eq_erase]
  · have hf : (fun j => replaceEntry W i c a j (σ j)) = (fun j => W j (σ j)) := by
      ext j
      by_cases hji : j = i <;> simp [replaceEntry, hji, hc]
    simp only [hc, ite_false, weight, hf]

theorem hasDerivAt_weight_replaceEntry (W : Fin d → Fin q → ℝ)
    (i : Fin d) (c : Fin q) (hW : W i c ≠ 0) (σ : Injection d q) :
    HasDerivAt (fun a => weight (replaceEntry W i c a) σ)
      (weight W σ * cell i c σ / W i c) (W i c) := by
  simp_rw [weight_replaceEntry W i c hW]
  by_cases hc : σ i = c
  · simp only [hc, ite_true, cell, mul_one]
    convert! (hasDerivAt_id (W i c)).mul_const (weight W σ / W i c) using 1
    · ext a
      dsimp only [id]
      ring
    · ring
  · simpa only [hc, ite_false, cell, mul_zero, zero_div] using
      hasDerivAt_const (W i c) (weight W σ)

noncomputable def numerator (W : Fin d → Fin q → ℝ) (f : Injection d q → ℝ) : ℝ :=
  ∑ σ, weight W σ * f σ

/-- The actual polynomial-ratio expectation, defined also away from the probability domain. -/
noncomputable def weightedExpectation (W : Fin d → Fin q → ℝ)
    (f : Injection d q → ℝ) : ℝ := numerator W f / partition W

theorem weightedExpectation_eq (W : Fin d → Fin q → ℝ)
    (hW : ∀ i c, 0 ≤ W i c) (hZ : 0 < partition W) (f : Injection d q → ℝ) :
    weightedExpectation W f = (law W hW hZ).expectation f := by
  unfold weightedExpectation numerator FiniteLaw.expectation law
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]

theorem hasDerivAt_numerator (W : Fin d → Fin q → ℝ) (i : Fin d) (c : Fin q)
    (hW : W i c ≠ 0) (f : Injection d q → ℝ) :
    HasDerivAt (fun a => numerator (replaceEntry W i c a) f)
      (numerator W (fun σ => f σ * cell i c σ) / W i c) (W i c) := by
  have h := HasDerivAt.fun_sum (u := univ) (fun σ _ =>
    (hasDerivAt_weight_replaceEntry W i c hW σ).mul_const (f σ))
  have heq : (∑ σ, (weight W σ * cell i c σ / W i c) * f σ) =
      numerator W (fun σ => f σ * cell i c σ) / W i c := by
    rw [numerator, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  exact heq ▸ h

theorem hasDerivAt_partition (W : Fin d → Fin q → ℝ) (i : Fin d) (c : Fin q)
    (hW : W i c ≠ 0) :
    HasDerivAt (fun a => partition (replaceEntry W i c a))
      (numerator W (cell i c) / W i c) (W i c) := by
  simpa [numerator, partition] using hasDerivAt_numerator W i c hW (fun _ => 1)

/-- Lemma 2.2: the actual entry derivative equals covariance divided by the entry weight. -/
theorem derivative_expectation_covariance (W : Fin d → Fin q → ℝ)
    (hW : ∀ i c, 0 ≤ W i c) (hZ : 0 < partition W)
    (i : Fin d) (c : Fin q) (hic : 0 < W i c) (f : Injection d q → ℝ) :
    HasDerivAt (fun a => weightedExpectation (replaceEntry W i c a) f)
      ((law W hW hZ).covariance f (cell i c) / W i c) (W i c) := by
  have h := (hasDerivAt_numerator W i c hic.ne' f).div
    (hasDerivAt_partition W i c hic.ne') (by simpa using hZ.ne')
  simp only [replaceEntry_self] at h
  have heq :
      ((numerator W (fun σ => f σ * cell i c σ) / W i c) * partition W -
        numerator W f * (numerator W (cell i c) / W i c)) / (partition W)^2 =
      (law W hW hZ).covariance f (cell i c) / W i c := by
    rw [FiniteLaw.covariance_eq_mixed_moment,
      ← weightedExpectation_eq W hW hZ, ← weightedExpectation_eq W hW hZ,
      ← weightedExpectation_eq W hW hZ]
    unfold weightedExpectation
    field_simp
  exact heq ▸ h

end EdgeColoringMixing.WeightedInjection
