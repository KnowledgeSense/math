import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite probability laws, with normalization and nonnegativity proved in the kernel. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable

/-- A real presentation of a probability law on a finite sample space. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  sum_one : ∑ x, mass x = 1

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

@[ext] theorem ext {μ ν : FiniteLaw Ω} (h : ∀ x, μ.mass x = ν.mass x) : μ = ν := by
  cases μ
  cases ν
  simp_all only [mk.injEq]
  exact funext h

noncomputable def toPMF (μ : FiniteLaw Ω) : PMF Ω :=
  PMF.ofFintype (fun x => ENNReal.ofReal (μ.mass x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => μ.nonneg x), μ.sum_one,
      ENNReal.ofReal_one])

@[simp] theorem toPMF_apply (μ : FiniteLaw Ω) (x : Ω) :
    μ.toPMF x = ENNReal.ofReal (μ.mass x) := rfl

noncomputable def expectation (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  ∑ x, μ.mass x * f x

noncomputable def variance (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  μ.expectation (fun x => (f x - μ.expectation f) ^ 2)

noncomputable def covariance (μ : FiniteLaw Ω) (f g : Ω → ℝ) : ℝ :=
  μ.expectation (fun x => (f x - μ.expectation f) * (g x - μ.expectation g))

@[simp] theorem expectation_const (μ : FiniteLaw Ω) (c : ℝ) :
    μ.expectation (fun _ => c) = c := by
  simp [expectation, ← sum_mul, μ.sum_one]

theorem expectation_add (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.expectation (fun x => f x + g x) = μ.expectation f + μ.expectation g := by
  simp [expectation, mul_add, sum_add_distrib]

theorem expectation_sub (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.expectation (fun x => f x - g x) = μ.expectation f - μ.expectation g := by
  simp [expectation, mul_sub, sum_sub_distrib]

theorem expectation_smul (μ : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    μ.expectation (fun x => c * f x) = c * μ.expectation f := by
  simp only [expectation, mul_sum]
  apply sum_congr rfl
  intro x _
  ring

theorem expectation_sum {ι : Type*} [Fintype ι] (μ : FiniteLaw Ω) (f : ι → Ω → ℝ) :
    μ.expectation (fun x => ∑ i, f i x) = ∑ i, μ.expectation (f i) := by
  simp only [expectation, mul_sum]
  exact sum_comm

theorem expectation_nonneg (μ : FiniteLaw Ω) {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ μ.expectation f := sum_nonneg (fun x _ => mul_nonneg (μ.nonneg x) (hf x))

theorem expectation_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.expectation f ≤ μ.expectation g :=
  sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonneg x))

theorem variance_nonneg (μ : FiniteLaw Ω) (f : Ω → ℝ) : 0 ≤ μ.variance f :=
  μ.expectation_nonneg (fun _ => sq_nonneg _)

theorem variance_eq_second_moment (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.variance f = μ.expectation (fun x => f x ^ 2) - μ.expectation f ^ 2 := by
  unfold variance
  have h (x : Ω) : (f x - μ.expectation f)^2 =
      f x ^ 2 - (2 * μ.expectation f) * f x + μ.expectation f ^ 2 := by ring
  simp_rw [h]
  rw [expectation_add, expectation_sub, expectation_smul, expectation_const]
  ring

theorem covariance_eq_mixed_moment (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.covariance f g = μ.expectation (fun x => f x * g x) -
      μ.expectation f * μ.expectation g := by
  unfold covariance
  have h (x : Ω) : (f x - μ.expectation f) * (g x - μ.expectation g) =
      f x * g x - μ.expectation g * f x - μ.expectation f * g x +
        μ.expectation f * μ.expectation g := by ring
  simp_rw [h]
  rw [expectation_add, expectation_sub, expectation_sub,
    expectation_smul, expectation_smul, expectation_const]
  ring

@[simp] theorem covariance_self (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.covariance f f = μ.variance f := by
  simp [covariance, variance, pow_two]

theorem covariance_symm (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.covariance f g = μ.covariance g f := by
  simp only [covariance, mul_comm]

/-- Probability of a finite event. -/
noncomputable def eventMass (μ : FiniteLaw Ω) (E : Ω → Prop) : ℝ := by
  classical
  exact ∑ x, if E x then μ.mass x else 0

theorem eventMass_nonneg (μ : FiniteLaw Ω) (E : Ω → Prop) :
    0 ≤ μ.eventMass E := by
  classical
  apply sum_nonneg
  intro x _
  split_ifs
  · exact μ.nonneg x
  · rfl

theorem eventMass_le_one (μ : FiniteLaw Ω) (E : Ω → Prop) :
    μ.eventMass E ≤ 1 := by
  classical
  rw [← μ.sum_one]
  apply sum_le_sum
  intro x _
  split_ifs
  · exact le_refl _
  · exact μ.nonneg x

/-- Conditioning is performed only on positive-probability events. -/
noncomputable def condition (μ : FiniteLaw Ω) (E : Ω → Prop) (hE : 0 < μ.eventMass E) :
    FiniteLaw Ω := by
  classical
  refine ⟨fun x => (if E x then μ.mass x else 0) / μ.eventMass E, ?_, ?_⟩
  · intro x
    apply div_nonneg _ (le_of_lt hE)
    split_ifs
    · exact μ.nonneg x
    · rfl
  · rw [← sum_div]
    exact div_self (ne_of_gt hE)

@[simp] theorem condition_mass (μ : FiniteLaw Ω) (E : Ω → Prop)
    (hE : 0 < μ.eventMass E) (x : Ω) :
    (μ.condition E hE).mass x =
      (if E x then μ.mass x else 0) / μ.eventMass E := by
  classical
  rfl

theorem condition_eventMass (μ : FiniteLaw Ω) (E F : Ω → Prop)
    (hE : 0 < μ.eventMass E) :
    (μ.condition E hE).eventMass F = μ.eventMass (fun x => E x ∧ F x) / μ.eventMass E := by
  classical
  unfold eventMass
  rw [sum_div]
  apply sum_congr rfl
  intro x _
  simp only [condition_mass]
  by_cases he : E x <;> by_cases hf : F x <;> simp [he, hf, eventMass]

/-- Reweight a law by a nonnegative density of positive mean. -/
noncomputable def reweight (μ : FiniteLaw Ω) (w : Ω → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hZ : 0 < μ.expectation w) : FiniteLaw Ω := by
  refine ⟨fun x => μ.mass x * w x / μ.expectation w, ?_, ?_⟩
  · intro x
    exact div_nonneg (mul_nonneg (μ.nonneg x) (hw x)) (le_of_lt hZ)
  · rw [← sum_div]
    exact div_self (ne_of_gt hZ)

end FiniteLaw
end HardCoreActivityThreshold
