import HardCoreActivityThreshold.HeatBath
import HardCoreActivityThreshold.FiniteVariance

/-! The heat-bath gap is unchanged when zero-probability configurations are removed.
The resulting chain has precisely the actual probabilistic support as its state space. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable

section FiniteSums
variable {Ω : Type*} [Fintype Ω]

theorem sum_subtype_of_zero (p : Ω → Prop) (f : Ω → ℝ) (hz : ∀ x, ¬ p x → f x = 0) :
    (∑ x, f x) = ∑ x : {x // p x}, f x.val := by
  rw [← Finset.sum_subtype (p := p) (univ.filter p) (fun _ => by simp) f, sum_filter]
  apply sum_congr rfl
  intro x _
  by_cases hx : p x
  · simp [hx]
  · simp [hx, hz x hx]

end FiniteSums

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

def Support (μ : FiniteLaw Ω) := {x // 0 < μ.mass x}
noncomputable instance supportFintype (μ : FiniteLaw Ω) : Fintype μ.Support := inferInstanceAs (Fintype {x // 0 < μ.mass x})

noncomputable def supportLaw (μ : FiniteLaw Ω) : FiniteLaw μ.Support where
  mass x := μ.mass x.val
  nonneg x := μ.nonneg x.val
  sum_one := by
    rw [← μ.sum_one]
    symm
    exact sum_subtype_of_zero _ _ (fun x hx => le_antisymm (le_of_not_gt hx) (μ.nonneg x))

theorem supportLaw_expectation (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.supportLaw.expectation (fun x => f x.val) = μ.expectation f := by
  symm
  apply sum_subtype_of_zero
  intro x hx
  have hm : μ.mass x = 0 := le_antisymm (le_of_not_gt hx) (μ.nonneg x)
  simp [hm]

theorem supportLaw_variance (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.supportLaw.variance (fun x => f x.val) = μ.variance f := by
  unfold variance
  rw [supportLaw_expectation]
  exact μ.supportLaw_expectation (fun x => (f x - μ.expectation f)^2)

noncomputable def extendSupport (μ : FiniteLaw Ω) (f : μ.Support → ℝ) (x : Ω) : ℝ :=
  if hx : 0 < μ.mass x then f ⟨x, hx⟩ else 0

@[simp] theorem extendSupport_apply (μ : FiniteLaw Ω) (f : μ.Support → ℝ) (x : μ.Support) :
    μ.extendSupport f x.val = f x := by
  dsimp only [extendSupport]
  rw [dite_eq_left x.property]
  apply congrArg f
  exact Subtype.ext rfl

end FiniteLaw

/-- A stochastic reversible transition matrix on a finite state space. -/
structure FiniteReversibleChain (Ω : Type*) [Fintype Ω] where
  law : FiniteLaw Ω
  transition : Ω → Ω → ℝ
  nonneg : ∀ x y, 0 ≤ transition x y
  row_sum : ∀ x, ∑ y, transition x y = 1
  reversible : ∀ x y, law.mass x * transition x y = law.mass y * transition y x

namespace FiniteReversibleChain
variable {Ω : Type*} [Fintype Ω]

noncomputable def dirichlet (P : FiniteReversibleChain Ω) (f : Ω → ℝ) : ℝ :=
  (∑ x, ∑ y, P.law.mass x * P.transition x y * (f x-f y)^2)/2

/-- The optimal Poincaré spectral gap of this finite reversible Markov chain. -/
noncomputable def spectralGap (P : FiniteReversibleChain Ω) : ℝ :=
  if ∃ f : Ω → ℝ, 0 < P.law.variance f then
    sInf {r : ℝ | ∃ f : Ω → ℝ, 0 < P.law.variance f ∧ r = P.dirichlet f / P.law.variance f}
  else 1

end FiniteReversibleChain

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem heatBathKernel_support_closed (μ : FiniteLaw (Finset V)) (s : μ.Support) (t : Finset V)
    (ht : ¬ 0 < μ.mass t) : heatBathKernel μ s.val t = 0 := by
  have hz : μ.mass t = 0 := le_antisymm (le_of_not_gt ht) (μ.nonneg t)
  have he := heatBathKernel_reversible μ s.val t
  rw [hz, zero_mul] at he
  exact (mul_eq_zero.mp he).resolve_left s.property.ne'

/-- The actual heat-bath chain, restricted to configurations of positive probability. -/
noncomputable def supportHeatBath [Nonempty V] (μ : FiniteLaw (Finset V)) :
    FiniteReversibleChain μ.Support where
  law := μ.supportLaw
  transition s t := heatBathKernel μ s.val t.val
  nonneg s t := heatBathKernel_nonneg μ s.val t.val
  row_sum s := by
    rw [← heatBathKernel_row_sum μ s.val]
    symm
    exact sum_subtype_of_zero _ _ (heatBathKernel_support_closed μ s)
  reversible s t := heatBathKernel_reversible μ s.val t.val

theorem supportHeatBath_dirichlet [Nonempty V] (μ : FiniteLaw (Finset V)) (f : Finset V → ℝ) :
    (supportHeatBath μ).dirichlet (fun s => f s.val) = dirichletForm μ f := by
  unfold FiniteReversibleChain.dirichlet dirichletForm supportHeatBath FiniteLaw.supportLaw
  congr 1
  symm
  have ht (s : Finset V) :
      (∑ t, μ.mass s * heatBathKernel μ s t * (f s-f t)^2) =
        ∑ t : μ.Support, μ.mass s * heatBathKernel μ s t.val * (f s-f t.val)^2 := by
    apply sum_subtype_of_zero
    intro t ht
    have hz : μ.mass t = 0 := le_antisymm (le_of_not_gt ht) (μ.nonneg t)
    rw [heatBathKernel_reversible, hz, zero_mul, zero_mul]
  simp_rw [ht]
  apply sum_subtype_of_zero
  intro s hs
  have hz : μ.mass s = 0 := le_antisymm (le_of_not_gt hs) (μ.nonneg s)
  simp [hz]

/-- The exact gap used in the theorem is the gap of the stochastic chain on its true support. -/
theorem heatBathGap_eq_support_spectralGap [Nonempty V] (μ : FiniteLaw (Finset V)) :
    heatBathGap μ = (supportHeatBath μ).spectralGap := by
  have hv (f : Finset V → ℝ) :
      (supportHeatBath μ).law.variance (fun s => f s.val) = μ.variance f := μ.supportLaw_variance f
  have hve (f : μ.Support → ℝ) :
      μ.variance (μ.extendSupport f) = (supportHeatBath μ).law.variance f := by
    rw [← hv]
    simp only [FiniteLaw.extendSupport_apply]
  have hde (f : μ.Support → ℝ) : dirichletForm μ (μ.extendSupport f) = (supportHeatBath μ).dirichlet f := by
    rw [← supportHeatBath_dirichlet]
    simp only [FiniteLaw.extendSupport_apply]
  have hex : (∃ f : Finset V → ℝ, 0 < μ.variance f) ↔
      ∃ f : μ.Support → ℝ, 0 < (supportHeatBath μ).law.variance f := by
    constructor
    · rintro ⟨f, hf⟩
      exact ⟨fun s => f s.val, by rw [hv]; exact hf⟩
    · rintro ⟨f, hf⟩
      exact ⟨μ.extendSupport f, by rw [hve]; exact hf⟩
  unfold heatBathGap FiniteReversibleChain.spectralGap
  simp only [hex]
  split_ifs
  · congr 1
    ext r
    constructor
    · rintro ⟨f, hf, hr⟩
      exact ⟨fun s => f s.val, by rw [hv]; exact hf,
        by rw [supportHeatBath_dirichlet, hv]; exact hr⟩
    · rintro ⟨f, hf, hr⟩
      exact ⟨μ.extendSupport f, by rw [hve]; exact hf,
        by rw [hde, hve]; exact hr⟩
  · rfl

end HardCoreActivityThreshold
