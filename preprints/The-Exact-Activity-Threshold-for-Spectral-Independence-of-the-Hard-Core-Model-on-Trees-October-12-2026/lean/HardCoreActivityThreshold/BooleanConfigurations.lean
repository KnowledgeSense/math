import HardCoreActivityThreshold.RestrictedLaw

/-! Boolean configurations and vertex subsets are linked by an explicit probability-preserving bijection. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable

namespace FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
noncomputable def mapEquiv (μ : FiniteLaw Ω) (e : Ω ≃ Ξ) : FiniteLaw Ξ where
  mass y := μ.mass (e.symm y)
  nonneg y := μ.nonneg _
  sum_one := by rw [e.symm.sum_comp μ.mass, μ.sum_one]

theorem mapEquiv_expectation (μ : FiniteLaw Ω) (e : Ω ≃ Ξ) (f : Ξ → ℝ) :
    (μ.mapEquiv e).expectation f = μ.expectation (fun x => f (e x)) := by
  unfold expectation mapEquiv
  apply Fintype.sum_equiv e.symm
  intro y
  simp
end FiniteLaw

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def configurationEquiv : Finset V ≃ (V → Bool) where
  toFun s v := decide (v ∈ s)
  invFun x := univ.filter (fun v => x v = true)
  left_inv s := by ext v; simp
  right_inv x := by funext v; simp

def BooleanIndependent (G : SimpleGraph V) (x : V → Bool) : Prop :=
  ∀ u, x u = true → ∀ v, x v = true → ¬ G.Adj u v

noncomputable def booleanWeight (G : SimpleGraph V) (activity : V → ℝ) (x : V → Bool) : ℝ :=
  if BooleanIndependent G x then ∏ v, if x v then activity v else 1 else 0

theorem booleanWeight_eq (G : SimpleGraph V) (activity : V → ℝ) (x : V → Bool) :
    booleanWeight G activity x = configurationWeight G activity (configurationEquiv.symm x) := by
  have hind : Independent G (configurationEquiv.symm x) ↔ BooleanIndependent G x := by
    simp only [configurationEquiv, Equiv.coe_fn_symm_mk, mem_filter, mem_univ, true_and,
      Independent, BooleanIndependent]
  unfold booleanWeight configurationWeight
  rw [hind]
  split_ifs
  · change (∏ v, if x v = true then activity v else 1) = ∏ v ∈ univ.filter (fun v => x v = true), activity v
    exact (prod_filter _ _).symm
  · rfl

noncomputable def booleanHardCoreLaw (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) : FiniteLaw (V → Bool) :=
  (hardCoreLaw G activity ha).mapEquiv configurationEquiv

theorem booleanHardCoreLaw_mass (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (x : V → Bool) :
    (booleanHardCoreLaw G activity ha).mass x = booleanWeight G activity x / partitionFunction G activity := by
  rw [booleanWeight_eq]
  rfl

noncomputable def booleanWithinLaw (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (allowed : Finset V) : FiniteLaw (V → Bool) :=
  (hardCoreWithin G activity ha allowed).mapEquiv configurationEquiv

theorem booleanWithinLaw_mass (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (allowed : Finset V) (x : V → Bool) :
    (booleanWithinLaw G activity ha allowed).mass x =
      (if ∀ v, x v = true → v ∈ allowed then booleanWeight G activity x else 0) /
        partitionWithin G activity allowed := by
  change withinWeight G activity allowed (configurationEquiv.symm x) / _ = _
  unfold withinWeight
  rw [← booleanWeight_eq]
  have he : configurationEquiv.symm x ⊆ allowed ↔ ∀ v, x v = true → v ∈ allowed := by
    simp [configurationEquiv, subset_iff]
  simp only [he]

end HardCoreActivityThreshold
