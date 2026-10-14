import MainTheorems.PreorderGamma.SimplicialRealization.IntegerConfiguration
import MainTheorems.PreorderGamma.SimplicialRealization.PositiveCompositions
import MainTheorems.PreorderGamma.SimplicialRealization.BoundaryDimension

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

noncomputable def integralCombination (s : Finset (QuotientIndex E))
    (c : s → ℕ) : E → ℤ :=
  ∑ v : s, (c v : ℤ) • integerQuotientVertex v.val

theorem integralCombination_cast (s : Finset (QuotientIndex E)) (c : s → ℕ) :
    (fun i => (integralCombination s c i : ℝ)) = ∑ v : s, (c v : ℝ) • v.val.val := by
  funext i
  simp [integralCombination, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem integralCombination_injective (s : Finset (QuotientIndex E))
    (hs : LinearIndependent ℝ (fun v : s => v.val.val)) :
    Function.Injective (integralCombination s) := by
  intro c d h
  have hcast := congrArg (fun z : E → ℤ => fun i => (z i : ℝ)) h
  rw [integralCombination_cast, integralCombination_cast] at hcast
  have hzero : (∑ v : s, ((c v : ℝ) - (d v : ℝ)) • v.val.val) = 0 := by
    simpa only [sub_smul, Finset.sum_sub_distrib] using sub_eq_zero.mpr hcast
  have hc := (Fintype.linearIndependent_iff.mp hs) _ hzero
  funext v
  have heq : (c v : ℝ) = (d v : ℝ) := sub_eq_zero.mp (hc v)
  exact_mod_cast heq

abbrev IntegralConePoints (s : Finset (QuotientIndex E)) (t : ℕ) :=
  {z : E → ℤ // ∃ c : PositiveCoefficients s t, integralCombination s c.val = z}

noncomputable def integralConeEquiv (s : Finset (QuotientIndex E)) (t : ℕ)
    (hs : LinearIndependent ℝ (fun v : s => v.val.val)) :
    PositiveCoefficients s t ≃ IntegralConePoints s t where
  toFun c := ⟨integralCombination s c.val, c, rfl⟩
  invFun z := Classical.choose z.property
  left_inv := by
    intro c
    apply Subtype.ext
    apply integralCombination_injective s hs
    exact Classical.choose_spec (show ∃ d : PositiveCoefficients s t,
      integralCombination s d.val = integralCombination s c.val from ⟨c, rfl⟩)
  right_inv := by
    intro z
    apply Subtype.ext
    exact Classical.choose_spec z.property

theorem integralConePoints_count (s : Finset (QuotientIndex E)) (t : ℕ)
    (hs : LinearIndependent ℝ (fun v : s => v.val.val)) :
    Nat.card (IntegralConePoints s t) = Nat.choose t s.card := by
  rw [← Nat.card_congr (integralConeEquiv s t hs), positiveCoefficients_count]
  simp

theorem boundary_integral_cone_count (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (hboundary : HasSimplicialBoundary height)
    (s : Finset (QuotientIndex E)) (hs : s ∈ boundaryVertexFaces height) (t : ℕ) :
    Nat.card (IntegralConePoints s t) = Nat.choose t s.card :=
  integralConePoints_count s t (boundary_face_original_linearIndependent height hheight hboundary s hs)

end ResearchMain.PreorderGamma.SimplicialRealization
