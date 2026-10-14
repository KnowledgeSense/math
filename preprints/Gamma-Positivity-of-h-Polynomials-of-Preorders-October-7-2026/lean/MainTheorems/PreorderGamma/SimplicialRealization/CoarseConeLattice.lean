import MainTheorems.PreorderGamma.SimplicialRealization.CoarseRefinement
import MainTheorems.PreorderGamma.SimplicialRealization.ConeSaturation
import MainTheorems.PreorderGamma.SimplicialRealization.QuotientLattice
import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.BigOperators.Field

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators Pointwise

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

theorem integralCombination_quotientIntegerPoint (s : Finset (QuotientIndex E))
    (t : ℕ) (c : s → ℕ) (hc : (∑ v, c v) ≤ t) :
    QuotientIntegerPoint t (integralCombination s c) := by
  classical
  by_cases ht : t = 0
  · have hz : ∀ v : s, c v = 0 := by
      intro v
      have h := Finset.single_le_sum (fun i hi => Nat.zero_le (c i)) (Finset.mem_univ v)
      omega
    rw [ht, quotientIntegerPoint_zero_iff]
    simp [integralCombination, hz]
  · have htp : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero ht
    let w : Option s → ℝ
      | none => 1 - (∑ v : s, (c v : ℝ)) / t
      | some v => (c v : ℝ) / t
    let p : Option s → E → ℝ
      | none => 0
      | some v => v.val.val
    have hw : ∀ v, 0 ≤ w v := by
      intro v
      cases v with
      | none =>
        change 0 ≤ 1 - (∑ v : s, (c v : ℝ)) / t
        apply sub_nonneg.mpr
        apply (div_le_one₀ htp).mpr
        exact_mod_cast hc
      | some v => exact div_nonneg (Nat.cast_nonneg _) htp.le
    have hw1 : (∑ v, w v) = 1 := by
      rw [Fintype.sum_option]
      change 1 - (∑ v : s, (c v : ℝ)) / t +
        (∑ v : s, (c v : ℝ) / t) = 1
      rw [← Finset.sum_div]
      ring
    have hp : ∀ v, p v ∈ quotientVertices (E := E) := by
      intro v
      cases v with
      | none => exact (mem_quotientVertices _).mpr (Or.inl rfl)
      | some v => exact v.val.property
    have hsum : (∑ v, w v • p v) =
        (t : ℝ)⁻¹ • (fun i => (integralCombination s c i : ℝ)) := by
      rw [integralCombination_cast, Finset.smul_sum, Fintype.sum_option]
      simp only [w, p, smul_zero, zero_add, smul_smul]
      apply Finset.sum_congr rfl
      intro v hv
      rw [div_eq_mul_inv, mul_comm]
    have hmem : (∑ v, w v • p v) ∈ quotientPolytope (E := E) :=
      mem_convexHull_of_exists_fintype w p hw hw1 hp rfl
    apply Set.mem_smul_set.mpr
    refine ⟨∑ v, w v • p v, hmem, ?_⟩
    rw [hsum, smul_smul, mul_inv_cancel₀ (ne_of_gt htp), one_smul]

theorem coarseFunctional_le (l : (E → ℝ) →ₗ[ℝ] ℝ)
    (hb : ∀ v : QuotientIndex E, l v.val ≤ 1)
    {x : E → ℝ} (hx : x ∈ quotientPolytope (E := E)) : l x ≤ 1 := by
  apply convexHull_min ?_ (convex_halfSpace_le l.isLinear 1) hx
  intro v hv
  exact hb ⟨v, hv⟩

theorem coarseCombination_mass_le (s : Finset (QuotientIndex E))
    (hs : IsCoarseFace s) (t : ℕ) (c : s → ℕ)
    (hc : QuotientIntegerPoint t (integralCombination s c)) : (∑ v, c v) ≤ t := by
  obtain ⟨l, hb, ht⟩ := hs
  have hmass : l (fun i => (integralCombination s c i : ℝ)) = ∑ v : s, (c v : ℝ) := by
    rw [integralCombination_cast, map_sum]
    apply Finset.sum_congr rfl
    intro v hv
    rw [map_smul, ht v.val v.property, smul_eq_mul, mul_one]
  obtain ⟨x, hx, heq⟩ := Set.mem_smul_set.mp hc
  have hb' := coarseFunctional_le l hb hx
  have hle := mul_le_mul_of_nonneg_left hb' (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
  have hcast : (∑ v : s, (c v : ℝ)) ≤ t := by
    rw [← hmass, ← heq, map_smul, smul_eq_mul]
    simpa only [mul_one] using hle
  exact_mod_cast hcast

theorem coarse_integralCombination_iff (s : Finset (QuotientIndex E))
    (hs : IsCoarseFace s) (t : ℕ) (c : s → ℕ) :
    QuotientIntegerPoint t (integralCombination s c) ↔ (∑ v, c v) ≤ t :=
  ⟨coarseCombination_mass_le s hs t c, integralCombination_quotientIntegerPoint s t c⟩

end ResearchMain.PreorderGamma.SimplicialRealization
