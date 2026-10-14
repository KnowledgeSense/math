import HardCoreActivityThreshold.VarianceBoosting

/-! A direct field-and-pinning interface for the fully proved finite revealing argument. -/
namespace HardCoreActivityThreshold
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Uniform scalar fields and occupied pinnings are sufficient for variance boosting. -/
theorem varianceTensorization_boost_fields (μ : FiniteLaw (Finset V))
    {θ C B : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hC : 0 ≤ C)
    (hcorr : ∀ (x : ℝ) (hx : 0 < x), x ≤ 1 → ∀ (r : Finset V)
      (hr : 0 < (applyField μ (fun _ => x) (fun _ => hx)).eventMass (agreesWith r r)),
      CorrelationBound ((applyField μ (fun _ => x) (fun _ => hx)).condition
        (agreesWith r r) hr) B)
    (hsmall : ∀ (r : Finset V)
      (hr : 0 < (applyField μ (fun _ => θ) (fun _ => hθ)).eventMass (agreesWith r r)),
      VarianceTensorization ((applyField μ (fun _ => θ) (fun _ => hθ)).condition
        (agreesWith r r) hr) C) :
    VarianceTensorization μ (C / θ^(Nat.ceil B)) := by
  apply varianceTensorization_boost μ (Nat.ceil B) hθ hθ1 hC
  · intro x hx hx1 r hr
    have hxpos : 0 < x := lt_trans hθ hx
    have hr' : 0 < ((positiveThinning x hxpos.le hx1.le).output μ).mass r := by
      rw [← thinningMass_eq_output μ hxpos.le hx1.le]
      exact hr
    rw [positiveThinning_posterior μ hxpos hx1 r hr']
    exact (hcorr x hxpos hx1.le r _).mono (Nat.le_ceil B)
  · intro r hr
    have hr' : 0 < ((positiveThinning θ hθ.le hθ1.le).output μ).mass r := by
      rw [← thinningMass_eq_output μ hθ.le hθ1.le]
      exact hr
    rw [positiveThinning_posterior μ hθ hθ1 r hr']
    exact hsmall r _

/-- A uniform lower-field tensorization bound gives an actual ambient-site heat-bath gap. -/
theorem heatBathGap_lower_of_field_bounds [Nonempty V] (μ : FiniteLaw (Finset V))
    {θ C B : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hC : 1 ≤ C)
    (hcorr : ∀ (x : ℝ) (hx : 0 < x), x ≤ 1 → ∀ (r : Finset V)
      (hr : 0 < (applyField μ (fun _ => x) (fun _ => hx)).eventMass (agreesWith r r)),
      CorrelationBound ((applyField μ (fun _ => x) (fun _ => hx)).condition
        (agreesWith r r) hr) B)
    (hsmall : ∀ (r : Finset V)
      (hr : 0 < (applyField μ (fun _ => θ) (fun _ => hθ)).eventMass (agreesWith r r)),
      VarianceTensorization ((applyField μ (fun _ => θ) (fun _ => hθ)).condition
        (agreesWith r r) hr) C) :
    (θ^(Nat.ceil B) / C) / Fintype.card V ≤ heatBathGap μ := by
  have hpow : 0 < θ^(Nat.ceil B) := pow_pos hθ _
  have hpow1 : θ^(Nat.ceil B) ≤ 1 := pow_le_one₀ hθ.le hθ1.le
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have htensor := varianceTensorization_boost_fields μ hθ hθ1 hCpos.le hcorr hsmall
  have hCT : 1 ≤ C / θ^(Nat.ceil B) := (one_le_div hpow).mpr (hpow1.trans hC)
  have hg := htensor.heatBathGap_lower hCT
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := V)
  convert hg using 1
  field_simp

end HardCoreActivityThreshold
