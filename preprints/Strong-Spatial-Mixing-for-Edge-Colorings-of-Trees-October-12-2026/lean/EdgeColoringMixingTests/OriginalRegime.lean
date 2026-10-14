import EdgeColoringMixing.ColumnCovariance

set_option autoImplicit false
namespace EdgeColoringMixing.Tests
open WeightedInjection

/-- Concrete positive weighted injections exist in the exact original asymptotic
regime, and the complete column conclusion is obtained on those actual laws. -/
theorem original_regime_nonvacuous (ε : ℝ) (hε : 0 < ε) :
    ∃ Δ q : ℕ, 3 ≤ Δ ∧ ((3 + Real.sqrt 5) / 2 + ε) * (Δ : ℝ) ≤ q ∧
      ∃ hW : RowSurplus (fun (_ : Fin 2) (_ : Fin q) => (1 : ℝ))
        ((q : ℝ) - 2 * (Δ : ℝ) + 2),
        let s := (q : ℝ) - 2 * (Δ : ℝ) + 2
        let μ := law (fun (_ : Fin 2) (_ : Fin q) => (1 : ℝ)) hW.nonneg
          (partition_pos _ hW)
        let L := 22 + 8 * ((q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2)
        let δ := (columnError L (s + 1) Δ + 1 / (s + 1)) * (((Δ : ℝ) + s) / s)
        ((1 + δ) • columnBlock μ - covariance μ).PosSemidef := by
  obtain ⟨N, hN⟩ := release_parameter_choice hε
  let Δ := max N 3
  let q := Nat.ceil (((3 + Real.sqrt 5) / 2 + ε) * (Δ : ℝ))
  have hq : ((3 + Real.sqrt 5) / 2 + ε) * (Δ : ℝ) ≤ q := Nat.le_ceil _
  obtain ⟨hΔ, hs, _, hfirst, hsecond, hthird, _, _, _⟩ := hN Δ q (le_max_left _ _) hq
  have hW : RowSurplus (fun (_ : Fin 2) (_ : Fin q) => (1 : ℝ))
      ((q : ℝ) - 2 * (Δ : ℝ) + 2) := by
    refine ⟨hs, fun _ _ => zero_le_one, fun _ _ => le_rfl, ?_⟩
    intro i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hΔr : (3 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    norm_num
    linarith
  refine ⟨Δ, q, hΔ, hq, hW, ?_⟩
  exact column_covariance_bound _ hW Δ (by omega) (by omega) hfirst hsecond hthird

end EdgeColoringMixing.Tests
