import RandomWalkSearch.Probability
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp

/-! # Universal expected-cost restoration lower bound -/

namespace RandomWalkSearch.Cycle
open MeasureTheory
open scoped ENNReal BigOperators

variable {k : ℕ} [NeZero (N k)]
variable {Ω : Type*} [MeasurableSpace Ω]

theorem Randomized.averageSuccess_ge_half (A : Randomized k Ω) (μ : Measure Ω)
    (hs : ∀ a, (1 : ℝ≥0∞) / 2 ≤ A.success μ a) :
    (1 : ℝ≥0∞) / 2 ≤ A.averageSuccess μ := by
  have hN : (N k : ℝ≥0∞) ≠ 0 := by exact_mod_cast NeZero.ne (N k)
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Vertex k))) (fun a _ => hs a)
  have hd := mul_le_mul hh (le_rfl : (N k : ℝ≥0∞)⁻¹ ≤ (N k : ℝ≥0∞)⁻¹)
  simpa [Randomized.averageSuccess, Finset.sum_const, nsmul_eq_mul,
    ZMod.card, mul_comm (N k : ℝ≥0∞), ← div_eq_mul_inv,
    ENNReal.mul_div_cancel_right hN (ENNReal.natCast_ne_top _)] using hd

omit [NeZero (N k)] in
/-- The purely arithmetic final step, with the budgets still representing the
actual truncation caps. -/
theorem restoration_budget_arithmetic (b : ℕ) (hb : 1 ≤ b)
    (hk : 16 * (b + 1) ≤ k) (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (T Q : ℕ) (hT : 16 * a + 1 ≤ T) (hT' : (T : ℝ) ≤ 16 * a + 2)
    (hQ : 16 * c + 1 ≤ Q) (hQ' : (Q : ℝ) ≤ 16 * c + 2)
    (h : (1 : ℝ) / 2 ≤
      (((Q + 1) * k ^ 6 + (b + 1) * D k + T : ℕ) : ℝ) / N k + a / T + c / Q) :
    (1 : ℝ) / 64 ≤ c / L k + a / N k := by
  have hk32 : (32 : ℝ) ≤ k := by exact_mod_cast (by omega : 32 ≤ k)
  have hkpos : (0 : ℝ) < k := by linarith
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hTp : (0 : ℝ) < T := by linarith
  have hQp : (0 : ℝ) < Q := by linarith
  have hau : a / T ≤ 1 / 16 := (div_le_iff₀ hTp).mpr (by linarith)
  have hcu : c / Q ≤ 1 / 16 := (div_le_iff₀ hQp).mpr (by linarith)
  have heq : (((Q + 1) * k ^ 6 + (b + 1) * D k + T : ℕ) : ℝ) / N k =
      ((Q : ℝ) + 1) / (k : ℝ) ^ 2 + ((b : ℝ) + 1) / k + T / (k : ℝ) ^ 8 := by
    simp only [N, D, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one]
    field_simp
  rw [heq] at h
  have hQu : ((Q : ℝ) + 1) / (k : ℝ)^2 ≤ (16*c+3) / (k : ℝ)^2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hTu : (T : ℝ) / (k : ℝ)^8 ≤ (16*a+2) / (k : ℝ)^8 :=
    div_le_div_of_nonneg_right hT' (by positivity)
  have hbsmall : ((b : ℝ)+1) / k ≤ 1/16 := by
    apply (div_le_iff₀ hkpos).mpr
    have hkr : 16 * ((b : ℝ)+1) ≤ k := by exact_mod_cast hk
    linarith
  have hk2 : (96 : ℝ) ≤ (k : ℝ)^2 := by nlinarith
  have hk8 : (64 : ℝ) ≤ (k : ℝ)^8 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 32) hk32 8]
  have hsmall2 : 3 / (k : ℝ)^2 ≤ 1/32 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hsmall8 : 2 / (k : ℝ)^8 ≤ 1/32 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hsplitQ : (16*c+3) / (k : ℝ)^2 = 16*(c/(k:ℝ)^2)+3/(k:ℝ)^2 := by ring
  have hsplitT : (16*a+2) / (k : ℝ)^8 = 16*(a/(k:ℝ)^8)+2/(k:ℝ)^8 := by ring
  simp only [L, N, Nat.cast_pow]
  rw [hsplitQ] at hQu
  rw [hsplitT] at hTu
  linarith

/-- The paper's free-restoration theorem for arbitrary adaptive randomized
policies, genuine possibly divergent executions, and extended expected costs. -/
theorem Randomized.restoration_lower_bound (A : Randomized k Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hobs : A.Observable)
    (b : ℕ) (hb : 1 ≤ b) (hk : 16 * (b + 1) ≤ k)
    (hA : A.Restoration b) (hs : ∀ a, (1 : ℝ≥0∞) / 2 ≤ A.success μ a) :
    (1 : ℝ≥0∞) / 64 ≤ A.averageChecks μ / L k + A.averageUpdates μ / N k := by
  have hkpos : 0 < k := by omega
  have hN : (N k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (N_pos hkpos).ne'
  have hL : (L k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (L_pos hkpos).ne'
  by_cases ha : A.averageUpdates μ = ∞
  · simp [ha, ENNReal.top_div]
  by_cases hc : A.averageChecks μ = ∞
  · simp [hc, ENNReal.top_div]
  let a := (A.averageUpdates μ).toReal
  let c := (A.averageChecks μ).toReal
  let T : ℕ := ⌈16*a+1⌉₊
  let Q : ℕ := ⌈16*c+1⌉₊
  have han : 0 ≤ a := ENNReal.toReal_nonneg
  have hcn : 0 ≤ c := ENNReal.toReal_nonneg
  have hT : 16*a+1 ≤ (T : ℝ) := Nat.le_ceil _
  have hQ : 16*c+1 ≤ (Q : ℝ) := Nat.le_ceil _
  have hT' : (T : ℝ) ≤ 16*a+2 := by have := Nat.ceil_lt_add_one (show 0 ≤ 16*a+1 by linarith); dsimp [T]; linarith
  have hQ' : (Q : ℝ) ≤ 16*c+2 := by have := Nat.ceil_lt_add_one (show 0 ≤ 16*c+1 by linarith); dsimp [Q]; linarith
  have hTp : 0 < T := by exact_mod_cast (show (0:ℝ) < T by linarith)
  have hQp : 0 < Q := by exact_mod_cast (show (0:ℝ) < Q by linarith)
  have hT0 : (T : ℝ≥0∞) ≠ 0 := by exact_mod_cast hTp.ne'
  have hQ0 : (Q : ℝ≥0∞) ≠ 0 := by exact_mod_cast hQp.ne'
  have hbud := (A.averageSuccess_ge_half μ hs).trans
    (A.expected_restoration_budget μ hobs b T Q hA hTp hQp)
  have hHfin : ((((Q + 1) * k ^ 6 + (b + 1) * D k + T : ℕ) : ℝ≥0∞) / N k) ≠ ∞ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hN
  have hUfin := ENNReal.div_ne_top ha hT0
  have hCfin := ENNReal.div_ne_top hc hQ0
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨hHfin, hUfin⟩, hCfin⟩) hbud
  simp only [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hHfin, hUfin⟩) hCfin,
    ENNReal.toReal_add hHfin hUfin, ENNReal.toReal_div, ENNReal.toReal_natCast] at hreal
  have harith := restoration_budget_arithmetic b hb hk a c han hcn T Q hT hT' hQ hQ' hreal
  apply (ENNReal.toReal_le_toReal (by norm_num)
    (ENNReal.add_ne_top.mpr ⟨ENNReal.div_ne_top hc hL, ENNReal.div_ne_top ha hN⟩)).mp
  simpa [a, c, ENNReal.toReal_add (ENNReal.div_ne_top hc hL) (ENNReal.div_ne_top ha hN),
    ENNReal.toReal_div, ENNReal.toReal_natCast] using harith

end RandomWalkSearch.Cycle
