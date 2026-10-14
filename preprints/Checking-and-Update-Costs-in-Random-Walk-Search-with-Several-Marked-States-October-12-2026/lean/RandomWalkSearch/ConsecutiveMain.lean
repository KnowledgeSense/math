import RandomWalkSearch.ConsecutiveProbability
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! # Universal expected-cost consecutive lower bound -/
namespace RandomWalkSearch.Cycle
open MeasureTheory
open scoped ENNReal BigOperators

variable {k : ℕ}

/-- The square-root arithmetic retains the constants in the stated theorem. -/
theorem consecutive_budget_arithmetic (b : ℕ) (hb : 1 ≤ b)
    (hk : 16 * (b + 1) ≤ k) (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (T Q : ℕ) (hT : 16 * a + 1 ≤ T) (hT' : (T : ℝ) ≤ 16 * a + 2)
    (hQ : 16 * c + 1 ≤ Q) (hQ' : (Q : ℝ) ≤ 16 * c + 2)
    (h : (1 : ℝ) / 2 ≤
      (((Q + 1) * k ^ 6 + (b + 1) * D k : ℕ) : ℝ) / N k +
        (b : ℝ) * (2 * Real.sqrt (2 * (T : ℝ))) / N k + a / T + c / Q) :
    (1 : ℝ) / (64 * b) ≤ c / L k + Real.sqrt a / N k := by
  have hk32 : (32 : ℝ) ≤ k := by exact_mod_cast (by omega : 32 ≤ k)
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hkpos : (0 : ℝ) < k := by linarith
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hkr : 16 * ((b : ℝ)+1) ≤ k := by exact_mod_cast hk
  have hTp : (0 : ℝ) < T := by linarith
  have hQp : (0 : ℝ) < Q := by linarith
  have hau : a / T ≤ 1 / 16 := (div_le_iff₀ hTp).mpr (by linarith)
  have hcu : c / Q ≤ 1 / 16 := (div_le_iff₀ hQp).mpr (by linarith)
  have heq : (((Q + 1) * k ^ 6 + (b + 1) * D k : ℕ) : ℝ) / N k =
      ((Q : ℝ)+1)/(k : ℝ)^2 + ((b : ℝ)+1)/k := by
    simp only [N, D, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one]
    field_simp
  rw [heq] at h
  have hQu : ((Q : ℝ)+1)/(k:ℝ)^2 ≤ (16*c+3)/(k:ℝ)^2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hsqrta := Real.sq_sqrt ha
  have hsqrtt := Real.sq_sqrt (show (0 : ℝ) ≤ 2*T by positivity)
  have hsa := Real.sqrt_nonneg a
  have hst := Real.sqrt_nonneg (2*(T:ℝ))
  have hsqrt : Real.sqrt (2*(T:ℝ)) ≤ 8*Real.sqrt a+2 := by nlinarith
  have hru : (b:ℝ)*(2*Real.sqrt (2*(T:ℝ)))/(k:ℝ)^8 ≤
      (16*(b:ℝ)*Real.sqrt a+4*b)/(k:ℝ)^8 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hbsmall : ((b:ℝ)+1)/k ≤ 1/16 := (div_le_iff₀ hkpos).mpr (by linarith)
  have hk2 : (96:ℝ) ≤ (k:ℝ)^2 := by nlinarith
  have hk8 : (128:ℝ)*b ≤ (k:ℝ)^8 := by
    have hp := pow_le_pow_right₀ (show (1:ℝ) ≤ k by linarith) (by decide : 2 ≤ 8)
    nlinarith
  have hsmall2 : 3/(k:ℝ)^2 ≤ 1/32 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hsmall8 : (4:ℝ)*b/(k:ℝ)^8 ≤ 1/32 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hsplitQ : (16*c+3)/(k:ℝ)^2 = 16*(c/(k:ℝ)^2)+3/(k:ℝ)^2 := by ring
  have hsplitR : (16*(b:ℝ)*Real.sqrt a+4*b)/(k:ℝ)^8 =
      16*b*(Real.sqrt a/(k:ℝ)^8)+4*b/(k:ℝ)^8 := by ring
  rw [hsplitQ] at hQu
  rw [hsplitR] at hru
  simp only [N, Nat.cast_pow] at h
  have hcn : 0 ≤ c/(k:ℝ)^2 := by positivity
  have hweight : 16*(c/(k:ℝ)^2) ≤ 16*b*(c/(k:ℝ)^2) := by nlinarith
  simp only [L, N, Nat.cast_pow]
  apply (div_le_iff₀ (show (0:ℝ)<64*b by positivity)).mpr
  nlinarith

variable [NeZero (N k)] {Ω : Type*} [MeasurableSpace Ω]

/-- The paper's consecutive theorem, with square root expressed as extended
nonnegative real power and with all randomness and stopping semantics explicit. -/
theorem Randomized.consecutive_lower_bound (A : Randomized k Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hobs : A.Observable) (hlaw : A.LazyLaw μ)
    (b : ℕ) (hb : 1 ≤ b) (hk : 16 * (b + 1) ≤ k)
    (hA : A.Consecutive b) (hs : ∀ a, (1 : ℝ≥0∞) / 2 ≤ A.success μ a) :
    (1 : ℝ≥0∞) / (64 * b) ≤ A.averageChecks μ / L k +
      A.averageUpdates μ ^ (1 / (2 : ℝ)) / N k := by
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
    (A.expected_consecutive_budget μ hobs hlaw b T Q hA hTp hQp)
  have hHfin : ((((Q + 1) * k ^ 6 + (b + 1) * D k : ℕ) : ℝ≥0∞) / N k) ≠ ∞ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hN
  have hRfin : (b * ENNReal.ofReal (2 * Real.sqrt (2 * (T:ℝ))) / (N k : ℝ≥0∞)) ≠ ∞ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top) hN
  have hUfin := ENNReal.div_ne_top ha hT0
  have hCfin := ENNReal.div_ne_top hc hQ0
  have hHRfin := ENNReal.add_ne_top.mpr ⟨hHfin,hRfin⟩
  have hHRUfin := ENNReal.add_ne_top.mpr ⟨hHRfin,hUfin⟩
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hHRUfin,hCfin⟩) hbud
  simp only [ENNReal.toReal_add hHRUfin hCfin, ENNReal.toReal_add hHRfin hUfin,
    ENNReal.toReal_add hHfin hRfin, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*Real.sqrt (2*(T:ℝ)))] at hreal
  have harith := consecutive_budget_arithmetic b hb hk a c han hcn T Q hT hT' hQ hQ' hreal
  have hsfin := ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0:ℝ)≤1/2) ha
  apply (ENNReal.toReal_le_toReal
    (ENNReal.div_ne_top (by norm_num) (by positivity))
    (ENNReal.add_ne_top.mpr ⟨ENNReal.div_ne_top hc hL, ENNReal.div_ne_top hsfin hN⟩)).mp
  rw [ENNReal.toReal_add (ENNReal.div_ne_top hc hL) (ENNReal.div_ne_top hsfin hN)]
  simp only [Real.sqrt_eq_rpow] at harith
  simpa [a, c, ENNReal.toReal_div, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow] using harith

end RandomWalkSearch.Cycle
