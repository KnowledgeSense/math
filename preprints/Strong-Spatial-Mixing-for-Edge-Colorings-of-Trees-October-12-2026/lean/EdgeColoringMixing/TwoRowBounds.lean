import EdgeColoringMixing.TwoRowIdentities
import EdgeColoringMixing.MatrixBounds

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EdgeColoringMixing.WeightedInjection
open Finset Matrix

variable {q : ℕ}

noncomputable def twoBeta (W : Fin 2 → Fin q → ℝ) (x : Fin 2 × Fin q) : ℝ :=
  W 0 x.2 * W 1 x.2 / partition W

/-- The collision sum is bounded by either row mass. -/
theorem collision_le_row (W : Fin 2 → Fin q → ℝ) {s : ℝ} (hW : RowSurplus W s) :
    (∑ c, W 0 c * W 1 c) ≤ ∑ c, W 0 c ∧
      (∑ c, W 0 c * W 1 c) ≤ ∑ c, W 1 c := by
  constructor
  · apply Finset.sum_le_sum
    intro c _
    simpa using mul_le_mul_of_nonneg_left (hW.le_one 1 c) (hW.nonneg 0 c)
  · apply Finset.sum_le_sum
    intro c _
    simpa using mul_le_mul_of_nonneg_right (hW.le_one 0 c) (hW.nonneg 1 c)

theorem surplus_mul_collision_le_partition (W : Fin 2 → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) :
    (s + 1) * (∑ c, W 0 c * W 1 c) ≤ partition W := by
  rw [partition_two]
  have hT := (collision_le_row W hW).1
  have hS := hW.row_mass 1
  norm_num at hS
  have hS0 : 0 ≤ ∑ c, W 0 c := Finset.sum_nonneg (fun c _ => hW.nonneg 0 c)
  have hT0 : 0 ≤ ∑ c, W 0 c * W 1 c :=
    Finset.sum_nonneg (fun c _ => mul_nonneg (hW.nonneg 0 c) (hW.nonneg 1 c))
  have hA := mul_le_mul_of_nonneg_left hS hS0
  have hB := mul_le_mul_of_nonneg_left hT (show 0 ≤ s + 2 by linarith [hW.positive])
  nlinarith

/-- The rank-one residual is small relative to either marginal, without excluding null cells. -/
theorem twoBeta_le_mean_div (W : Fin 2 → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (x : Fin 2 × Fin q) :
    twoBeta W x ≤ mean (law W hW.nonneg (partition_pos W hW)) x.1 x.2 / (s + 1) := by
  have ht : 0 < s + 1 := by linarith [hW.positive]
  have hZ := partition_pos W hW
  obtain ⟨i,c⟩ := x
  fin_cases i
  · change twoBeta W (0,c) ≤ mean (law W hW.nonneg (partition_pos W hW)) 0 c / (s + 1)
    rw [mean_two_zero W hW c]
    unfold twoBeta
    dsimp only
    apply (le_div_iff₀ ht).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff_of_pos_right hZ).mpr
    have hS := hW.row_mass 1
    norm_num at hS
    have hyt : W 1 c * (s + 1) ≤ (∑ b, W 1 b) - W 1 c := by
      have h := mul_le_mul_of_nonneg_right (hW.le_one 1 c) ht.le
      nlinarith [hW.le_one 1 c]
    nlinarith [mul_le_mul_of_nonneg_left hyt (hW.nonneg 0 c)]
  · change twoBeta W (1,c) ≤ mean (law W hW.nonneg (partition_pos W hW)) 1 c / (s + 1)
    rw [mean_two_one W hW c]
    unfold twoBeta
    dsimp only
    apply (le_div_iff₀ ht).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff_of_pos_right hZ).mpr
    have hS := hW.row_mass 0
    norm_num at hS
    have hxt : W 0 c * (s + 1) ≤ (∑ b, W 0 b) - W 0 c := by
      have h := mul_le_mul_of_nonneg_right (hW.le_one 0 c) ht.le
      nlinarith [hW.le_one 0 c]
    nlinarith [mul_le_mul_of_nonneg_left hxt (hW.nonneg 1 c)]

theorem twoBeta_nonneg (W : Fin 2 → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (x : Fin 2 × Fin q) : 0 ≤ twoBeta W x :=
  div_nonneg (mul_nonneg (hW.nonneg 0 x.2) (hW.nonneg 1 x.2)) (partition_pos W hW).le

/-- Exact weighted square estimate for the two-row rank-one residual. -/
theorem twoBeta_square_sum_bound (W : Fin 2 → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) :
    (∑ x : Fin 2 × Fin q, (twoBeta W x)^2 /
      mean (law W hW.nonneg (partition_pos W hW)) x.1 x.2) ≤ 2 / (s + 1)^2 := by
  let μ := law W hW.nonneg (partition_pos W hW)
  have ht : 0 < s + 1 := by linarith [hW.positive]
  have hZ := partition_pos W hW
  have hterm (x : Fin 2 × Fin q) : (twoBeta W x)^2 / mean μ x.1 x.2 ≤ twoBeta W x / (s + 1) := by
    have hp := mean_nonneg μ x.1 x.2
    have hβ := twoBeta_nonneg W hW x
    have hle := twoBeta_le_mean_div W hW x
    change twoBeta W x ≤ mean μ x.1 x.2 / (s + 1) at hle
    by_cases hx : mean μ x.1 x.2 = 0
    · have hzero : twoBeta W x = 0 := by rw [hx, zero_div] at hle; linarith
      simp [hx, hzero]
    · have hxpos := lt_of_le_of_ne hp (Ne.symm hx)
      apply (div_le_iff₀ hxpos).mpr
      have h := mul_le_mul_of_nonneg_left hle hβ
      convert h using 1 <;> ring
  calc
    _ ≤ ∑ x : Fin 2 × Fin q, twoBeta W x / (s + 1) := Finset.sum_le_sum (fun x _ => hterm x)
    _ = 2 * ((∑ c, W 0 c * W 1 c) / partition W) / (s + 1) := by
      simp only [twoBeta, Fintype.sum_prod_type, Fin.sum_univ_two, ← Finset.sum_div]
      ring
    _ ≤ 2 * (1 / (s + 1)) / (s + 1) := by
      apply div_le_div_of_nonneg_right _ ht.le
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply (div_le_div_iff₀ hZ ht).mpr
      simpa [mul_comm] using surplus_mul_collision_le_partition W hW
    _ = _ := by field_simp

/-- The two-row rank-one residual has the exact diagonal majorant used in the base case. -/
theorem twoBeta_rank_bound (W : Fin 2 → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) :
    ((2 / (s + 1)^2) • Matrix.diagonal
      (fun x : Fin 2 × Fin q => mean (law W hW.nonneg (partition_pos W hW)) x.1 x.2) -
      Matrix.vecMulVec (twoBeta W) (twoBeta W)).PosSemidef := by
  apply weighted_rank_one_bound
    (fun x : Fin 2 × Fin q => mean (law W hW.nonneg (partition_pos W hW)) x.1 x.2)
    (twoBeta W) (fun x => mean_nonneg _ x.1 x.2)
  · intro x hx
    have h := twoBeta_le_mean_div W hW x
    rw [hx, zero_div] at h
    exact le_antisymm h (twoBeta_nonneg W hW x)
  · positivity
  · exact twoBeta_square_sum_bound W hW

/-- A scalar form of the two-row same-color correction estimate. -/
theorem two_row_scalar_correction {t S T U x y : ℝ}
    (ht : 1 < t) (hS : t + 1 ≤ S) (hT : t + 1 ≤ T)
    (hU0 : 0 ≤ U) (hUS : U ≤ S) (_hUT : U ≤ T)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |(S - x) * (T - y) - (S * T - U)| ≤ (8 / t) * ((S - x) * (T - y)) := by
  have ht0 : 0 < t := by linarith
  have ha : t ≤ S - x := by linarith
  have hb : t ≤ T - y := by linarith
  have hab : 0 ≤ (S - x) * (T - y) := mul_nonneg (by linarith) (by linarith)
  have hxy : x * y ≤ T := by nlinarith
  have hSy : S * y ≤ S := by nlinarith
  have hTx : T * x ≤ T := by nlinarith
  have habs : |(S - x) * (T - y) - (S * T - U)| ≤ S + T := by
    apply abs_le.mpr
    constructor <;> nlinarith
  apply habs.trans
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ ht0).mpr
  have h₁ := mul_le_mul_of_nonneg_left hb (show 0 ≤ S - x by linarith)
  have h₂ := mul_le_mul_of_nonneg_left ha (show 0 ≤ T - y by linarith)
  nlinarith

end EdgeColoringMixing.WeightedInjection
