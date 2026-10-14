import EdgeColoringMixing.TwoRowBounds

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EdgeColoringMixing.WeightedInjection
open Finset Matrix

variable {q : ℕ}

/-- The exact same-color difference between the unnormalized and retained negative blocks. -/
theorem two_row_correction_bound (W : Fin 2 → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (c : Fin q) :
    let μ := law W hW.nonneg (partition_pos W hW)
    |mean μ 0 c * mean μ 1 c - twoBeta W (0,c)| ≤
      (8 / (s + 1)) * (mean μ 0 c * mean μ 1 c) := by
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  let S := ∑ b, W 0 b
  let T := ∑ b, W 1 b
  let U := ∑ b, W 0 b * W 1 b
  let A := (S - W 0 c) * (T - W 1 c)
  let a := W 0 c * W 1 c / (partition W)^2
  have hZ := partition_pos W hW
  have ha : 0 ≤ a := by unfold a; positivity [hW.nonneg 0 c, hW.nonneg 1 c]
  have hU0 : 0 ≤ U := Finset.sum_nonneg (fun b _ =>
    mul_nonneg (hW.nonneg 0 b) (hW.nonneg 1 b))
  have hST := collision_le_row W hW
  have hS : (s + 1) + 1 ≤ S := by
    have h := hW.row_mass 0
    norm_num at h
    dsimp [S]
    linarith
  have hT : (s + 1) + 1 ≤ T := by
    have h := hW.row_mass 1
    norm_num at h
    dsimp [T]
    linarith
  have hscalar := two_row_scalar_correction (show 1 < s + 1 by linarith [hW.positive])
    hS hT hU0 hST.1 hST.2 (hW.nonneg 0 c) (hW.le_one 0 c)
    (hW.nonneg 1 c) (hW.le_one 1 c)
  have hpart : partition W = S * T - U := partition_two W
  change |A - (S * T - U)| ≤ (8 / (s + 1)) * A at hscalar
  rw [← hpart] at hscalar
  have hprod : mean μ 0 c * mean μ 1 c = a * A := by
    rw [mean_two_zero W hW c, mean_two_one W hW c]
    dsimp [a, A, S, T]
    field_simp
  have hdiff : mean μ 0 c * mean μ 1 c - twoBeta W (0,c) = a * (A - partition W) := by
    rw [hprod]
    dsimp [a, twoBeta]
    field_simp
  change |mean μ 0 c * mean μ 1 c - twoBeta W (0,c)| ≤ _
  rw [hdiff, abs_mul, abs_of_nonneg ha, hprod]
  have h := mul_le_mul_of_nonneg_left hscalar ha
  exact h.trans_eq (by ring)

noncomputable def twoCorrection (W : Fin 2 → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) : Matrix (Fin 2 × Fin q) (Fin 2 × Fin q) ℝ :=
  let μ := law W hW.nonneg (partition_pos W hW)
  fun x y => if x.1 ≠ y.1 ∧ x.2 = y.2 then
    mean μ x.1 x.2 * mean μ y.1 y.2 - twoBeta W x else 0

theorem twoCorrection_hermitian (W : Fin 2 → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) : (twoCorrection W hW).IsHermitian := by
  ext x y
  change twoCorrection W hW y x = twoCorrection W hW x y
  simp only [twoCorrection]
  by_cases hrow : x.1 = y.1
  · simp [hrow]
  · by_cases hcolor : x.2 = y.2
    · simp [hrow, Ne.symm hrow, hcolor, twoBeta, mul_comm]
    · simp [hrow, Ne.symm hrow, hcolor, Ne.symm hcolor]

/-- Absolute row sums of the two-row correction are of order 1/t². -/
theorem twoCorrection_row_bound (W : Fin 2 → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (x : Fin 2 × Fin q) :
    (∑ y, |twoCorrection W hW x y|) ≤
      (8 / (s + 1)^2) * mean (law W hW.nonneg (partition_pos W hW)) x.1 x.2 := by
  let μ := law W hW.nonneg (partition_pos W hW)
  have ht : 0 < s + 1 := by linarith [hW.positive]
  have hp (i : Fin 2) (c : Fin q) : mean μ i c ≤ 1 / (s + 1) :=
    (marginal_le W hW i c).trans (div_le_div_of_nonneg_right (hW.le_one i c) ht.le)
  obtain ⟨i,c⟩ := x
  have h := two_row_correction_bound W hW c
  change |mean μ 0 c * mean μ 1 c - twoBeta W (0,c)| ≤
    (8 / (s + 1)) * (mean μ 0 c * mean μ 1 c) at h
  fin_cases i
  · change (∑ y, |twoCorrection W hW (0,c) y|) ≤ (8 / (s + 1)^2) * mean μ 0 c
    have heq : (∑ y, |twoCorrection W hW (0,c) y|) =
        |mean μ 0 c * mean μ 1 c - twoBeta W (0,c)| := by
      simp [twoCorrection, Fintype.sum_prod_type, Fin.sum_univ_two, twoBeta, μ, apply_ite abs]
    rw [heq]
    apply h.trans
    have h' := mul_le_mul_of_nonneg_left (hp 1 c)
      (show 0 ≤ (8 / (s + 1)) * mean μ 0 c by positivity [mean_nonneg μ 0 c])
    convert h' using 1
    · ring
    · field_simp
  · change (∑ y, |twoCorrection W hW (1,c) y|) ≤ (8 / (s + 1)^2) * mean μ 1 c
    have heq : (∑ y, |twoCorrection W hW (1,c) y|) =
        |mean μ 0 c * mean μ 1 c - twoBeta W (0,c)| := by
      simp [twoCorrection, Fintype.sum_prod_type, Fin.sum_univ_two, twoBeta, μ, mul_comm, apply_ite abs]
    rw [heq]
    apply h.trans
    have h' := mul_le_mul_of_nonneg_left (hp 0 c)
      (show 0 ≤ (8 / (s + 1)) * mean μ 1 c by positivity [mean_nonneg μ 1 c])
    convert h' using 1
    · ring
    · field_simp

/-- Matrix version of the retained-block correction estimate. -/
theorem twoCorrection_bound (W : Fin 2 → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) :
    ((8 / (s + 1)^2) • Matrix.diagonal
      (fun x : Fin 2 × Fin q => mean (law W hW.nonneg (partition_pos W hW)) x.1 x.2) -
        twoCorrection W hW).PosSemidef := by
  have h := diagonal_dominance_bound (twoCorrection W hW) (twoCorrection_hermitian W hW)
    (fun x => (8 / (s + 1)^2) * mean (law W hW.nonneg (partition_pos W hW)) x.1 x.2)
    (twoCorrection_row_bound W hW)
  convert h using 1
  ext x y
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply]
  split_ifs <;> ring

end EdgeColoringMixing.WeightedInjection
