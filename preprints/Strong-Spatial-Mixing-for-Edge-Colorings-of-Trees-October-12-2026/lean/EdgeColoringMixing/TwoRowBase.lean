import EdgeColoringMixing.TwoRowCorrection
import EdgeColoringMixing.AlternatingInfluence

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EdgeColoringMixing
open Finset Matrix

/-- The two-row cross term has a rank-one majorant; no square-root division is needed. -/
theorem two_outer_bound {ι : Type*} [Fintype ι] (X Y : ι → ℝ) {S T Z : ℝ}
    (hS : 0 < S) (hT : 0 < T) (hZ : 0 < Z) (hZT : Z ≤ S * T) :
    ((1 / 2 : ℝ) • Matrix.vecMulVec
      (fun i => (T * X i + S * Y i) / Z) (fun i => (T * X i + S * Y i) / Z) -
      (1 / Z) • (Matrix.vecMulVec X Y + Matrix.vecMulVec Y X)).PosSemidef := by
  let u := fun i => T * X i - S * Y i
  let v := fun i => T * X i + S * Y i
  have hu : (Matrix.vecMulVec u u).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star u
  have hv : (Matrix.vecMulVec v v).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star v
  have h₁ := hu.smul (show 0 ≤ 1 / (2 * Z * S * T) by positivity)
  have h₂ := hv.smul (show 0 ≤ (S * T - Z) / (2 * Z^2 * S * T) by positivity)
  convert h₁.add h₂ using 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul, u, v]
  field_simp
  ring

namespace WeightedInjection
variable {d q : ℕ}

/-- The retained negative same-color block, extended over every cell. -/
noncomputable def retainedNegative (μ : FiniteLaw (Injection d q)) :
    Matrix (Fin d × Fin q) (Fin d × Fin q) ℝ := fun x y =>
  if x.1 ≠ y.1 ∧ x.2 = y.2 then -mean μ x.1 x.2 * mean μ y.1 y.2 else 0

noncomputable def twoX (W : Fin 2 → Fin q → ℝ) (x : Fin 2 × Fin q) : ℝ :=
  if x.1 = 0 then W 0 x.2 else 0

noncomputable def twoY (W : Fin 2 → Fin q → ℝ) (x : Fin 2 × Fin q) : ℝ :=
  if x.1 = 1 then W 1 x.2 else 0

noncomputable def twoAlpha (W : Fin 2 → Fin q → ℝ) (x : Fin 2 × Fin q) : ℝ :=
  ((∑ c, W 1 c) * twoX W x + (∑ c, W 0 c) * twoY W x) / partition W

noncomputable def twoOuter (W : Fin 2 → Fin q → ℝ) :
    Matrix (Fin 2 × Fin q) (Fin 2 × Fin q) ℝ :=
  (1 / partition W) • (Matrix.vecMulVec (twoX W) (twoY W) +
    Matrix.vecMulVec (twoY W) (twoX W))

/-- Exact marginal decomposition p = alpha - beta. -/
theorem twoAlpha_eq (W : Fin 2 → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (x : Fin 2 × Fin q) :
    twoAlpha W x = mean (law W hW.nonneg (partition_pos W hW)) x.1 x.2 + twoBeta W x := by
  obtain ⟨i,c⟩ := x
  fin_cases i
  · change twoAlpha W (0,c) = mean (law W hW.nonneg (partition_pos W hW)) 0 c + twoBeta W (0,c)
    rw [mean_two_zero W hW c]
    simp only [twoAlpha, twoX, twoY, twoBeta, ite_true,
      show (0 : Fin 2) ≠ 1 from by decide, ite_false, mul_zero, add_zero]
    ring
  · change twoAlpha W (1,c) = mean (law W hW.nonneg (partition_pos W hW)) 1 c + twoBeta W (1,c)
    rw [mean_two_one W hW c]
    simp only [twoAlpha, twoX, twoY, twoBeta, ite_true,
      show (1 : Fin 2) ≠ 0 from by decide, ite_false, mul_zero, zero_add]
    ring

/-- Exact covariance decomposition of the genuine two-row injection law. -/
theorem covariance_two_decomposition (W : Fin 2 → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) :
    let μ := law W hW.nonneg (partition_pos W hW)
    covariance μ = Matrix.diagonal (marginalVector μ) + retainedNegative μ + twoOuter W -
      Matrix.vecMulVec (marginalVector μ) (marginalVector μ) + twoCorrection W hW := by
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  ext x y
  change covariance μ x y =
    (if x = y then mean μ x.1 x.2 else 0) +
    (if x.1 ≠ y.1 ∧ x.2 = y.2 then -mean μ x.1 x.2 * mean μ y.1 y.2 else 0) +
    (1 / partition W) *
      ((if x.1 = 0 then W 0 x.2 else 0) * (if y.1 = 1 then W 1 y.2 else 0) +
       (if x.1 = 1 then W 1 x.2 else 0) * (if y.1 = 0 then W 0 y.2 else 0)) -
    mean μ x.1 x.2 * mean μ y.1 y.2 +
    (if x.1 ≠ y.1 ∧ x.2 = y.2 then mean μ x.1 x.2 * mean μ y.1 y.2 - twoBeta W x else 0)
  obtain ⟨i,c⟩ := x
  obtain ⟨j,b⟩ := y
  fin_cases i <;> fin_cases j
  · change covariance μ (0,c) (0,b) = _
    by_cases hcb : c = b
    · subst b
      rw [covariance_diagonal]
      simp [μ, pow_two]
    · rw [covariance_same_row μ 0 hcb]
      simp [μ, hcb]
  · change covariance μ (0,c) (1,b) = _
    rw [covariance, FiniteLaw.covariance_eq_mixed_moment, mixed_moment_two W hW c b]
    change _ - mean μ 0 c * mean μ 1 b = _
    by_cases hcb : c = b
    · subst b
      simp [twoBeta, μ]
      ring
    · simp [μ, hcb, Ne.symm hcb]
      ring
  · change covariance μ (1,c) (0,b) = _
    rw [covariance, FiniteLaw.covariance_symm, FiniteLaw.covariance_eq_mixed_moment,
      mixed_moment_two W hW b c]
    change _ - mean μ 0 b * mean μ 1 c = _
    by_cases hcb : c = b
    · subst b
      simp [twoBeta, μ]
      ring
    · simp [μ, hcb]
      ring
  · change covariance μ (1,c) (1,b) = _
    by_cases hcb : c = b
    · subst b
      rw [covariance_diagonal]
      simp [μ, pow_two]
    · rw [covariance_same_row μ 1 hcb]
      simp [μ, hcb]

/-- Lemma 4.8, in its equivalent covariance form, for the actual two-row weighted law. -/
theorem two_row_retained_covariance (W : Fin 2 → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) :
    let μ := law W hW.nonneg (partition_pos W hW)
    (((1 + 10 / (s + 1)^2) • Matrix.diagonal (marginalVector μ)) +
      retainedNegative μ - covariance μ).PosSemidef := by
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  let S := ∑ c, W 0 c
  let T := ∑ c, W 1 c
  have hS : 0 < S := by
    have h := hW.row_mass 0
    norm_num at h
    dsimp [S]
    linarith [hW.positive]
  have hT : 0 < T := by
    have h := hW.row_mass 1
    norm_num at h
    dsimp [T]
    linarith [hW.positive]
  have hZ := partition_pos W hW
  have hZT : partition W ≤ S * T := by
    rw [partition_two]
    exact sub_le_self _ (Finset.sum_nonneg (fun c _ =>
      mul_nonneg (hW.nonneg 0 c) (hW.nonneg 1 c)))
  have houter := two_outer_bound (twoX W) (twoY W) hS hT hZ hZT
  change ((1 / 2 : ℝ) • Matrix.vecMulVec (twoAlpha W) (twoAlpha W) - twoOuter W).PosSemidef at houter
  let v := fun x => twoAlpha W x - 2 * twoBeta W x
  have hv : (Matrix.vecMulVec v v).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star v
  have hsum := ((twoBeta_rank_bound W hW).add (twoCorrection_bound W hW)).add
    (houter.add (hv.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)))
  convert hsum using 1
  rw [covariance_two_decomposition W hW]
  ext x y
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.diagonal_apply, Matrix.vecMulVec_apply, v, twoAlpha_eq W hW, marginalVector]
  split_ifs <;> ring

end WeightedInjection
end EdgeColoringMixing
