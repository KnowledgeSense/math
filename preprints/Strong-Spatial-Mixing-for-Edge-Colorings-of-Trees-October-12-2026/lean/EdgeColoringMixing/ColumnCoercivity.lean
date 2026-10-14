import EdgeColoringMixing.TwoRowBase

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EdgeColoringMixing.WeightedInjection
open Finset Matrix

variable {d q : ℕ}

noncomputable def colorVector (μ : FiniteLaw (Injection d q)) (c : Fin q)
    (x : Fin d × Fin q) : ℝ := if x.2 = c then mean μ x.1 x.2 else 0

theorem colorVector_nonneg (μ : FiniteLaw (Injection d q)) (c : Fin q)
    (x : Fin d × Fin q) : 0 ≤ colorVector μ c x := by
  unfold colorVector
  split_ifs
  · exact mean_nonneg μ x.1 x.2
  · rfl

theorem sum_colorVector (μ : FiniteLaw (Injection d q)) (c : Fin q) :
    ∑ x, colorVector μ c x = colorMean μ c := by
  simp [colorVector, Fintype.sum_prod_type, colorMean]

theorem sum_color_diagonal (μ : FiniteLaw (Injection d q)) :
    (∑ c, Matrix.diagonal (colorVector μ c)) = Matrix.diagonal (marginalVector μ) := by
  ext x y
  simp only [Matrix.sum_apply, Matrix.diagonal_apply, colorVector, marginalVector]
  by_cases hxy : x = y
  · simp [hxy]
  · simp [hxy]

theorem columnBlock_eq_sum (μ : FiniteLaw (Injection d q)) :
    columnBlock μ = ∑ c, (Matrix.diagonal (colorVector μ c) -
      Matrix.vecMulVec (colorVector μ c) (colorVector μ c)) := by
  ext x y
  simp only [Matrix.sum_apply, Matrix.sub_apply, Matrix.diagonal_apply,
    Matrix.vecMulVec_apply, colorVector, columnBlock]
  by_cases hxy : x = y
  · subst y
    simp
  · by_cases hcolor : x.2 = y.2
    · have hrow : x.1 ≠ y.1 := by
        intro h
        exact hxy (Prod.ext h hcolor)
      simp [hxy, hcolor, hrow, mul_ite, ite_mul]
    · simp [hxy, hcolor, mul_ite, ite_mul]

theorem retainedNegative_eq (μ : FiniteLaw (Injection d q)) :
    retainedNegative μ = columnBlock μ - Matrix.diagonal (marginalVector μ) +
      Matrix.diagonal (fun x => (marginalVector μ x)^2) := by
  ext x y
  simp only [retainedNegative, columnBlock, Matrix.add_apply, Matrix.sub_apply,
    Matrix.diagonal_apply, marginalVector]
  by_cases hcolor : x.2 = y.2
  · by_cases hrow : x.1 = y.1
    · have hxy : x = y := Prod.ext hrow hcolor
      subst y
      simp
      ring
    · have hxy : x ≠ y := fun h => hrow (congrArg Prod.fst h)
      simp [hcolor, hrow, hxy]
  · have hxy : x ≠ y := fun h => hcolor (congrArg Prod.snd h)
    simp [hcolor, hxy]

/-- Exact retained-block coercivity, using the true color-occupancy bound. -/
theorem columnBlock_coercivity (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (Δ : ℕ) (hd : d ≤ Δ) :
    let μ := law W hW.nonneg (partition_pos W hW)
    (columnBlock μ - (s / ((Δ : ℝ) + s)) • Matrix.diagonal (marginalVector μ)).PosSemidef := by
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  let r := (Δ : ℝ) / ((Δ : ℝ) + s)
  have hden : 0 < (Δ : ℝ) + s := add_pos_of_nonneg_of_pos (Nat.cast_nonneg Δ) hW.positive
  have hr : 0 ≤ r := div_nonneg (Nat.cast_nonneg Δ) hden.le
  have hcolor (c : Fin q) : colorMean μ c ≤ r := by
    apply (colorMean_le W hW c).trans
    apply (div_le_div_iff₀ (show 0 < (d : ℝ) + s by positivity [hW.positive]) hden).mpr
    have hcast : (d : ℝ) ≤ Δ := by exact_mod_cast hd
    nlinarith [hW.positive]
  have hblock (c : Fin q) :
      (r • Matrix.diagonal (colorVector μ c) -
        Matrix.vecMulVec (colorVector μ c) (colorVector μ c)).PosSemidef := by
    apply weighted_rank_one_bound (colorVector μ c) (colorVector μ c)
      (colorVector_nonneg μ c) (fun _ h => h) hr
    have hsq (x : Fin d × Fin q) : (colorVector μ c x)^2 / colorVector μ c x = colorVector μ c x := by
      by_cases hx : colorVector μ c x = 0
      · simp [hx]
      · field_simp
    simp_rw [hsq]
    rw [sum_colorVector]
    exact hcolor c
  have h := Matrix.posSemidef_sum (s := univ) (fun c _ => hblock c)
  convert h using 1
  rw [columnBlock_eq_sum]
  ext x y
  simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← sum_color_diagonal μ]
  simp only [Matrix.sum_apply, Matrix.diagonal_apply,
    Matrix.vecMulVec_apply, Finset.sum_sub_distrib, ← Finset.mul_sum]
  dsimp only [r]
  field_simp
  ring

/-- Diagonal marginals are dominated by the retained color blocks with the exact surplus loss. -/
theorem diagonal_le_columnBlock (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (Δ : ℕ) (hd : d ≤ Δ) :
    let μ := law W hW.nonneg (partition_pos W hW)
    ((((Δ : ℝ) + s) / s) • columnBlock μ - Matrix.diagonal (marginalVector μ)).PosSemidef := by
  have hden : 0 < (Δ : ℝ) + s := add_pos_of_nonneg_of_pos (Nat.cast_nonneg Δ) hW.positive
  have h := (columnBlock_coercivity W hW Δ hd).smul
    (show 0 ≤ ((Δ : ℝ) + s) / s from div_nonneg hden.le hW.positive.le)
  dsimp only at h ⊢
  convert h using 1
  ext x y
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp [hW.positive.ne']

/-- The diagonal square term has its exact universal marginal bound. -/
theorem diagonal_square_bound (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) :
    let μ := law W hW.nonneg (partition_pos W hW)
    ((1 / (s + 1)) • Matrix.diagonal (marginalVector μ) -
      Matrix.diagonal (fun x => (marginalVector μ x)^2)).PosSemidef := by
  dsimp only
  have hdiag : ((1 / (s + 1)) • Matrix.diagonal
      (marginalVector (law W hW.nonneg (partition_pos W hW))) -
      Matrix.diagonal (fun x => (marginalVector (law W hW.nonneg (partition_pos W hW)) x)^2)) =
      Matrix.diagonal (fun x => (1 / (s + 1)) *
        marginalVector (law W hW.nonneg (partition_pos W hW)) x -
        (marginalVector (law W hW.nonneg (partition_pos W hW)) x)^2) := by
    ext x y
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply]
    split_ifs <;> ring
  rw [hdiag]
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro x
  have ht : 0 < s + 1 := by linarith [hW.positive]
  have hmax := (marginal_le W hW x.1 x.2).trans
    (div_le_div_of_nonneg_right (hW.le_one x.1 x.2) ht.le)
  have hp := mean_nonneg (law W hW.nonneg (partition_pos W hW)) x.1 x.2
  dsimp only [marginalVector]
  nlinarith

/-- The retained-column theorem implies the covariance metric bound without losing a color variance. -/
theorem retained_covariance_to_columnBlock (W : Fin d → Fin q → ℝ) {s b : ℝ}
    (hW : RowSurplus W s) (hb : 0 ≤ b) (Δ : ℕ) (hd : d ≤ Δ)
    (hretained : let μ := law W hW.nonneg (partition_pos W hW)
      (((1 + b) • Matrix.diagonal (marginalVector μ)) + retainedNegative μ - covariance μ).PosSemidef) :
    let μ := law W hW.nonneg (partition_pos W hW)
    let δ := (b + 1 / (s + 1)) * (((Δ : ℝ) + s) / s)
    ((1 + δ) • columnBlock μ - covariance μ).PosSemidef := by
  dsimp only at hretained ⊢
  have ht : 0 < s + 1 := by linarith [hW.positive]
  have h₁ := hretained.add (diagonal_square_bound W hW)
  have h₂ := (diagonal_le_columnBlock W hW Δ hd).smul
    (show 0 ≤ b + 1 / (s + 1) by positivity)
  convert h₁.add h₂ using 1
  rw [retainedNegative_eq]
  ext x y
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Removing cross-color blocks never makes the retained block exceed the marginal diagonal. -/
theorem columnBlock_upper (μ : FiniteLaw (Injection d q)) :
    (Matrix.diagonal (marginalVector μ) - columnBlock μ).PosSemidef := by
  have h : (∑ c, Matrix.vecMulVec (colorVector μ c) (colorVector μ c)).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro c _
    simpa using Matrix.posSemidef_vecMulVec_self_star (colorVector μ c)
  convert h using 1
  rw [columnBlock_eq_sum, ← sum_color_diagonal μ]
  ext x y
  simp only [Matrix.sub_apply, Matrix.sum_apply, Finset.sum_sub_distrib]
  ring

/-- The spectral cap on the retained negative block is proved from the actual cell bounds. -/
theorem retainedNegative_upper (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) :
    let μ := law W hW.nonneg (partition_pos W hW)
    ((1 / (s + 1)) • Matrix.diagonal (marginalVector μ) - retainedNegative μ).PosSemidef := by
  dsimp only
  have h := (columnBlock_upper (law W hW.nonneg (partition_pos W hW))).add
    (diagonal_square_bound W hW)
  convert h using 1
  rw [retainedNegative_eq]
  ext x y
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem retainedNegative_hermitian (μ : FiniteLaw (Injection d q)) :
    (retainedNegative μ).IsHermitian := by
  rw [retainedNegative_eq]
  have hD : (Matrix.diagonal (marginalVector μ)).IsHermitian := by simp
  have hD₂ : (Matrix.diagonal (fun x => (marginalVector μ x)^2)).IsHermitian := by simp
  exact ((columnBlock_posSemidef μ).isHermitian.sub hD).add hD₂

theorem retainedNegative_zero_of_mean_zero (μ : FiniteLaw (Injection d q))
    (x y : Fin d × Fin q) (hy : mean μ y.1 y.2 = 0) : retainedNegative μ x y = 0 := by
  simp [retainedNegative, hy]

/-- The one-row case is an exact diagonal minus rank-one covariance. -/
theorem covariance_one_row (μ : FiniteLaw (Injection 1 q)) :
    covariance μ = Matrix.diagonal (marginalVector μ) -
      Matrix.vecMulVec (marginalVector μ) (marginalVector μ) := by
  ext x y
  have hrow : x.1 = y.1 := Subsingleton.elim _ _
  by_cases hcolor : x.2 = y.2
  · have hxy : x = y := Prod.ext hrow hcolor
    subst y
    rw [covariance_diagonal]
    simp [Matrix.sub_apply, Matrix.vecMulVec_apply, marginalVector, pow_two]
  · have hxy : x ≠ y := fun h => hcolor (congrArg Prod.snd h)
    obtain ⟨i,c⟩ := x
    obtain ⟨j,b⟩ := y
    dsimp only at hrow
    subst j
    rw [covariance_same_row μ i hcolor]
    simp [Matrix.sub_apply, Matrix.vecMulVec_apply, marginalVector, hxy]

theorem one_row_retained_covariance (W : Fin 1 → Fin q → ℝ) {s b : ℝ}
    (hW : RowSurplus W s) (hb : 0 ≤ b) :
    let μ := law W hW.nonneg (partition_pos W hW)
    (((1 + b) • Matrix.diagonal (marginalVector μ)) + retainedNegative μ - covariance μ).PosSemidef := by
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  have hD : (Matrix.diagonal (marginalVector μ)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun x => mean_nonneg μ x.1 x.2)
  have hP : (Matrix.vecMulVec (marginalVector μ) (marginalVector μ)).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star (marginalVector μ)
  have hF : retainedNegative μ = 0 := by
    ext x y
    simp [retainedNegative, Subsingleton.elim x.1 y.1]
  change (((1 + b) • Matrix.diagonal (marginalVector μ)) + retainedNegative μ - covariance μ).PosSemidef
  rw [hF, covariance_one_row]
  convert (hD.smul hb).add hP using 1
  ext x y
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
  ring

end EdgeColoringMixing.WeightedInjection
