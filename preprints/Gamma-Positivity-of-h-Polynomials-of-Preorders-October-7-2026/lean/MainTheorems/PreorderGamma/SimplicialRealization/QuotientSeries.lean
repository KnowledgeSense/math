import MainTheorems.PreorderGamma.SimplicialRealization.RootProjectionFibers
import MainTheorems.PreorderGamma.RootEhrhart

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

noncomputable def quotientEhrhartSeries : PowerSeries ℚ :=
  PowerSeries.mk fun t => (quotientLatticeCount (E := E) t : ℚ)

omit [Fintype E] in
@[simp] theorem quotientEhrhartSeries_coeff (t : ℕ) :
    PowerSeries.coeff t (quotientEhrhartSeries (E := E)) =
      (quotientLatticeCount (E := E) t : ℚ) := PowerSeries.coeff_mk _ _

noncomputable def quotientFiniteSeries (t : ℕ) : PowerSeries ℚ :=
  ∑ z : QuotientPoints (E := E) t,
    PowerSeries.X ^ quotientLatticeDegree z.val * (PowerSeries.invOneSubPow ℚ 1).val

noncomputable def rootFiniteSeries (t : ℕ) : PowerSeries ℚ :=
  ∑ z : QuotientPoints (E := E) t,
    PowerSeries.X ^ quotientLatticeDegree z.val *
      (PowerSeries.invOneSubPow ℚ (Fintype.card E + 1)).val

theorem quotientFiniteSeries_coeff {j t : ℕ} (hjt : j ≤ t) :
    PowerSeries.coeff j (quotientFiniteSeries (E := E) t) =
      (quotientLatticeCount (E := E) j : ℚ) := by
  classical
  rw [quotientFiniteSeries, quotientLatticeCount_nested hjt]
  simp only [map_sum, PowerSeries.coeff_X_pow_mul',
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
    PowerSeries.coeff_mk, Nat.zero_add, Nat.choose_zero_right, Nat.cast_one,
    Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : quotientLatticeDegree z.val ≤ j <;> simp [h]

theorem rootFiniteSeries_coeff (t : ℕ) :
    PowerSeries.coeff t (rootFiniteSeries (E := E) t) =
      (rootLatticeCount (E := E) t : ℚ) := by
  classical
  rw [rootFiniteSeries, rootLatticeCount_projected_fibers]
  simp only [map_sum, PowerSeries.coeff_X_pow_mul',
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
    PowerSeries.coeff_mk, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [ite_eq_left ((quotientIntegerPoint_iff_degree t z.val).mp z.property)]
  exact_mod_cast (Nat.choose_symm_add (a := Fintype.card E)
    (b := t - quotientLatticeDegree z.val))

theorem finiteSeries_factor (t : ℕ) :
    quotientFiniteSeries (E := E) t *
      (PowerSeries.invOneSubPow ℚ (Fintype.card E)).val =
      rootFiniteSeries (E := E) t := by
  classical
  rw [quotientFiniteSeries, rootFiniteSeries, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  rw [mul_assoc, ← Units.val_mul, ← PowerSeries.invOneSubPow_add, Nat.add_comm 1]

theorem powerSeries_coeff_mul_congr_le (f g q : PowerSeries ℚ) (t : ℕ)
    (h : ∀ j ≤ t, PowerSeries.coeff j f = PowerSeries.coeff j g) :
    PowerSeries.coeff t (f * q) = PowerSeries.coeff t (g * q) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hsum := Finset.mem_antidiagonal.mp hp
  rw [h p.1 (by omega)]

theorem root_ehrhart_series_quotient :
    rootEhrhartSeries (E := E) = quotientEhrhartSeries (E := E) *
      (PowerSeries.invOneSubPow ℚ (Fintype.card E)).val := by
  ext t
  rw [rootEhrhartSeries_coeff, ← rootFiniteSeries_coeff, ← finiteSeries_factor]
  apply powerSeries_coeff_mul_congr_le
  intro j hj
  rw [quotientFiniteSeries_coeff hj, quotientEhrhartSeries_coeff]

theorem quotient_ehrhart_series :
    quotientEhrhartSeries (E := E) =
      ((supportPolynomial (E := E)).map (Nat.castRingHom ℚ) : PowerSeries ℚ) *
        (PowerSeries.invOneSubPow ℚ (Fintype.card E + 1)).val := by
  have hfactor : (PowerSeries.invOneSubPow ℚ (2 * Fintype.card E + 1)).val =
      (PowerSeries.invOneSubPow ℚ (Fintype.card E + 1)).val *
        (PowerSeries.invOneSubPow ℚ (Fintype.card E)).val := by
    rw [← Units.val_mul, ← PowerSeries.invOneSubPow_add]
    congr 2
    omega
  have h := root_ehrhart_series (E := E)
  rw [root_ehrhart_series_quotient, hfactor, ← mul_assoc] at h
  have h' := congrArg (fun f : PowerSeries ℚ =>
    f * ((PowerSeries.invOneSubPow ℚ (Fintype.card E))⁻¹).val) h
  simpa only [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one] using h'

theorem quotient_ehrhart_numerator :
    quotientEhrhartSeries (E := E) *
      (1 - PowerSeries.X : PowerSeries ℚ) ^ (Fintype.card E + 1) =
      ((supportPolynomial (E := E)).map (Nat.castRingHom ℚ) : PowerSeries ℚ) := by
  rw [quotient_ehrhart_series, mul_assoc,
    ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow, Units.val_inv, mul_one]

end ResearchMain.PreorderGamma.SimplicialRealization
