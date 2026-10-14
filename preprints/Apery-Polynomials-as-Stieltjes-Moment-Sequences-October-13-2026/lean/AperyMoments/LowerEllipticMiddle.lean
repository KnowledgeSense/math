import AperyMoments.LowerEllipticBoundary

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def middleEllipticChange (c θ : ℝ) : ℝ :=
  Real.sqrt c / Real.sqrt (1 - (1 - c ^ 2) * Real.sin θ ^ 2)

def middleEllipticDerivative (c θ : ℝ) : ℝ :=
  Real.sqrt c * (1 - c ^ 2) * Real.sin θ * Real.cos θ /
    ((1 - (1 - c ^ 2) * Real.sin θ ^ 2) *
      Real.sqrt (1 - (1 - c ^ 2) * Real.sin θ ^ 2))

theorem middleElliptic_base_pos {c : ℝ} (hc : 0 < c) (θ : ℝ) :
    0 < 1 - (1 - c ^ 2) * Real.sin θ ^ 2 :=
  ellipticK_base_pos (by nlinarith : 1 - c ^ 2 < 1) θ

theorem middleEllipticChange_hasDerivAt {c : ℝ} (hc : 0 < c) (θ : ℝ) :
    HasDerivAt (middleEllipticChange c) (middleEllipticDerivative c θ) θ := by
  have hb := middleElliptic_base_pos hc θ
  have h := (hasDerivAt_const θ (Real.sqrt c)).div
    (((hasDerivAt_const θ (1 : ℝ)).sub
      (((Real.hasDerivAt_sin θ).pow 2).const_mul (1 - c ^ 2))).sqrt hb.ne')
    (Real.sqrt_pos.2 hb).ne'
  convert h using 1
  · rfl
  · unfold middleEllipticDerivative
    simp only [Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_mul, zero_sub]
    rw [Real.sq_sqrt hb.le]
    field_simp

theorem middleEllipticChange_continuous {c : ℝ} (hc : 0 < c) :
    Continuous (middleEllipticChange c) :=
  continuous_iff_continuousAt.mpr fun θ => (middleEllipticChange_hasDerivAt hc θ).continuousAt

theorem middleEllipticDerivative_nonneg {c θ : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (hθ : θ ∈ Ioo 0 (Real.pi / 2)) : 0 ≤ middleEllipticDerivative c θ := by
  unfold middleEllipticDerivative
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by nlinarith))
      (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])).le)
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩).le
  · exact mul_nonneg (middleElliptic_base_pos hc θ).le (Real.sqrt_nonneg _)

theorem middleElliptic_substitution {c θ : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (hθ : θ ∈ Ioo 0 (Real.pi / 2)) :
    ((middleEllipticChange c θ ^ 2 - c) ^ (-(1 / 2 : ℝ)) *
      (1 - c * middleEllipticChange c θ ^ 2) ^ (-(1 / 2 : ℝ))) *
      middleEllipticDerivative c θ =
        (1 - (1 - c ^ 2) * Real.sin θ ^ 2) ^ (-(1 / 2 : ℝ)) := by
  let D := 1 - (1 - c ^ 2) * Real.sin θ ^ 2
  let m := 1 - c ^ 2
  have hD : 0 < D := middleElliptic_base_pos hc θ
  have hm : 0 < m := by dsimp [m]; nlinarith
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hsqc := Real.sq_sqrt hc.le
  have hsqD := Real.sq_sqrt hD.le
  have hsqm := Real.sq_sqrt hm.le
  have hA : middleEllipticChange c θ ^ 2 - c =
      c * m * Real.sin θ ^ 2 / D := by
    unfold middleEllipticChange
    change (Real.sqrt c / Real.sqrt D) ^ 2 - c = _
    rw [div_pow, hsqc, hsqD]
    field_simp
    dsimp [D, m]
    ring
  have hB : 1 - c * middleEllipticChange c θ ^ 2 =
      m * Real.cos θ ^ 2 / D := by
    unfold middleEllipticChange
    change 1 - c * (Real.sqrt c / Real.sqrt D) ^ 2 = _
    rw [div_pow, hsqc, hsqD]
    field_simp
    dsimp [D, m]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hApos : 0 < c * m * Real.sin θ ^ 2 / D := by positivity
  have hBpos : 0 < m * Real.cos θ ^ 2 / D := by positivity
  rw [hA, hB, inverse_sqrt_rpow hApos.le, inverse_sqrt_rpow hBpos.le,
    Real.sqrt_div (by positivity), Real.sqrt_div (by positivity),
    Real.sqrt_mul (by positivity : 0 ≤ c * m), Real.sqrt_mul hc.le,
    Real.sqrt_mul hm.le, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
    abs_of_pos hsin, abs_of_pos hcos, inverse_sqrt_rpow hD.le]
  change _ * (Real.sqrt c * m * Real.sin θ * Real.cos θ /
    (D * Real.sqrt D)) = (Real.sqrt D)⁻¹
  field_simp
  nlinarith [hsqm]

theorem middleEllipticChange_endpoints {c : ℝ} (hc : 0 < c) :
    middleEllipticChange c 0 = Real.sqrt c ∧
    middleEllipticChange c (Real.pi / 2) = (Real.sqrt c)⁻¹ := by
  constructor
  · simp [middleEllipticChange]
  · simp only [middleEllipticChange, Real.sin_pi_div_two, one_pow, mul_one]
    rw [show 1 - (1 - c ^ 2) = c ^ 2 by ring, Real.sqrt_sq hc.le]
    have h := Real.sq_sqrt hc.le
    have hs := (Real.sqrt_pos.2 hc).ne'
    field_simp
    nlinarith

theorem middleElliptic_substitution_ae {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    (fun θ => ((middleEllipticChange c θ ^ 2 - c) ^ (-(1 / 2 : ℝ)) *
      (1 - c * middleEllipticChange c θ ^ 2) ^ (-(1 / 2 : ℝ))) *
      middleEllipticDerivative c θ) =ᵐ[volume.restrict (uIoc 0 (Real.pi / 2))]
    (fun θ => (1 - (1 - c ^ 2) * Real.sin θ ^ 2) ^ (-(1 / 2 : ℝ))) := by
  have hne : ∀ᵐ θ : ℝ ∂volume, θ ≠ Real.pi / 2 := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_eq_eq_singleton] using
      (measure_singleton (Real.pi / 2) : volume {Real.pi / 2} = 0)
  apply (ae_restrict_iff' measurableSet_uIoc).mpr
  filter_upwards [hne] with θ hθne hθ
  rw [uIoc_of_le (by positivity)] at hθ
  exact middleElliptic_substitution hc hc1 ⟨hθ.1, lt_of_le_of_ne hθ.2 hθne⟩

/-- The real contribution between the two branch points is the original elliptic integral. -/
theorem lowerElliptic_middle_interval {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    (∫ t in Real.sqrt c..(Real.sqrt c)⁻¹,
      (t ^ 2 - c) ^ (-(1 / 2 : ℝ)) *
        (1 - c * t ^ 2) ^ (-(1 / 2 : ℝ))) = ellipticK (1 - c ^ 2) := by
  have he := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.pi / 2)
    (f := middleEllipticChange c) (f' := middleEllipticDerivative c)
    (g := fun t => (t ^ 2 - c) ^ (-(1 / 2 : ℝ)) *
      (1 - c * t ^ 2) ^ (-(1 / 2 : ℝ)))
    (middleEllipticChange_continuous hc).continuousOn
    (fun θ _ => middleEllipticChange_hasDerivAt hc θ)
    (by
      intro θ hθ
      rw [min_eq_left (by positivity), max_eq_right (by positivity)] at hθ
      exact middleEllipticDerivative_nonneg hc hc1 hθ)
  rw [(middleEllipticChange_endpoints hc).1, (middleEllipticChange_endpoints hc).2] at he
  rw [← he, ellipticK]
  exact intervalIntegral.integral_congr_ae_restrict (middleElliptic_substitution_ae hc hc1)

theorem lowerElliptic_middle_interval_integrable {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    IntervalIntegrable (fun t => (t ^ 2 - c) ^ (-(1 / 2 : ℝ)) *
      (1 - c * t ^ 2) ^ (-(1 / 2 : ℝ))) volume (Real.sqrt c) (Real.sqrt c)⁻¹ := by
  have hi := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.pi / 2)
    (f := middleEllipticChange c) (f' := middleEllipticDerivative c)
    (g := fun t => (t ^ 2 - c) ^ (-(1 / 2 : ℝ)) *
      (1 - c * t ^ 2) ^ (-(1 / 2 : ℝ)))
    (middleEllipticChange_continuous hc).continuousOn
    (fun θ _ => middleEllipticChange_hasDerivAt hc θ)
    (by
      intro θ hθ
      rw [min_eq_left (by positivity), max_eq_right (by positivity)] at hθ
      exact middleEllipticDerivative_nonneg hc hc1 hθ)
  rw [(middleEllipticChange_endpoints hc).1, (middleEllipticChange_endpoints hc).2] at hi
  exact hi.mp ((ellipticK_integrable (show 1 - c ^ 2 < 1 by nlinarith)).congr_ae
    (middleElliptic_substitution_ae hc hc1).symm)

end AperyMoments
