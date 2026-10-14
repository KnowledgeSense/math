import ArithmeticSections.ConditionContinuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds

namespace ArithmeticSections

/-- A bounded derivative estimate used only on a compact subinterval of (-1,1). -/
theorem arccos_lipschitz_small {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (3 / 5))
    (hy : y ∈ Set.Icc (0 : ℝ) (3 / 5)) :
    |Real.arccos y - Real.arccos x| ≤ 2 * |y - x| := by
  have hd : ∀ z ∈ Set.Icc (0 : ℝ) (3 / 5), DifferentiableAt ℝ Real.arccos z := by
    intro z hz
    exact (Real.hasDerivAt_arccos (by linarith [hz.1]) (by linarith [hz.2])).differentiableAt
  have hb : ∀ z ∈ Set.Icc (0 : ℝ) (3 / 5), ‖deriv Real.arccos z‖ ≤ (2 : ℝ) := by
    intro z hz
    rw [Real.deriv_arccos, Real.norm_eq_abs, abs_neg]
    have hs : 0 ≤ 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
    have hsqr := Real.sq_sqrt hs
    have hspos := Real.sqrt_nonneg (1 - z ^ 2)
    have hslo : 1 / 2 ≤ Real.sqrt (1 - z ^ 2) := by nlinarith [hz.1, hz.2]
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ (by linarith : 0 < Real.sqrt (1 - z ^ 2))).mpr
    linarith
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (0 : ℝ) (3 / 5)).norm_image_sub_le_of_norm_deriv_le hd hb hx hy

/-- The cosine bound used for all the small angles. -/
theorem small_angle_cos_bound {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 4) :
    31 / 32 ≤ Real.cos s := by
  have h := Real.one_sub_sq_div_two_le_cos (x := s)
  nlinarith

/-- The minus deviation estimate in inverse-radius coordinates. -/
theorem arccos_minus_quadratic {c s : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1 / 2)
    (hs : 0 ≤ s) (hs' : s ≤ 1 / 4) :
    0 ≤ Real.arccos c - Real.arccos (c / Real.cos s) ∧
      Real.arccos c - Real.arccos (c / Real.cos s) ≤ s ^ 2 := by
  have hcos := small_angle_cos_bound hs hs'
  have hcospos : 0 < Real.cos s := by linarith
  have hrpos : 0 ≤ c / Real.cos s := div_nonneg hc hcospos.le
  have hrle : c / Real.cos s ≤ 3 / 5 := by
    apply (div_le_iff₀ hcospos).mpr
    linarith
  have hcr : c ≤ c / Real.cos s := by
    apply (le_div_iff₀ hcospos).mpr
    nlinarith [Real.cos_le_one s]
  have hdiff : c / Real.cos s - c ≤ 1 - Real.cos s := by
    have hh : c / Real.cos s ≤ (1 - Real.cos s) + c := by
      apply (div_le_iff₀ hcospos).mpr
      nlinarith [Real.cos_le_one s]
    linarith
  refine ⟨sub_nonneg.mpr (Real.antitone_arccos hcr), ?_⟩
  have h := arccos_lipschitz_small ⟨hc, by linarith⟩ ⟨hrpos, hrle⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hcr)] at h
  have ha : Real.arccos c - Real.arccos (c / Real.cos s) ≤
      |Real.arccos (c / Real.cos s) - Real.arccos c| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  have hquad := Real.one_sub_sq_div_two_le_cos (x := s)
  nlinarith

/-- Elementary half-angle identity, including all denominator side conditions. -/
theorem sine_quotient_half_angles {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (ht : t ≤ 1 / 4) :
    Real.sin (t - s) / (Real.sin t - Real.sin s) =
      Real.cos ((t - s) / 2) / Real.cos ((t + s) / 2) := by
  have hsum := small_angle_cos_bound (s := (t + s) / 2) (by linarith) (by linarith)
  have hsum0 : Real.cos ((t + s) / 2) ≠ 0 := by linarith
  have hsin : 0 < Real.sin ((t - s) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_gt_three])
  rw [Real.sin_sub_sin]
  have he : Real.sin (t - s) = 2 * Real.sin ((t - s) / 2) * Real.cos ((t - s) / 2) := by
    convert Real.sin_two_mul ((t - s) / 2) using 1
    congr 1
    ring
  rw [he]
  field_simp

/-- The plus deviation estimate in inverse-radius coordinates. -/
theorem arccos_plus_quadratic {c s t : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1 / 2)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1 / 4) :
    0 ≤ Real.arccos (c * Real.cos ((t + s) / 2) / Real.cos ((t - s) / 2)) - Real.arccos c ∧
      Real.arccos (c * Real.cos ((t + s) / 2) / Real.cos ((t - s) / 2)) - Real.arccos c ≤ s * t := by
  let u := (t - s) / 2
  let v := (t + s) / 2
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hu' : u ≤ 1 / 4 := by dsimp [u]; linarith
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have hv' : v ≤ 1 / 4 := by dsimp [v]; linarith
  have hcu := small_angle_cos_bound hu hu'
  have hcv := small_angle_cos_bound hv hv'
  have hcupos : 0 < Real.cos u := by linarith
  have hcvpos : 0 < Real.cos v := by linarith
  have huv : u ≤ v := by dsimp [u, v]; linarith
  have hcvu : Real.cos v ≤ Real.cos u :=
    Real.cos_le_cos_of_nonneg_of_le_pi hu (by linarith [Real.pi_gt_three] : v ≤ Real.pi) huv
  have hd : Real.cos u - Real.cos v = 2 * Real.sin (s / 2) * Real.sin (t / 2) := by
    rw [Real.cos_sub_cos]
    have he1 : (u + v) / 2 = t / 2 := by dsimp [u, v]; ring
    have he2 : (u - v) / 2 = -(s / 2) := by dsimp [u, v]; ring
    rw [he1, he2, Real.sin_neg]
    ring
  have hsin_s : 0 ≤ Real.sin (s / 2) := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith) (by linarith [Real.pi_gt_three])
  have hsin_t : 0 ≤ Real.sin (t / 2) := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith) (by linarith [Real.pi_gt_three])
  have hds : Real.cos u - Real.cos v ≤ s * t / 2 := by
    rw [hd]
    have hm := mul_le_mul (Real.sin_le (by linarith : 0 ≤ s / 2))
      (Real.sin_le (by linarith : 0 ≤ t / 2)) hsin_t (by linarith : 0 ≤ s / 2)
    nlinarith
  let d := c * Real.cos v / Real.cos u
  have hdpos : 0 ≤ d := by dsimp [d]; positivity
  have hdle : d ≤ c := by
    dsimp [d]
    apply (div_le_iff₀ hcupos).mpr
    exact mul_le_mul_of_nonneg_left hcvu hc
  have hdiff : c - d ≤ s * t / 2 := by
    have he : c - d = (c / Real.cos u) * (Real.cos u - Real.cos v) := by
      dsimp [d]
      field_simp
    rw [he]
    have hcl : c / Real.cos u ≤ 1 := (div_le_one hcupos).mpr (by linarith)
    calc
      c / Real.cos u * (Real.cos u - Real.cos v) ≤ Real.cos u - Real.cos v := by
        nlinarith [sub_nonneg.mpr hcvu]
      _ ≤ _ := hds
  change 0 ≤ Real.arccos d - Real.arccos c ∧ Real.arccos d - Real.arccos c ≤ s * t
  refine ⟨sub_nonneg.mpr (Real.antitone_arccos hdle), ?_⟩
  have h := arccos_lipschitz_small ⟨hdpos, by linarith⟩ ⟨hc, by linarith⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hdle)] at h
  have ha : Real.arccos d - Real.arccos c ≤ |Real.arccos c - Real.arccos d| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  linarith

/-- The quadratic estimates of Lemma 3.1 for the actual order statistics. -/
theorem deviations_quadratic {γ : ℝ} (hγ : Irrational γ)
    (hlo : 1 / 3 < γ) (hhi : γ < 1 / 2) {k : ℕ} (hk : 2 ≤ k)
    (ht : secondDistance γ k ≤ 1 / 4) :
    0 ≤ minusDeviation γ k ∧ minusDeviation γ k ≤ firstDistance γ k ^ 2 ∧
    0 ≤ plusDeviation γ k ∧ plusDeviation γ k ≤ firstDistance γ k * secondDistance γ k := by
  have hs := firstDistance_pos hγ (by omega : 1 ≤ k)
  have hst := firstDistance_lt_second hγ hk
  have ha : 0 ≤ Real.pi * γ := by nlinarith [Real.pi_pos]
  have ha' : Real.pi * γ < Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hc : 0 < Real.cos (Real.pi * γ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha'⟩
  have hc' : Real.cos (Real.pi * γ) ≤ 1 / 2 := by
    rw [← Real.cos_pi_div_three]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
    nlinarith [Real.pi_pos]
  have harc := Real.arccos_cos ha (by linarith [Real.pi_pos] : Real.pi * γ ≤ Real.pi)
  have hm := arccos_minus_quadratic hc.le hc' hs.le (by linarith : firstDistance γ k ≤ 1 / 4)
  have hp := arccos_plus_quadratic hc.le hc' hs.le hst.le ht
  have hmeq : minusDeviation γ k = Real.arccos (Real.cos (Real.pi * γ)) -
      Real.arccos (Real.cos (Real.pi * γ) / Real.cos (firstDistance γ k)) := by
    simp only [minusDeviation, sectionG, rotationRadius, mul_inv_rev, inv_inv, harc,
      div_eq_mul_inv]
    ring
  have hpeq : plusDeviation γ k =
      Real.arccos (Real.cos (Real.pi * γ) * Real.cos ((secondDistance γ k + firstDistance γ k) / 2) /
        Real.cos ((secondDistance γ k - firstDistance γ k) / 2)) -
        Real.arccos (Real.cos (Real.pi * γ)) := by
    rw [plusDeviation, sectionG, sine_quotient_half_angles hs hst ht, rotationRadius]
    simp only [mul_inv_rev, inv_inv, harc, div_eq_mul_inv]
    congr 2
    ring
  rw [hmeq, hpeq]
  exact ⟨hm.1, hm.2, hp.1, hp.2⟩

/-- Convenient product version: both deviations are at most the product of the two minima. -/
theorem max_deviation_le_product {γ : ℝ} (hγ : Irrational γ)
    (hlo : 1 / 3 < γ) (hhi : γ < 1 / 2) {k : ℕ} (hk : 2 ≤ k)
    (ht : secondDistance γ k ≤ 1 / 4) :
    max (minusDeviation γ k) (plusDeviation γ k) ≤ firstDistance γ k * secondDistance γ k := by
  have h := deviations_quadratic hγ hlo hhi hk ht
  have hs := firstDistance_pos hγ (by omega : 1 ≤ k)
  have hst := firstDistance_lt_second hγ hk
  exact max_le (by nlinarith [h.2.1]) h.2.2.2

end ArithmeticSections
