import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

namespace ResearchMain.DiagonalSchatten

noncomputable section

def powerEnvelope (a t : ℝ) : ℝ :=
  (a + 1 - (a - 1) * t) * t ^ a - (a + 1) * t + a - 1

def powerEnvelopeDerivative (a t : ℝ) : ℝ :=
  a * (a + 1) * t ^ (a - 1) - (a + 1) * (a - 1) * t ^ a - (a + 1)

theorem powerEnvelope_hasDerivAt (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (powerEnvelope a) (powerEnvelopeDerivative a t) t := by
  have hp := Real.hasDerivAt_rpow_const (p := a) (Or.inl ht.ne')
  have h := (((hasDerivAt_const t (a + 1)).sub
    ((hasDerivAt_id t).const_mul (a - 1))).mul hp).sub
    ((hasDerivAt_id t).const_mul (a + 1))
  convert h.add_const (a - 1) using 1
  · ext x
    simp only [powerEnvelope, Pi.sub_apply, Pi.mul_apply, id_eq]
    ring
  · unfold powerEnvelopeDerivative
    simp only [Pi.sub_apply, id_eq]
    rw [Real.rpow_sub_one ht.ne']
    field_simp [ht.ne']
    ring

theorem powerEnvelopeDerivative_hasDerivAt (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (powerEnvelopeDerivative a)
      (a * (a + 1) * (a - 1) * (1 - t) * t ^ (a - 2)) t := by
  have h1 := Real.hasDerivAt_rpow_const (p := a - 1) (Or.inl ht.ne')
  have h2 := Real.hasDerivAt_rpow_const (p := a) (Or.inl ht.ne')
  have h := ((h1.const_mul (a * (a + 1))).sub
    (h2.const_mul ((a + 1) * (a - 1)))).sub_const (a + 1)
  convert h using 1
  · rfl
  · have hp : t ^ (a - 1) = t ^ (a - 2) * t := by
      simpa only [show a - 2 + 1 = a - 1 by ring] using
        Real.rpow_add_one ht.ne' (a - 2)
    rw [show a - 1 - 1 = a - 2 by ring, hp]
    ring

theorem powerEnvelopeDerivative_negative {a t : ℝ}
    (ha : 1 < a) (ht : 0 < t) (hneq : t ≠ 1) :
    powerEnvelopeDerivative a t < 0 := by
  have h1 : powerEnvelopeDerivative a 1 = 0 := by simp [powerEnvelopeDerivative]; ring
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · have hmono : StrictMonoOn (powerEnvelopeDerivative a) (Set.Icc t 1) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc t 1)
      · intro x hx
        exact (powerEnvelopeDerivative_hasDerivAt a (lt_of_lt_of_le ht hx.1)).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hxpos := lt_trans ht hx.1
        rw [(powerEnvelopeDerivative_hasDerivAt a hxpos).deriv]
        have ha0 : 0 < a := lt_trans zero_lt_one ha
        have ha1 : 0 < a + 1 := by linarith
        have ha2 : 0 < a - 1 := sub_pos.mpr ha
        have hx1 : 0 < 1 - x := sub_pos.mpr hx.2
        positivity
    have h := hmono ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt
    simpa only [h1] using h
  · have hanti : StrictAntiOn (powerEnvelopeDerivative a) (Set.Icc 1 t) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc 1 t)
      · intro x hx
        exact (powerEnvelopeDerivative_hasDerivAt a (lt_of_lt_of_le zero_lt_one hx.1)).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hxpos := lt_trans zero_lt_one hx.1
        rw [(powerEnvelopeDerivative_hasDerivAt a hxpos).deriv]
        have ha0 : 0 < a := lt_trans zero_lt_one ha
        have ha1 : 0 < a + 1 := by linarith
        have ha2 : 0 < a - 1 := sub_pos.mpr ha
        have hx1 : 1 - x < 0 := sub_neg.mpr hx.1
        have hpre : 0 < a * (a + 1) * (a - 1) := by positivity
        exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hpre hx1)
          (Real.rpow_pos_of_pos hxpos _)
    have h := hanti ⟨le_rfl, hgt.le⟩ ⟨hgt.le, le_rfl⟩ hgt
    simpa only [h1] using h

theorem powerEnvelope_sign {a t : ℝ} (ha : 1 < a) (ht : 0 < t) :
    (t < 1 → 0 < powerEnvelope a t) ∧
      (1 < t → powerEnvelope a t < 0) := by
  have h1 : powerEnvelope a 1 = 0 := by simp [powerEnvelope]
  constructor
  · intro hlt
    have hanti : StrictAntiOn (powerEnvelope a) (Set.Icc t 1) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc t 1)
      · intro x hx
        exact (powerEnvelope_hasDerivAt a (lt_of_lt_of_le ht hx.1)).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hxpos := lt_trans ht hx.1
        rw [(powerEnvelope_hasDerivAt a hxpos).deriv]
        exact powerEnvelopeDerivative_negative ha hxpos (ne_of_lt hx.2)
    have h := hanti ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt
    simpa only [h1] using h
  · intro hgt
    have hanti : StrictAntiOn (powerEnvelope a) (Set.Icc 1 t) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc 1 t)
      · intro x hx
        exact (powerEnvelope_hasDerivAt a (lt_of_lt_of_le zero_lt_one hx.1)).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hxpos := lt_trans zero_lt_one hx.1
        rw [(powerEnvelope_hasDerivAt a hxpos).deriv]
        exact powerEnvelopeDerivative_negative ha hxpos (ne_of_gt hx.1)
    have h := hanti ⟨le_rfl, hgt.le⟩ ⟨hgt.le, le_rfl⟩ hgt
    simpa only [h1] using h

theorem divided_power_rational_upper {a t : ℝ}
    (ha : 1 < a) (ht : 0 < t) (hneq : t ≠ 1)
    (hd : 0 < a + 1 - (a - 1) * t) :
    (t ^ a - 1) / (t - 1) < 2 * a / (a + 1 - (a - 1) * t) := by
  have ht1 : t - 1 ≠ 0 := sub_ne_zero.mpr hneq
  have hid : powerEnvelope a t =
      (t - 1) * (((t ^ a - 1) / (t - 1)) * (a + 1 - (a - 1) * t) - 2 * a) := by
    unfold powerEnvelope
    field_simp [ht1]
    ring
  have hs := powerEnvelope_sign ha ht
  apply (lt_div_iff₀ hd).mpr
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · have hpos := hs.1 hlt
    rw [hid] at hpos
    have htneg : t - 1 < 0 := sub_neg.mpr hlt
    nlinarith
  · have hneg := hs.2 hgt
    rw [hid] at hneg
    have htpos : 0 < t - 1 := sub_pos.mpr hgt
    nlinarith

end

end ResearchMain.DiagonalSchatten
