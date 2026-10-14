import ArithmeticSections.SecondDistance
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

namespace ArithmeticSections

noncomputable def sectionG (γ x : ℝ) : ℝ := Real.arccos x⁻¹ - Real.pi * γ
noncomputable def minusDeviation (γ : ℝ) (k : ℕ) : ℝ :=
  -sectionG γ (rotationRadius γ * Real.cos (firstDistance γ k))
noncomputable def plusDeviation (γ : ℝ) (k : ℕ) : ℝ :=
  sectionG γ (rotationRadius γ * (Real.sin (secondDistance γ k - firstDistance γ k) /
    (Real.sin (secondDistance γ k) - Real.sin (firstDistance γ k))))

/-- Positivity is the strict inequality C(A,k), in rotation coordinates. -/
noncomputable def conditionGap (γ : ℝ) (k : ℕ) : ℝ :=
  oddDistance γ (k + 1) - max (minusDeviation γ k) (plusDeviation γ k)

/-- Local continuity behind Lemma 2.4, with denominators justified. -/
theorem continuousAt_conditionGap {γ : ℝ} (hγ : Irrational γ)
    (hlo : 1 / 3 < γ) (hhi : γ < 1 / 2) {k : ℕ} (hk : 2 ≤ k) :
    ContinuousAt (fun x => conditionGap x k) γ := by
  have hspos := firstDistance_pos hγ (by omega : 1 ≤ k)
  have hst := firstDistance_lt_second hγ hk
  have hthi := secondDistance_lt_half_pi hγ hk
  have hangle : Real.pi * γ < Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hcospos : 0 < Real.cos (Real.pi * γ) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hangle⟩
  have hrpos : 0 < rotationRadius γ := inv_pos.mpr hcospos
  have hsin : Real.sin (firstDistance γ k) < Real.sin (secondDistance γ k) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) hthi.le hst
  have hnum : 0 < Real.sin (secondDistance γ k - firstDistance γ k) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hplus : 0 < rotationRadius γ *
      (Real.sin (secondDistance γ k - firstDistance γ k) /
        (Real.sin (secondDistance γ k) - Real.sin (firstDistance γ k))) :=
    mul_pos hrpos (div_pos hnum (sub_pos.mpr hsin))
  have hminus := (firstDistance_bounds_and_radius hγ hlo hhi hk).2.2.2
  have ca : ContinuousAt (fun x : ℝ => Real.pi * x) γ := continuous_const.continuousAt.mul continuous_id.continuousAt
  have cr : ContinuousAt rotationRadius γ :=
    (Real.continuous_cos.continuousAt.comp ca).inv₀ (ne_of_gt hcospos)
  have cs := (continuous_firstDistance k).continuousAt (x := γ)
  have ct := (continuous_secondDistance k).continuousAt (x := γ)
  have cm : ContinuousAt (fun x => minusDeviation x k) γ :=
    ((Real.continuous_arccos.continuousAt.comp
      ((cr.mul (Real.continuous_cos.continuousAt.comp cs)).inv₀
        (by linarith : rotationRadius γ * Real.cos (firstDistance γ k) ≠ 0))).sub ca).neg
  have cp : ContinuousAt (fun x => plusDeviation x k) γ :=
    (Real.continuous_arccos.continuousAt.comp
      ((cr.mul ((Real.continuous_sin.continuousAt.comp (ct.sub cs)).div
        ((Real.continuous_sin.continuousAt.comp ct).sub (Real.continuous_sin.continuousAt.comp cs))
        (ne_of_gt (sub_pos.mpr hsin)))).inv₀ (ne_of_gt hplus))).sub ca
  exact (continuous_oddDistance (k + 1)).continuousAt.sub (cm.max cp)

/-- Irrational rotation parameters between one third and one half. -/
def rotationDomain : Set ℝ := {γ | 1 / 3 < γ ∧ γ < 1 / 2 ∧ Irrational γ}

theorem isOpen_condition (k : ℕ) (hk : 2 ≤ k) :
    IsOpen {γ : rotationDomain | 0 < conditionGap γ k} := by
  have h : Continuous (fun γ : rotationDomain => conditionGap γ k) := by
    apply continuous_iff_continuousAt.mpr
    intro γ
    exact (continuousAt_conditionGap γ.property.2.2 γ.property.1 γ.property.2.1 hk).comp
      continuous_subtype_val.continuousAt
  exact isOpen_lt continuous_const h

end ArithmeticSections
