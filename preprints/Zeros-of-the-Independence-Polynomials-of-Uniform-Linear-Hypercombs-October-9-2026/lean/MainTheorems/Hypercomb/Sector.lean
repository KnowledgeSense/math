import MainTheorems.Hypercomb.QuarticSector
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace ResearchMain.Hypercomb

def LeftCone (z : ℂ) : Prop := z.re < 0 ∧ z.im ^ 2 < 3 * z.re ^ 2

theorem leftCone_arg {z : ℂ} (hz : LeftCone z) : 2 * Real.pi / 3 < |z.arg| := by
  have hne : z ≠ 0 := by intro he; subst z; simpa using hz.1
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hne
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.sq_norm z
  have hnormbound : ‖z‖ < -2 * z.re := by nlinarith [hz.1, hz.2]
  have hcos : Real.cos z.arg < -1 / 2 := by
    rw [Complex.cos_arg hne]
    apply (div_lt_iff₀ hnorm).mpr
    linarith
  have hcosangle : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
    norm_num
  by_contra h
  have hle : |z.arg| ≤ 2 * Real.pi / 3 := le_of_not_gt h
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg z.arg)
    (by linarith [Real.pi_pos] : 2 * Real.pi / 3 ≤ Real.pi) hle
  rw [hcosangle, Real.cos_abs] at h
  linarith

theorem inverse_rightCone {w : ℂ} (hw : RightCone w) : LeftCone (-w⁻¹) := by
  have hne : w ≠ 0 := by intro he; subst w; simpa using hw.1
  have hnorm : 0 < Complex.normSq w := Complex.normSq_pos.mpr hne
  constructor
  · simp only [Complex.neg_re, Complex.inv_re]
    exact neg_neg_of_pos (div_pos hw.1 hnorm)
  · simp only [Complex.neg_im, Complex.inv_im, Complex.neg_re, Complex.inv_re, div_pow, neg_sq]
    rw [← mul_div_assoc]
    exact (div_lt_div_iff_of_pos_right (pow_pos hnorm 2)).mpr hw.2

theorem leftCone_of_arg {z : ℂ} (hz : z ≠ 0) (harg : 2 * Real.pi / 3 < |z.arg|) : LeftCone z := by
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hcosangle : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
    norm_num
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi
    (by linarith [Real.pi_pos] : 0 ≤ 2 * Real.pi / 3) (Complex.abs_arg_le_pi z) harg
  rw [hcosangle, Real.cos_abs, Complex.cos_arg hz] at hcos
  have hre := (div_lt_iff₀ hnorm).mp hcos
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.sq_norm z
  constructor <;> nlinarith

def transformedQuartic (a σ τ : ℝ) (w : ℂ) : ℂ :=
  (((w - (a : ℂ)) * (w - (a : ℂ) + 1) - (σ : ℂ) * w) ^ 2) -
    (τ : ℂ) ^ 2 * w ^ 2 * (w - (a : ℂ))

theorem transformed_zero_tau {a σ : ℝ} (ha : 2 ≤ a)
    (hσ0 : 0 ≤ σ) (w : ℂ) (hw : transformedQuartic a σ 0 w = 0) : RightCone w := by
  have hD : (w - (a : ℂ)) * (w - (a : ℂ) + 1) - (σ : ℂ) * w = 0 := by
    simpa only [transformedQuartic, Complex.ofReal_zero, zero_pow (by decide : 2 ≠ 0),
      zero_mul, sub_zero, sq_eq_zero_iff] using hw
  have hr := congrArg Complex.re hD
  have hi := congrArg Complex.im hD
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
    sub_zero, add_zero, zero_mul] at hr hi
  have him : w.im = 0 := by
    by_contra h
    have hmul : w.im * (2 * w.re - (2 * a - 1 + σ)) = 0 := by nlinarith only [hi]
    have hlin := (mul_eq_zero.mp hmul).resolve_left h
    have hdisc : 0 < (2 * a - 1 + σ) ^ 2 - 4 * a * (a - 1) := by
      have hprod : 0 ≤ (2 * a - 1) * σ := mul_nonneg (by linarith) hσ0
      nlinarith [sq_nonneg σ]
    have hx : w.re = (2 * a - 1 + σ) / 2 := by linarith only [hlin]
    rw [hx] at hr
    nlinarith [sq_nonneg w.im]
  have hre : 0 < w.re := by
    rw [him] at hr
    have hC : 0 < 2 * a - 1 + σ := by linarith
    have hA : 0 < a * (a - 1) := mul_pos (by linarith) (by linarith)
    by_contra h
    have hle : w.re ≤ 0 := le_of_not_gt h
    have hprod : (2 * a - 1 + σ) * w.re ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hC.le hle
    nlinarith [sq_nonneg w.re]
  exact ⟨hre, by rw [him]; nlinarith [sq_pos_of_pos hre]⟩

theorem transformed_rightCone {a σ τ : ℝ} (ha : 2 ≤ a)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hτ0 : 0 ≤ τ) (hτ2 : τ ≤ 2)
    (w : ℂ) (hw : transformedQuartic a σ τ w = 0) : RightCone w := by
  by_cases ht : τ = 0
  · subst τ
    exact transformed_zero_tau ha hσ0 w hw
  · have htpos : 0 < τ := lt_of_le_of_ne hτ0 (Ne.symm ht)
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (w - (a : ℂ)) (by decide : 0 < 2)
    let D := (w - (a : ℂ)) * (w - (a : ℂ) + 1) - (σ : ℂ) * w
    have hprod : (D - (τ : ℂ) * w * c) * (D + (τ : ℂ) * w * c) = 0 := by
      have hid : (D - (τ : ℂ) * w * c) * (D + (τ : ℂ) * w * c) =
          transformedQuartic a σ τ w + (τ : ℂ) ^ 2 * w ^ 2 * (w - (a : ℂ) - c ^ 2) := by
        dsimp [D, transformedQuartic]
        ring
      rw [hid, hw, hc, sub_self, mul_zero, add_zero]
    have hex : ∃ v : ℂ, v ^ 2 = w - (a : ℂ) ∧ D = (τ : ℂ) * w * v := by
      rcases mul_eq_zero.mp hprod with h | h
      · exact ⟨c, hc, sub_eq_zero.mp h⟩
      · refine ⟨-c, by simpa using hc, ?_⟩
        have h' := add_eq_zero_iff_eq_neg.mp h
        simpa only [mul_neg] using h'
    obtain ⟨v, hv, hD⟩ := hex
    have hwv : w = (a : ℂ) + v ^ 2 := by linear_combination -hv
    have hF : complexQuartic a σ τ v = 0 := by
      rw [hwv] at hD
      dsimp only [D] at hD
      rw [hwv] at hD
      dsimp [complexQuartic]
      linear_combination hD
    rw [hwv]
    exact quartic_root_rightCone ha hσ0 hσ1 htpos hτ2 v hF

def sectorQuartic (a σ τ : ℝ) (z : ℂ) : ℂ :=
  (((1 + (a : ℂ) * z) * (1 + ((a - 1 : ℝ) : ℂ) * z) + (σ : ℂ) * z) ^ 2) +
    (τ : ℂ) ^ 2 * z * (1 + (a : ℂ) * z)

theorem quartic_inversion_identity (a σ τ : ℝ) (z : ℂ) (hz : z ≠ 0) :
    z ^ 4 * transformedQuartic a σ τ (-z⁻¹) = sectorQuartic a σ τ z := by
  dsimp [transformedQuartic, sectorQuartic]
  push_cast
  field_simp
  ring

theorem sector_quadratic_arg {a σ : ℝ} (ha : 2 ≤ a) (hσ0 : 0 ≤ σ)
    (z : ℂ) (hz : (1 + (a : ℂ) * z) * (1 + ((a - 1 : ℝ) : ℂ) * z) + (σ : ℂ) * z = 0) :
    2 * Real.pi / 3 < |z.arg| := by
  have hne : z ≠ 0 := by intro he; subst z; simp at hz
  have hP : sectorQuartic a σ 0 z = 0 := by simp only [sectorQuartic, hz]; norm_num
  have hw : transformedQuartic a σ 0 (-z⁻¹) = 0 :=
    (mul_eq_zero.mp ((quartic_inversion_identity a σ 0 z hne).trans hP)).resolve_left (pow_ne_zero 4 hne)
  have hleft := inverse_rightCone (transformed_zero_tau ha hσ0 (-z⁻¹) hw)
  simp only [inv_neg, inv_inv, neg_neg] at hleft
  exact leftCone_arg hleft

theorem sector_quartic_arg {a σ τ : ℝ} (ha : 2 ≤ a)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hτ0 : 0 ≤ τ) (hτ2 : τ ≤ 2)
    (z : ℂ) (hz : sectorQuartic a σ τ z = 0) : 2 * Real.pi / 3 < |z.arg| := by
  have hne : z ≠ 0 := by intro he; subst z; simp [sectorQuartic] at hz
  let w := -z⁻¹
  have hid : z ^ 4 * transformedQuartic a σ τ w = sectorQuartic a σ τ z :=
    quartic_inversion_identity a σ τ z hne
  have hw : transformedQuartic a σ τ w = 0 :=
    (mul_eq_zero.mp (hid.trans hz)).resolve_left (pow_ne_zero 4 hne)
  have hcone := transformed_rightCone ha hσ0 hσ1 hτ0 hτ2 w hw
  have hinv : -w⁻¹ = z := by simp [w]
  have hleft := inverse_rightCone hcone
  rw [hinv] at hleft
  exact leftCone_arg hleft

end ResearchMain.Hypercomb
