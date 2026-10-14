import MainTheorems.Corona.Midpoint
import MainTheorems.Corona.Shape

namespace ResearchMain.Corona

open Polynomial

theorem coefficient_far_bound {p : ℝ[X]} (hp : NonnegativeCoefficients p) (hm : 0 < mass p)
    {W V G : ℝ} (hW : mass p ≤ W) (hV : variance p ≤ V) (hG : 0 ≤ G) (k : ℕ)
    (hd : G / 3 ≤ |(k : ℝ) - mean p|) : G ^ 2 * p.coeff k ≤ 9 * W * V := by
  have hv0 : 0 ≤ V := (variance_nonnegative hp hm).trans hV
  have hd2 : (G / 3) ^ 2 ≤ ((k : ℝ) - mean p) ^ 2 := by
    have hsq : (G / 3) ^ 2 ≤ |(k : ℝ) - mean p| ^ 2 := by
      nlinarith only [hd, hG, abs_nonneg ((k : ℝ) - mean p)]
    simpa only [sq_abs] using hsq
  have h₁ := mul_le_mul_of_nonneg_right hd2 (hp k)
  have h₂ := centeredSum_point hp (mean p) k
  rw [centeredSum_mean p (ne_of_gt hm)] at h₂
  have h₃ := mul_le_mul_of_nonneg_left hV hm.le
  have h₄ := mul_le_mul_of_nonneg_right hW hv0
  nlinarith only [h₁, h₂, h₃, h₄]

theorem corrected_window_peak {p q C : ℝ[X]} (hp : NonnegativeCoefficients p)
    (hq : NonnegativeCoefficients q) (hC : NonnegativeCoefficients C) (hm : 0 < mass p)
    {W R : ℝ} (hW : W / 2 ≤ mass p) (hR : 1 ≤ R) (hv : variance p ≤ R ^ 2 / 2)
    (hcorrection : mass C ≤ W / (24 * R)) :
    ∃ j : ℕ, |(j : ℝ) - mean p| ≤ R ∧ W ≤ 24 * R * (p + q - C).coeff j := by
  have hR0 : 0 < R := by linarith
  obtain ⟨j, hj, hpeak⟩ := window_peak hp hm hR0 hv
  have h₁ : W ≤ 12 * R * p.coeff j := by
    have hnonneg := hp j
    nlinarith only [hW, hpeak, hR, hnonneg]
  have hCbound : 24 * R * C.coeff j ≤ W := by
    have hle := (coefficient_le_mass hC j).trans hcorrection
    simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < 24 * R)).mp hle
  have hqpos : 0 ≤ 24 * R * q.coeff j := mul_nonneg (by positivity) (hq j)
  refine ⟨j, hj, ?_⟩
  rw [coeff_sub, coeff_add]
  nlinarith only [h₁, hCbound, hqpos]

theorem ordered_polynomial_valley {A B C : ℝ[X]} (hA : NonnegativeCoefficients A)
    (hB : NonnegativeCoefficients B) (hC : NonnegativeCoefficients C)
    (hAm : 0 < mass A) (hBm : 0 < mass B) {W V R G : ℝ}
    (hW : 0 < W) (hAW : W / 2 ≤ mass A ∧ mass A ≤ W)
    (hBW : W / 2 ≤ mass B ∧ mass B ≤ W)
    (hAV : variance A ≤ V) (hBV : variance B ≤ V)
    (hR : 1 ≤ R) (hwindowA : variance A ≤ R ^ 2 / 2) (hwindowB : variance B ≤ R ^ 2 / 2)
    (hG : 6 ≤ G) (hgap : G ≤ mean B - mean A) (hseparated : 2 * R + 2 < G)
    (hsize : 432 * R * V < G ^ 2) (hcorrection : mass C ≤ W / (24 * R)) :
    ∃ j k l : ℕ, j < k ∧ k < l ∧
      (A + B - C).coeff k < (A + B - C).coeff j ∧
      (A + B - C).coeff k < (A + B - C).coeff l := by
  have hAn := mean_nonnegative hA hAm
  have hBn := mean_nonnegative hB hBm
  obtain ⟨j, hj, hpeakj⟩ := corrected_window_peak hA hB hC hAm hAW.1 hR hwindowA hcorrection
  obtain ⟨l, hl, hpeakl⟩ := corrected_window_peak hB hA hC hBm hBW.1 hR hwindowB hcorrection
  rw [add_comm B A] at hpeakl
  let k := midpointIndex (mean A) (mean B)
  have hbetween := midpoint_between_windows hAn hBn hgap hseparated hj hl
  have hdist := midpoint_distances hAn hBn hG hgap
  have hAk := coefficient_far_bound hA hAm hAW.2 hAV (by linarith : 0 ≤ G) k hdist.1
  have hBk := coefficient_far_bound hB hBm hBW.2 hBV (by linarith : 0 ≤ G) k hdist.2
  have hCk := mul_nonneg (sq_nonneg G) (hC k)
  have hcenter : G ^ 2 * (A + B - C).coeff k ≤ 18 * W * V := by
    rw [coeff_sub, coeff_add]
    nlinarith only [hAk, hBk, hCk]
  have hfactor : 0 < 24 * R * G ^ 2 := by positivity
  have hcenterscaled := mul_le_mul_of_nonneg_left hcenter (show 0 ≤ 24 * R by positivity)
  have hstrict := mul_lt_mul_of_pos_right hsize hW
  have hbefore : 24 * R * G ^ 2 * (A + B - C).coeff k < G ^ 2 * W := by
    nlinarith only [hcenterscaled, hstrict]
  have hcompare (i : ℕ) (hi : W ≤ 24 * R * (A + B - C).coeff i) :
      (A + B - C).coeff k < (A + B - C).coeff i := by
    have hb := mul_le_mul_of_nonneg_left hi (sq_nonneg G)
    have hprod : 24 * R * G ^ 2 * (A + B - C).coeff k <
        24 * R * G ^ 2 * (A + B - C).coeff i := by nlinarith only [hbefore, hb]
    exact (mul_lt_mul_iff_of_pos_left hfactor).mp hprod
  exact ⟨j, k, l, hbetween.1, hbetween.2, hcompare j hpeakj, hcompare l hpeakl⟩

theorem polynomial_not_unimodal {A B C : ℝ[X]} (hA : NonnegativeCoefficients A)
    (hB : NonnegativeCoefficients B) (hC : NonnegativeCoefficients C)
    (hAm : 0 < mass A) (hBm : 0 < mass B) {W V R G : ℝ}
    (hW : 0 < W) (hAW : W / 2 ≤ mass A ∧ mass A ≤ W)
    (hBW : W / 2 ≤ mass B ∧ mass B ≤ W)
    (hAV : variance A ≤ V) (hBV : variance B ≤ V)
    (hR : 1 ≤ R) (hwindowA : variance A ≤ R ^ 2 / 2) (hwindowB : variance B ≤ R ^ 2 / 2)
    (hG : 6 ≤ G) (hgap : G ≤ |mean A - mean B|) (hseparated : 2 * R + 2 < G)
    (hsize : 432 * R * V < G ^ 2) (hcorrection : mass C ≤ W / (24 * R)) :
    ¬Unimodal (fun k => (A + B - C).coeff k) := by
  have hvalley : ∃ j k l : ℕ, j < k ∧ k < l ∧
      (A + B - C).coeff k < (A + B - C).coeff j ∧
      (A + B - C).coeff k < (A + B - C).coeff l := by
    by_cases horder : mean A ≤ mean B
    · rw [abs_of_nonpos (sub_nonpos.mpr horder), neg_sub] at hgap
      exact ordered_polynomial_valley hA hB hC hAm hBm hW hAW hBW hAV hBV
        hR hwindowA hwindowB hG hgap hseparated hsize hcorrection
    · rw [abs_of_nonneg (by linarith : 0 ≤ mean A - mean B)] at hgap
      have h := ordered_polynomial_valley hB hA hC hBm hAm hW hBW hAW hBV hAV
        hR hwindowB hwindowA hG hgap hseparated hsize hcorrection
      simpa only [add_comm B A] using h
  obtain ⟨j, k, l, hjk, hkl, hj, hl⟩ := hvalley
  exact valley_not_unimodal hjk hkl hj hl

end ResearchMain.Corona
