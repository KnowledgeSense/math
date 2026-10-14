import MainTheorems.DiagonalSchatten.HermitianTwoSpectrum
import Mathlib.Tactic

namespace ResearchMain.DiagonalSchatten

noncomputable section

def rationalSVDCore (t w h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + h * t * w, t - h * w; w - h * t, t * w + h]

theorem positive_right_gram_slope {a b c : ℝ} (hc : 0 < c) :
    ∃ t : ℝ, 0 < t ∧ c * t ^ 2 + (a - b) * t - c = 0 := by
  let d := Real.sqrt ((a - b) ^ 2 + 4 * c ^ 2)
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hd2 : d ^ 2 = (a - b) ^ 2 + 4 * c ^ 2 := Real.sq_sqrt (by positivity)
  have hdn : 0 < d - (a - b) := by
    nlinarith [sq_nonneg (d + (a - b))]
  let t := (d - (a - b)) / (2 * c)
  refine ⟨t, div_pos hdn (by positivity), ?_⟩
  dsimp [t]
  field_simp [hc.ne']
  nlinarith [hd2]

theorem rationalSVD_factorization {a b c d t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (ht : 0 < t)
    (hdet : 0 < a * d - b * c)
    (hq : (a * b + c * d) * t ^ 2 +
      (a ^ 2 + c ^ 2 - (b ^ 2 + d ^ 2)) * t - (a * b + c * d) = 0) :
    ∃ L w h : ℝ, 0 < L ∧ 0 < w ∧ 0 < h ∧ h < 1 ∧
      (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℝ) = L • rationalSVDCore t w h := by
  let u := a + b * t
  let v := c + d * t
  let e := b - a * t
  let f := d - c * t
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have ht2 : 0 < 1 + t ^ 2 := by positivity
  have hort : u * e + v * f = 0 := by
    dsimp [u, v, e, f]
    nlinarith only [hq]
  have hdetid : (a * d - b * c) * (1 + t ^ 2) = u * f - v * e := by
    dsimp [u, v, e, f]
    ring
  have hdetid2 : (a * d - b * c) * u * (1 + t ^ 2) =
      (u ^ 2 + v ^ 2) * f := by
    rw [show (a * d - b * c) * u * (1 + t ^ 2) =
      ((a * d - b * c) * (1 + t ^ 2)) * u by ring, hdetid]
    linear_combination -v * hort
  have hf : 0 < f := by
    have hm : 0 < (u ^ 2 + v ^ 2) * f := by
      rw [← hdetid2]
      exact mul_pos (mul_pos hdet hu) ht2
    exact pos_of_mul_pos_right hm (by positivity)
  have hdiff : (u ^ 2 + v ^ 2 - (e ^ 2 + f ^ 2)) * t =
      (a * b + c * d) * (1 + t ^ 2) ^ 2 := by
    dsimp [u, v, e, f]
    linear_combination -(t ^ 2 - 1) * hq
  have hdiffpos : 0 < u ^ 2 + v ^ 2 - (e ^ 2 + f ^ 2) := by
    exact pos_of_mul_pos_left (show 0 <
      (u ^ 2 + v ^ 2 - (e ^ 2 + f ^ 2)) * t by rw [hdiff]; positivity) ht.le
  let L := u / (1 + t ^ 2)
  let w := v / u
  let h := f / u
  have hw : 0 < w := div_pos hv hu
  have hh : 0 < h := div_pos hf hu
  have he : e = -w * f := by
    dsimp [w]
    field_simp [hu.ne']
    nlinarith only [hort]
  have hh1 : h < 1 := by
    have hbnd : f < u := by
      by_contra hn
      have huf : u ≤ f := le_of_not_gt hn
      have hve : v ^ 2 ≤ e ^ 2 := by
        have he2 : e ^ 2 * u ^ 2 = v ^ 2 * f ^ 2 := by
          rw [he]
          dsimp [w]
          field_simp [hu.ne']
        have hs : u ^ 2 ≤ f ^ 2 := by nlinarith
        apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hu)).mp
        nlinarith only [he2,
          mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hs)]
      nlinarith
    exact (div_lt_one hu).mpr hbnd
  refine ⟨L, w, h, div_pos hu ht2, hw, hh, hh1, ?_⟩
  have hae : a * (1 + t ^ 2) = u - t * e := by dsimp [u, e]; ring
  have hbe : b * (1 + t ^ 2) = t * u + e := by dsimp [u, e]; ring
  have hce : c * (1 + t ^ 2) = v - t * f := by dsimp [v, f]; ring
  have hde : d * (1 + t ^ 2) = t * v + f := by dsimp [v, f]; ring
  rw [he] at hae hbe
  dsimp [w] at hae hbe
  field_simp [hu.ne'] at hae hbe
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [rationalSVDCore, Matrix.smul_apply, smul_eq_mul]
  · dsimp [L, w, h]
    field_simp [hu.ne', ht2.ne']
    nlinarith only [hae]
  · dsimp [L, w, h]
    field_simp [hu.ne', ht2.ne']
    nlinarith only [hbe]
  · dsimp [L, w, h]
    field_simp [hu.ne', ht2.ne']
    nlinarith only [hce]
  · dsimp [L, w, h]
    field_simp [hu.ne', ht2.ne']
    nlinarith only [hde]

theorem positive_two_by_two_rationalSVD (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : ∀ i j, 0 < M i j) (hdet : 0 < M.det) :
    ∃ L t w h : ℝ, 0 < L ∧ 0 < t ∧ 0 < w ∧ 0 < h ∧ h < 1 ∧
      M = L • rationalSVDCore t w h := by
  obtain ⟨t, ht, hq⟩ := positive_right_gram_slope
    (a := M 0 0 ^ 2 + M 1 0 ^ 2) (b := M 0 1 ^ 2 + M 1 1 ^ 2)
    (c := M 0 0 * M 0 1 + M 1 0 * M 1 1)
    (add_pos (mul_pos (hM 0 0) (hM 0 1)) (mul_pos (hM 1 0) (hM 1 1)))
  obtain ⟨L, w, h, hL, hw, hh, hh1, he⟩ := rationalSVD_factorization
    (hM 0 0) (hM 0 1) (hM 1 0) (hM 1 1) ht
    (by simpa [Matrix.det_fin_two] using hdet) hq
  refine ⟨L, t, w, h, hL, ht, hw, hh, hh1, ?_⟩
  convert! he using 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end

end ResearchMain.DiagonalSchatten
