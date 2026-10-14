import MainTheorems.Hypercomb.QuarticRoots

namespace ResearchMain.Hypercomb

def complexQuartic (a σ τ : ℝ) (v : ℂ) : ℂ :=
  v ^ 4 - (τ : ℂ) * v ^ 3 + (1 - (σ : ℂ)) * v ^ 2 - (a : ℂ) * τ * v - (a : ℂ) * σ

def RightCone (z : ℂ) : Prop := 0 < z.re ∧ z.im ^ 2 < 3 * z.re ^ 2

theorem quartic_complex_factor {a σ τ r p : ℝ}
    (hr : quartic a σ τ r = 0) (hp : quartic a σ τ (-p) = 0) (hrp : 0 < r + p) :
    let δ : ℝ := r - p - τ
    let H : ℝ := r * p
    let Q : ℝ := 1 - σ + H + τ * δ + δ ^ 2
    ∀ v : ℂ, complexQuartic a σ τ v =
      (v - (r : ℂ)) * (v + (p : ℂ)) * (v ^ 2 + (δ : ℂ) * v + (Q : ℂ)) := by
  dsimp only
  obtain ⟨hlin, hcon, _⟩ := quartic_factor_data hr hp hrp
  have hlinC := congrArg (fun x : ℝ => (x : ℂ)) hlin
  have hconC := congrArg (fun x : ℝ => (x : ℂ)) hcon
  intro v
  dsimp only [complexQuartic]
  push_cast at hlinC hconC ⊢
  linear_combination v * hlinC + hconC

theorem quartic_delta_positive {a σ τ r p Q : ℝ}
    (ha : 2 ≤ a) (hτ0 : 0 < τ)
    (hr : 0 < r) (hp : 0 ≤ p) (hpr : p < r) (hQ : 0 < Q)
    (hQeq : Q = 1 - σ + r * p + τ * (r - p - τ) + (r - p - τ) ^ 2)
    (hlin : (r - p) * Q + r * p * (r - p - τ) = a * τ)
    (hcon : r * p * Q = a * σ) : 0 < r - p - τ := by
  let δ := r - p - τ
  have hH : 0 ≤ r * p := mul_nonneg hr.le hp
  have hsum : 0 < Q + r * p := by linarith
  have hlinear : a * τ = τ * Q + δ * (Q + r * p) := by dsimp [δ]; nlinarith only [hlin]
  by_contra h
  have hδ : δ ≤ 0 := by dsimp [δ]; linarith
  have hprod : δ * (Q + r * p) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hδ hsum.le
  have haQ : a ≤ Q := by nlinarith only [hlinear, hprod, hτ0]
  have ha0 : 0 < a := by linarith
  have hHσ : r * p ≤ σ := by
    have h := mul_le_mul_of_nonneg_left haQ hH
    nlinarith only [h, hcon, ha0]
  have hδsum : 0 < τ + δ := by dsimp [δ]; linarith
  have hprod' : δ * (τ + δ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hδ hδsum.le
  have hQ1 : Q ≤ 1 := by dsimp [δ] at hprod'; nlinarith only [hQeq, hHσ, hprod']
  linarith

theorem cone_scalar_bound {a Q K δ : ℝ} (ha : 2 ≤ a) (hQ : 0 < Q)
    (hK : 0 < K) (hδ : 0 < δ) (hKQ : Q ≤ 2 * K) (haeq : a = Q + δ * K) :
    Q < 3 * K ^ 2 + 3 * K * δ + δ ^ 2 := by
  by_cases hQlarge : 4 / 3 ≤ Q
  · have hsq : Q ^ 2 ≤ (2 * K) ^ 2 := by nlinarith only [hKQ, hQ, hK]
    have hprod : 0 < K * δ := mul_pos hK hδ
    nlinarith [sq_nonneg δ]
  · have hQsmall : Q < 4 / 3 := lt_of_not_ge hQlarge
    nlinarith [sq_nonneg K, sq_nonneg δ]

theorem quartic_root_rightCone {a σ τ : ℝ} (ha : 2 ≤ a)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hτ0 : 0 < τ) (hτ2 : τ ≤ 2)
    (v : ℂ) (hv : complexQuartic a σ τ v = 0) : RightCone ((a : ℂ) + v ^ 2) := by
  by_cases him : v.im = 0
  · have hre : 0 < ((a : ℂ) + v ^ 2).re := by
      simp only [Complex.add_re, Complex.ofReal_re, pow_two, Complex.mul_re, him, mul_zero, sub_zero]
      nlinarith [sq_nonneg v.re]
    constructor
    · exact hre
    · simp only [Complex.add_im, Complex.ofReal_im, pow_two, Complex.mul_im, him, mul_zero,
        zero_mul, add_zero, zero_pow (by decide : 2 ≠ 0)]
      simpa only [pow_two] using mul_pos (by norm_num : (0 : ℝ) < 3) (sq_pos_of_pos hre)
  · obtain ⟨r, p, hrt, hp, hFr, hFp, hpr⟩ := quartic_positive_roots ha hσ0 hσ1 hτ0
    have hr : 0 < r := lt_trans hτ0 hrt
    have hrp : 0 < r + p := by linarith
    let δ := r - p - τ
    let H := r * p
    let Q := 1 - σ + H + τ * δ + δ ^ 2
    obtain ⟨hlin, hcon, _⟩ := quartic_factor_data hFr hFp hrp
    have hfactor := quartic_complex_factor hFr hFp hrp v
    change complexQuartic a σ τ v = (v - (r : ℂ)) * (v + (p : ℂ)) *
      (v ^ 2 + (δ : ℂ) * v + (Q : ℂ)) at hfactor
    have hvr : v - (r : ℂ) ≠ 0 := by
      intro he
      have hi := congrArg Complex.im he
      exact him (by simpa using hi)
    have hvp : v + (p : ℂ) ≠ 0 := by
      intro he
      have hi := congrArg Complex.im he
      exact him (by simpa using hi)
    have hquad : v ^ 2 + (δ : ℂ) * v + (Q : ℂ) = 0 :=
      (mul_eq_zero.mp (hfactor.symm.trans hv)).resolve_left (mul_ne_zero hvr hvp)
    have hreal := congrArg Complex.re hquad
    have himag := congrArg Complex.im hquad
    simp only [Complex.add_re, Complex.add_im, pow_two, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im,
      zero_mul, sub_zero, add_zero] at hreal himag
    have hprod : v.im * (2 * v.re + δ) = 0 := by nlinarith only [himag]
    have hre : 2 * v.re + δ = 0 := (mul_eq_zero.mp hprod).resolve_left him
    have hx : v.re = -δ / 2 := by linarith only [hre]
    have hQ : 0 < Q := by nlinarith [sq_pos_of_ne_zero him, sq_nonneg v.re]
    have hδ : 0 < δ := quartic_delta_positive ha hτ0 hr hp hpr hQ rfl hlin hcon
    let K := (Q + H) / τ
    have hH : 0 ≤ H := mul_nonneg hr.le hp
    have hK : 0 < K := div_pos (by linarith) hτ0
    have hKt : K * τ = Q + H := div_mul_cancel₀ _ (ne_of_gt hτ0)
    have hKQ : Q ≤ 2 * K := by nlinarith only [hKt, hH, hτ2, hK]
    have haeq : a = Q + δ * K := by
      change (r - p) * Q + H * δ = a * τ at hlin
      have hd : r - p = δ + τ := by dsimp [δ]; ring
      rw [hd] at hlin
      have hm : τ * (a - Q - δ * K) = 0 := by linear_combination -hlin - δ * hKt
      have he := (mul_eq_zero.mp hm).resolve_left (ne_of_gt hτ0)
      linarith only [he]
    have hbound := cone_scalar_bound ha hQ hK hδ hKQ haeq
    have hy : v.im ^ 2 = Q - δ ^ 2 / 4 := by rw [hx] at hreal; nlinarith only [hreal]
    have hwre : ((a : ℂ) + v ^ 2).re = δ * (K + δ / 2) := by
      simp only [Complex.add_re, Complex.ofReal_re, pow_two, Complex.mul_re]
      rw [hx]
      linear_combination haeq - hy
    have hwim : ((a : ℂ) + v ^ 2).im ^ 2 = δ ^ 2 * (Q - δ ^ 2 / 4) := by
      simp only [Complex.add_im, Complex.ofReal_im, pow_two, Complex.mul_im, zero_add]
      rw [hx]
      linear_combination δ ^ 2 * hy
    refine ⟨?_, ?_⟩
    · rw [hwre]
      positivity
    · rw [hwre, hwim]
      have h := mul_pos (sq_pos_of_pos hδ) (sub_pos.mpr hbound)
      nlinarith only [h]

end ResearchMain.Hypercomb
