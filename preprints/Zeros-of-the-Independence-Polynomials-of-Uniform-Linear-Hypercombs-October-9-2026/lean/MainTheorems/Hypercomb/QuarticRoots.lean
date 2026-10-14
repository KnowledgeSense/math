import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace ResearchMain.Hypercomb

def quartic (a σ τ v : ℝ) : ℝ :=
  v ^ 4 - τ * v ^ 3 + (1 - σ) * v ^ 2 - a * τ * v - a * σ

theorem quartic_positive_roots {a σ τ : ℝ} (ha : 2 ≤ a)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hτ0 : 0 < τ) :
    ∃ r p : ℝ, τ < r ∧ 0 ≤ p ∧ quartic a σ τ r = 0 ∧
      quartic a σ τ (-p) = 0 ∧ p < r := by
  let M := a + τ + 2
  have hM1 : 1 < M := by dsimp [M]; linarith
  have hM0 : 0 < M := by linarith
  have hMt : τ < M := by dsimp [M]; linarith
  have htSq : 0 < τ ^ 2 := sq_pos_of_pos hτ0
  have hat : 2 * τ ^ 2 ≤ a * τ ^ 2 := mul_le_mul_of_nonneg_right ha htSq.le
  have hast : 0 ≤ a * σ := mul_nonneg (by linarith) hσ0
  have hσt : 0 ≤ σ * τ ^ 2 := mul_nonneg hσ0 htSq.le
  have hFt : quartic a σ τ τ < 0 := by dsimp [quartic]; nlinarith
  have hMsq : a * τ + a < M ^ 2 := by dsimp [M]; nlinarith [sq_nonneg (a - τ)]
  have hMsub : 1 < M - τ := by dsimp [M]; linarith
  have hM3 : M ^ 3 < M ^ 3 * (M - τ) := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hMsub (pow_pos hM0 3)
  have hMmul : (a * τ + a) * M < M ^ 3 := by
    have h := mul_lt_mul_of_pos_right hMsq hM0
    nlinarith only [h]
  have haM : a ≤ a * M := by nlinarith
  have haσ : a * σ ≤ a := by nlinarith
  have hterm : 0 ≤ (1 - σ) * M ^ 2 := mul_nonneg (by linarith) (sq_nonneg M)
  have hFM : 0 < quartic a σ τ M := by
    dsimp [quartic]
    nlinarith only [hM3, hMmul, haM, haσ, hterm]
  have hMsq1 : 1 < M ^ 2 := by nlinarith
  have hM4 : a < M ^ 4 := by
    have haMsq : a < M ^ 2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ a) hτ0.le]
    nlinarith [sq_nonneg (M ^ 2 - 1)]
  have hτM3 : 0 ≤ τ * M ^ 3 := mul_nonneg hτ0.le (pow_nonneg hM0.le 3)
  have haτM : 0 ≤ a * τ * M := by positivity
  have hFnegM : 0 < quartic a σ τ (-M) := by
    dsimp [quartic]
    nlinarith only [hM4, haσ, hτM3, haτM, hterm]
  have hcont : Continuous (quartic a σ τ) := by unfold quartic; fun_prop
  obtain ⟨r, hr, hFr⟩ := intermediate_value_Icc hMt.le hcont.continuousOn ⟨hFt.le, hFM.le⟩
  have hrt : τ < r := by
    have hne : r ≠ τ := by intro he; subst r; linarith
    exact lt_of_le_of_ne hr.1 (Ne.symm hne)
  have hF0 : quartic a σ τ (-0) ≤ 0 := by simpa [quartic] using neg_nonpos.mpr hast
  have hcontneg : Continuous (fun v => quartic a σ τ (-v)) := hcont.comp continuous_neg
  obtain ⟨p, hp, hFp⟩ := intermediate_value_Icc hM0.le hcontneg.continuousOn ⟨hF0, hFnegM.le⟩
  change quartic a σ τ (-p) = 0 at hFp
  have hrpos : 0 < r := lt_trans hτ0 hrt
  have hrp : 0 < r + p := by linarith [hp.1]
  have hdiff : (r + p) * ((r - p) * (r ^ 2 + p ^ 2 + (1 - σ)) -
      τ * (r ^ 2 - r * p + p ^ 2 + a)) = quartic a σ τ r - quartic a σ τ (-p) := by
    unfold quartic
    ring
  rw [hFr, hFp, sub_self] at hdiff
  have he := (mul_eq_zero.mp hdiff).resolve_left (ne_of_gt hrp)
  have hcoeff : 0 < r ^ 2 + p ^ 2 + (1 - σ) := by nlinarith [sq_pos_of_pos hrpos, sq_nonneg p]
  have hright : 0 < τ * (r ^ 2 - r * p + p ^ 2 + a) := by
    apply mul_pos hτ0
    nlinarith [sq_nonneg (r - p), sq_nonneg r, sq_nonneg p]
  have hpr : p < r := by nlinarith only [he, hcoeff, hright]
  exact ⟨r, p, hrt, hp.1, hFr, hFp, hpr⟩

theorem quartic_factor_data {a σ τ r p : ℝ}
    (hr : quartic a σ τ r = 0) (hp : quartic a σ τ (-p) = 0)
    (hrp : 0 < r + p) :
    let δ := r - p - τ
    let H := r * p
    let Q := 1 - σ + H + τ * δ + δ ^ 2
    (r - p) * Q + H * δ = a * τ ∧ H * Q = a * σ ∧
      ∀ v : ℝ, quartic a σ τ v = (v - r) * (v + p) * (v ^ 2 + δ * v + Q) := by
  dsimp only
  let δ := r - p - τ
  let H := r * p
  let Q := 1 - σ + H + τ * δ + δ ^ 2
  let L := (r - p) * Q + H * δ - a * τ
  let C := H * Q - a * σ
  have hid (v : ℝ) : quartic a σ τ v =
      (v - r) * (v + p) * (v ^ 2 + δ * v + Q) + L * v + C := by
    dsimp [quartic, δ, H, Q, L, C]
    ring
  have h1 : L * r + C = 0 := by have h := hid r; rw [hr] at h; nlinarith only [h]
  have h2 : -L * p + C = 0 := by have h := hid (-p); rw [hp] at h; nlinarith only [h]
  have hmul : (r + p) * L = 0 := by nlinarith only [h1, h2]
  have hL : L = 0 := (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hrp)
  have hC : C = 0 := by rw [hL] at h1; simpa only [zero_mul, zero_add] using h1
  refine ⟨?_, ?_, ?_⟩
  · change (r - p) * Q + H * δ = a * τ
    dsimp only [L] at hL
    linarith
  · change H * Q = a * σ
    dsimp only [C] at hC
    linarith
  · intro v
    change quartic a σ τ v = (v - r) * (v + p) * (v ^ 2 + δ * v + Q)
    rw [hid, hL, hC, zero_mul, add_zero, add_zero]

end ResearchMain.Hypercomb
