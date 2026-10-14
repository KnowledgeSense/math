import MainTheorems.WishartBlocks.GaussianSmoothing
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.Integral.Pi

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

theorem gaussian_pi_polynomial_integrable {n : ℕ} (v : Fin n → ℝ≥0) (k : ℕ) :
    Integrable (fun x : Fin n → ℝ => (1 + ‖x‖) ^ k)
      (Measure.pi fun i => gaussianReal 0 (v i)) := by
  have hX : MemLp (id : (Fin n → ℝ) → (Fin n → ℝ)) (k : ℝ≥0∞)
      (Measure.pi fun i => gaussianReal 0 (v i)) := by
    apply MemLp.of_eval
    intro i
    simpa only [Function.comp_def, id_eq] using
      (IsGaussian.memLp_id (gaussianReal 0 (v i)) (k : ℝ≥0∞) (by simp)).comp_measurePreserving
        (measurePreserving_eval (fun j => gaussianReal 0 (v j)) i)
  have hI := hX.integrable_norm_pow' (p := k)
  apply (((integrable_const 1).add hI).const_mul ((2 : ℝ) ^ (k - 1))).mono'
    (by fun_prop)
  exact ae_of_all _ fun x => by
    rw [Real.norm_of_nonneg (by positivity)]
    change (1 + ‖x‖) ^ k ≤ (2 : ℝ) ^ (k - 1) * (1 + ‖x‖ ^ k)
    simpa only [one_pow] using add_pow_le (zero_le_one (α := ℝ)) (norm_nonneg x) k

theorem gaussian_pi_real_growth_integrable {n : ℕ} (v : Fin n → ℝ≥0)
    {f : (Fin n → ℝ) → ℝ} (hf : Measurable f) {C β : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ β) :
    Integrable f (Measure.pi fun i => gaussianReal 0 (v i)) := by
  let k := ⌈β⌉₊
  apply ((gaussian_pi_polynomial_integrable v k).const_mul C).mono'
    hf.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    calc
      ‖f x‖ ≤ C * (1 + ‖x‖) ^ β := hb x
      _ ≤ C * (1 + ‖x‖) ^ k := by
        rw [← Real.rpow_natCast]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x]) (Nat.le_ceil β)) hC

noncomputable def gaussianPiQuadraticPower {n : ℕ} (c : ℝ) (d : Fin n → ℝ) (b : ℝ)
    (v : Fin n → ℝ≥0) (s : Fin n → ℝ) : ℝ :=
  ∫ x : Fin n → ℝ, (c + ∑ i, d i * (x i + s i) ^ 2) ^ b
    ∂(Measure.pi fun i => gaussianReal 0 (v i))

theorem gaussian_pi_quadratic_growth {n : ℕ} {c b : ℝ} (hc : 0 < c) (hb : 0 ≤ b)
    (d s : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) (x : Fin n → ℝ) :
    ‖(c + ∑ i, d i * (x i + s i) ^ 2) ^ b‖ ≤
      ((c + ∑ i, d i) * (1 + ‖s‖) ^ 2) ^ b * (1 + ‖x‖) ^ (2 * b) := by
  let B := (1 + ‖s‖) * (1 + ‖x‖)
  have hB : 1 ≤ B := by
    dsimp [B]
    nlinarith [norm_nonneg s, norm_nonneg x, mul_nonneg (norm_nonneg s) (norm_nonneg x)]
  have hsq : ∀ i, (x i + s i) ^ 2 ≤ B ^ 2 := by
    intro i
    have h := abs_add_le (x i) (s i)
    have hx := norm_le_pi_norm x i
    have hs := norm_le_pi_norm s i
    have ha : |x i + s i| ≤ B := by
      dsimp [B]
      rw [Real.norm_eq_abs] at hx hs
      nlinarith [norm_nonneg s, norm_nonneg x,
        mul_nonneg (norm_nonneg s) (norm_nonneg x)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (x i + s i)) ha 2
  have hq : 0 ≤ c + ∑ i, d i * (x i + s i) ^ 2 := by
    exact add_nonneg hc.le (Finset.sum_nonneg fun i _ => mul_nonneg (hd i) (sq_nonneg _))
  have hD : 0 ≤ ∑ i, d i := Finset.sum_nonneg fun i _ => hd i
  have hbound : c + ∑ i, d i * (x i + s i) ^ 2 ≤ (c + ∑ i, d i) * B ^ 2 := by
    have ht : (∑ i, d i * (x i + s i) ^ 2) ≤ (∑ i, d i) * B ^ 2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hsq i) (hd i)
    have hBB : 1 ≤ B ^ 2 := by nlinarith
    nlinarith
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hq b)]
  calc
    (c + ∑ i, d i * (x i + s i) ^ 2) ^ b ≤ ((c + ∑ i, d i) * B ^ 2) ^ b :=
      Real.rpow_le_rpow hq hbound hb
    _ = _ := by
      dsimp [B]
      rw [mul_pow, ← mul_assoc, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast_mul (by positivity) 2 b]
      norm_num

theorem gaussian_pi_quadratic_integrable {n : ℕ} {c b : ℝ} (hc : 0 < c) (hb : 0 ≤ b)
    (d s : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) (v : Fin n → ℝ≥0) :
    Integrable (fun x : Fin n → ℝ => (c + ∑ i, d i * (x i + s i) ^ 2) ^ b)
      (Measure.pi fun i => gaussianReal 0 (v i)) := by
  have hD : 0 ≤ ∑ i, d i := Finset.sum_nonneg fun i _ => hd i
  apply gaussian_pi_real_growth_integrable v (by fun_prop)
    (C := ((c + ∑ i, d i) * (1 + ‖s‖) ^ 2) ^ b) (β := 2 * b)
    (Real.rpow_nonneg (by positivity) b)
  exact gaussian_pi_quadratic_growth hc hb d s hd

theorem gaussian_pi_quadratic_split_integrable {n : ℕ} {c b : ℝ}
    (hc : 0 < c) (hb : 0 ≤ b) (d s : Fin (n + 1) → ℝ)
    (hd : ∀ i, 0 ≤ d i) (v : Fin (n + 1) → ℝ≥0) :
    Integrable
      (fun z : ℝ × (Fin n → ℝ) =>
        (c + d 0 * (z.1 + s 0) ^ 2 + ∑ i, d i.succ * (z.2 i + s i.succ) ^ 2) ^ b)
      ((gaussianReal 0 (v 0)).prod (Measure.pi fun i => gaussianReal 0 (v i.succ))) := by
  have hp := (measurePreserving_piFinSuccAbove
    (fun i => gaussianReal 0 (v i)) 0).symm
  have hi := hp.integrable_comp_of_integrable (gaussian_pi_quadratic_integrable hc hb d s hd v)
  simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.sum_univ_succ, Fin.insertNth_zero,
    Fin.zero_succAbove, Fin.cons_zero, Fin.cons_succ, cast_eq, add_assoc] using hi

theorem gaussianPiQuadraticPower_succ {n : ℕ} {c b : ℝ} (hc : 0 < c) (hb : 0 ≤ b)
    (d s : Fin (n + 1) → ℝ) (hd : ∀ i, 0 ≤ d i) (v : Fin (n + 1) → ℝ≥0) :
    gaussianPiQuadraticPower c d b v s =
      ∫ x, gaussianPiQuadraticPower (c + d 0 * (x + s 0) ^ 2)
        (fun i => d i.succ) b (fun i => v i.succ) (fun i => s i.succ)
        ∂(gaussianReal 0 (v 0)) := by
  unfold gaussianPiQuadraticPower
  rw [← ((measurePreserving_piFinSuccAbove (fun i => gaussianReal 0 (v i)) 0).symm).integral_comp']
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.sum_univ_succ, Fin.insertNth_zero, Fin.zero_succAbove,
    Fin.cons_zero, Fin.cons_succ, cast_eq, add_assoc]
  simpa only [add_assoc] using
    integral_prod _ (gaussian_pi_quadratic_split_integrable hc hb d s hd v)

theorem gaussianPiQuadraticPower_succ_reverse {n : ℕ} {c b : ℝ}
    (hc : 0 < c) (hb : 0 ≤ b) (d s : Fin (n + 1) → ℝ)
    (hd : ∀ i, 0 ≤ d i) (v : Fin (n + 1) → ℝ≥0) :
    gaussianPiQuadraticPower c d b v s =
      ∫ x : Fin n → ℝ,
        gaussianSmoothing
          (fun y => (c + (∑ i, d i.succ * (x i + s i.succ) ^ 2) + d 0 * y ^ 2) ^ b)
          (v 0) (s 0)
        ∂(Measure.pi fun i => gaussianReal 0 (v i.succ)) := by
  unfold gaussianPiQuadraticPower gaussianSmoothing
  rw [← ((measurePreserving_piFinSuccAbove (fun i => gaussianReal 0 (v i)) 0).symm).integral_comp']
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.sum_univ_succ, Fin.insertNth_zero, Fin.zero_succAbove,
    Fin.cons_zero, Fin.cons_succ, cast_eq]
  have hi := gaussian_pi_quadratic_split_integrable hc hb d s hd v
  have he :
      (fun z : ℝ × (Fin n → ℝ) =>
        (c + (d 0 * (z.1 + s 0) ^ 2 + ∑ i, d i.succ * (z.2 i + s i.succ) ^ 2)) ^ b) =
      (fun z : ℝ × (Fin n → ℝ) =>
        (c + (∑ i, d i.succ * (z.2 i + s i.succ) ^ 2) + d 0 * (z.1 + s 0) ^ 2) ^ b) := by
    ext z
    congr 1
    ring
  rw [he]
  exact integral_prod_symm _ (by simpa only [add_assoc, add_left_comm, add_comm] using hi)

theorem gaussianPiQuadraticPower_monotone {n : ℕ} {c b : ℝ} (hc : 0 < c) (hb : 0 ≤ b)
    (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) (v : Fin n → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    MonotoneOn (gaussianPiQuadraticPower c d b v) {s | ∀ i, 0 ≤ s i} := by
  induction n generalizing c with
  | zero =>
      intro s hs t ht hst
      have he : s = t := Subsingleton.elim _ _
      rw [he]
  | succ n ih =>
      intro s hs t ht hst
      let u : Fin (n + 1) → ℝ := Fin.cons (s 0) (fun i => t i.succ)
      have hsI := gaussian_pi_quadratic_split_integrable hc hb d s hd v
      have huI := gaussian_pi_quadratic_split_integrable hc hb d u hd v
      have htI := gaussian_pi_quadratic_split_integrable hc hb d t hd v
      calc
        gaussianPiQuadraticPower c d b v s ≤ gaussianPiQuadraticPower c d b v u := by
          rw [gaussianPiQuadraticPower_succ hc hb d s hd v,
            gaussianPiQuadraticPower_succ hc hb d u hd v]
          apply integral_mono (by simpa [gaussianPiQuadraticPower] using hsI.integral_prod_left)
            (by simpa [gaussianPiQuadraticPower] using huI.integral_prod_left)
          intro x
          have hc' : 0 < c + d 0 * (x + s 0) ^ 2 :=
            add_pos_of_pos_of_nonneg hc (mul_nonneg (hd 0) (sq_nonneg _))
          simpa only [u, Fin.cons_zero, Fin.cons_succ] using
            ih hc' (fun i => d i.succ) (fun i => hd i.succ) (fun i => v i.succ)
              (fun i => hv i.succ) (fun i => hs i.succ) (fun i => ht i.succ)
              (fun i => hst i.succ)
        _ ≤ gaussianPiQuadraticPower c d b v t := by
          rw [gaussianPiQuadraticPower_succ_reverse hc hb d u hd v,
            gaussianPiQuadraticPower_succ_reverse hc hb d t hd v]
          apply integral_mono
            (by simpa [gaussianSmoothing, add_assoc, add_left_comm, add_comm]
              using huI.integral_prod_right)
            (by simpa [gaussianSmoothing, add_assoc, add_left_comm, add_comm]
              using htI.integral_prod_right)
          intro x
          have hc' : 0 < c + ∑ i, d i.succ * (x i + t i.succ) ^ 2 :=
            add_pos_of_pos_of_nonneg hc
              (Finset.sum_nonneg fun i _ => mul_nonneg (hd i.succ) (sq_nonneg _))
          simpa only [u, Fin.cons_zero, Fin.cons_succ] using
            quadraticPower_gaussian_monotone hc' (hd 0) hb (hv 0) (hs 0) (ht 0) (hst 0)

end ResearchMain.WishartBlocks
