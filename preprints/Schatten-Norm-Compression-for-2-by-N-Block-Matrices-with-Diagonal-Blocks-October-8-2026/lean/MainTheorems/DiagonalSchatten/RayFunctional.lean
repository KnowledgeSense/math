import MainTheorems.DiagonalSchatten.CompressionKernel
import MainTheorems.DiagonalSchatten.HomogeneousEuler
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace ResearchMain.DiagonalSchatten

noncomputable section

open Matrix
open scoped BigOperators

structure RayParameters where
  a : ℝ
  b : ℝ
  c : ℝ
  k : ℝ
  z1 : ℝ
  z2 : ℝ
  z12 : ℝ

namespace RayParameters

variable (g : RayParameters)

def image (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![g.z1 * x 0 + g.z12 * x 1, g.z12 * x 0 + g.z2 * x 1]

def denominator (x : Fin 2 → ℝ) : ℝ :=
  g.k * ((g.k + 1) * g.a * g.c * x 0 ^ 2 +
    (g.k * g.a * g.b + (g.k + 2) * g.c ^ 2) * x 0 * x 1 +
    (g.k + 1) * g.b * g.c * x 1 ^ 2)

def numerator (x : Fin 2 → ℝ) : ℝ :=
  (g.k * g.b * x 0 * x 1 + (g.k + 1) * g.c * x 0 ^ 2) * (g.image x 0) ^ 2 +
    2 * g.c * x 0 * x 1 * g.image x 0 * g.image x 1 +
    (g.k * g.a * x 0 * x 1 + (g.k + 1) * g.c * x 1 ^ 2) * (g.image x 1) ^ 2

def functional (x : Fin 2 → ℝ) : ℝ := g.numerator x / g.denominator x

def kernel (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![kernelFirst g.k g.a g.c (x 0) (x 1), -g.c;
    -g.c, kernelSecond g.k g.b g.c (x 0) (x 1)]

theorem numerator_homogeneous (x : Fin 2 → ℝ) (t : ℝ) :
    g.numerator (t • x) = t ^ 4 * g.numerator x := by
  simp only [numerator, image, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

theorem denominator_homogeneous (x : Fin 2 → ℝ) (t : ℝ) :
    g.denominator (t • x) = t ^ 2 * g.denominator x := by
  simp only [denominator, Pi.smul_apply, smul_eq_mul]
  ring

theorem functional_homogeneous (x : Fin 2 → ℝ) (t : ℝ) :
    g.functional (t • x) = t ^ 2 * g.functional x := by
  by_cases ht : t = 0
  · subst t
    simp [functional, numerator, denominator, image]
  · unfold functional
    rw [g.numerator_homogeneous, g.denominator_homogeneous]
    rw [show t ^ 4 = t ^ 2 * t ^ 2 by ring, mul_assoc,
      mul_div_mul_left _ _ (pow_ne_zero 2 ht)]
    ring

theorem contDiffAt_functional {n : WithTop ℕ∞} (x : Fin 2 → ℝ)
    (hD : g.denominator x ≠ 0) : ContDiffAt ℝ n g.functional x := by
  unfold functional
  apply ContDiffAt.div
  · unfold numerator image
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    fun_prop
  · unfold denominator
    fun_prop
  · exact hD

theorem functional_euler (x : Fin 2 → ℝ) (hD : g.denominator x ≠ 0) :
    fderiv ℝ g.functional x x = 2 * g.functional x :=
  quadratic_homogeneous_euler x
    ((g.contDiffAt_functional (n := 1) x hD).differentiableAt (by norm_num))
    (fun t _ => g.functional_homogeneous x t)

theorem kernel_determinant (x : Fin 2 → ℝ) :
    (g.kernel x).det = kernelFirst g.k g.a g.c (x 0) (x 1) *
      kernelSecond g.k g.b g.c (x 0) (x 1) - g.c ^ 2 := by
  rw [Matrix.det_fin_two]
  change kernelFirst g.k g.a g.c (x 0) (x 1) *
    kernelSecond g.k g.b g.c (x 0) (x 1) - (-g.c) * (-g.c) = _
  ring

theorem denominator_eq_kernel_determinant (x : Fin 2 → ℝ)
    (hu : x 0 ≠ 0) (hv : x 1 ≠ 0) :
    g.denominator x = x 0 * x 1 * (g.kernel x).det := by
  rw [g.kernel_determinant, compressionKernel_determinant _ _ _ _ _ _ hu hv]
  unfold denominator
  field_simp [hu, hv]
  ring

theorem numerator_eq_kernel_adjugate (x : Fin 2 → ℝ)
    (hu : x 0 ≠ 0) (hv : x 1 ≠ 0) :
    g.numerator x = x 0 * x 1 *
      (kernelSecond g.k g.b g.c (x 0) (x 1) * (g.image x 0) ^ 2 +
        2 * g.c * g.image x 0 * g.image x 1 +
        kernelFirst g.k g.a g.c (x 0) (x 1) * (g.image x 1) ^ 2) := by
  unfold numerator kernelFirst kernelSecond
  field_simp [hu, hv]

theorem functional_inverse_quadratic (x : Fin 2 → ℝ)
    (hu : x 0 ≠ 0) (hv : x 1 ≠ 0) :
    g.functional x = dotProduct (g.image x) ((g.kernel x)⁻¹ *ᵥ g.image x) := by
  have hinv : dotProduct (g.image x) ((g.kernel x)⁻¹ *ᵥ g.image x) =
      (kernelSecond g.k g.b g.c (x 0) (x 1) * (g.image x 0) ^ 2 +
        2 * g.c * g.image x 0 * g.image x 1 +
        kernelFirst g.k g.a g.c (x 0) (x 1) * (g.image x 1) ^ 2) / (g.kernel x).det := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two]
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
    simp only [kernel, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [hinv, functional, g.numerator_eq_kernel_adjugate x hu hv,
    g.denominator_eq_kernel_determinant x hu hv,
    mul_div_mul_left _ _ (mul_ne_zero hu hv)]

theorem functional_first_axis (u : ℝ) (hk : g.k ≠ 0) (ha : g.a ≠ 0)
    (hc : g.c ≠ 0) (hbeta : g.k + 1 ≠ 0) :
    g.functional ![u, 0] = u ^ 2 * g.z1 ^ 2 / (g.k * g.a) := by
  by_cases hu : u = 0
  · subst u
    simp [functional, numerator, denominator, image]
  · have hbeta' : 1 + g.k ≠ 0 := by simpa only [add_comm] using hbeta
    simp only [functional, numerator, denominator, image, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_zero, zero_mul, add_zero, zero_add, zero_pow (by decide : 2 ≠ 0)]
    field_simp [hk, ha, hc, hu, hbeta, hbeta']

theorem functional_second_axis (v : ℝ) (hk : g.k ≠ 0) (hb : g.b ≠ 0)
    (hc : g.c ≠ 0) (hbeta : g.k + 1 ≠ 0) :
    g.functional ![0, v] = v ^ 2 * g.z2 ^ 2 / (g.k * g.b) := by
  by_cases hv : v = 0
  · subst v
    simp [functional, numerator, denominator, image]
  · have hbeta' : 1 + g.k ≠ 0 := by simpa only [add_comm] using hbeta
    simp only [functional, numerator, denominator, image, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_zero, zero_mul, add_zero, zero_add, zero_pow (by decide : 2 ≠ 0)]
    field_simp [hk, hb, hc, hv, hbeta, hbeta']

theorem denominator_upper (x : Fin 2 → ℝ) (hk : 0 < g.k) (ha : 0 < g.a)
    (hb : 0 < g.b) (hc : 0 < g.c) (hu : 0 ≤ x 0) (hv : 0 ≤ x 1)
    (hx : 0 < x 0 ∨ 0 < x 1) : 0 < g.denominator x := by
  have hbeta : 0 < g.k + 1 := by linarith
  rcases hx with hx | hx
  · have hfirst : 0 < (g.k + 1) * g.a * g.c * x 0 ^ 2 := by positivity
    have hmiddle : 0 ≤ (g.k * g.a * g.b + (g.k + 2) * g.c ^ 2) * x 0 * x 1 := by positivity
    have hlast : 0 ≤ (g.k + 1) * g.b * g.c * x 1 ^ 2 := by positivity
    unfold denominator
    apply mul_pos hk
    linarith
  · have hfirst : 0 ≤ (g.k + 1) * g.a * g.c * x 0 ^ 2 := by positivity
    have hmiddle : 0 ≤ (g.k * g.a * g.b + (g.k + 2) * g.c ^ 2) * x 0 * x 1 := by positivity
    have hlast : 0 < (g.k + 1) * g.b * g.c * x 1 ^ 2 := by positivity
    unfold denominator
    apply mul_pos hk
    linarith

theorem denominator_lower (x : Fin 2 → ℝ) (hk1 : -1 < g.k) (hk : g.k < 0)
    (ha : 0 < g.a) (hb : 0 < g.b) (hc : g.c < 0) (hdet : g.c ^ 2 < g.a * g.b)
    (hu : 0 ≤ x 0) (hv : 0 ≤ x 1) (hx : 0 < x 0 ∨ 0 < x 1) : 0 < g.denominator x := by
  have hbeta : 0 < g.k + 1 := by linarith
  have hkc : 0 < g.k * g.c := mul_pos_of_neg_of_neg hk hc
  by_cases hu0 : x 0 = 0
  · have hvp : 0 < x 1 := by
      rcases hx with h | h
      · rw [hu0] at h
        linarith
      · exact h
    have hid : g.denominator x = (g.k * g.c) * (g.k + 1) * g.b * x 1 ^ 2 := by
      unfold denominator
      rw [hu0]
      ring
    rw [hid]
    positivity
  by_cases hv0 : x 1 = 0
  · have hup : 0 < x 0 := lt_of_le_of_ne hu (Ne.symm hu0)
    have hid : g.denominator x = (g.k * g.c) * (g.k + 1) * g.a * x 0 ^ 2 := by
      unfold denominator
      rw [hv0]
      ring
    rw [hid]
    positivity
  have hup : 0 < x 0 := lt_of_le_of_ne hu (Ne.symm hu0)
  have hvp : 0 < x 1 := lt_of_le_of_ne hv (Ne.symm hv0)
  rw [g.denominator_eq_kernel_determinant x hu0 hv0, g.kernel_determinant]
  exact mul_pos (mul_pos hup hvp) (compressionKernel_lower hk1 hk ha hb hc hdet hup hvp).2

end RayParameters

end

end ResearchMain.DiagonalSchatten
