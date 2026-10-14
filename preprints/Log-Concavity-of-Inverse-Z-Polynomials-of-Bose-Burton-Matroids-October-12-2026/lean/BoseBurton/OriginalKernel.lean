import BoseBurton.KernelDuality
import BoseBurton.KernelSupport

noncomputable section
namespace BoseBurton
open Finset Polynomial

/-- The projective inverse-Z row in the source q-parameter. -/
def projectiveRow (q : ℝ) (n : ℕ) : Polynomial ℝ :=
  C (q^(n.choose 2))*gaussianRow q⁻¹ n

/-- Literal unnormalized source kernel, including the top/empty quotient. -/
def originalSignedKernel (q : ℝ) (r s : ℕ) : Polynomial ℝ :=
  projectiveRow q r+
    ∑ h∈Icc 1 s,∑ l∈range (min h (r-h)+1),
      C ((-1:ℝ)^(h+l)*gaussian q s h*gaussian q (r-h) l)*
      orientationPolynomial h l*projectiveRow q (r-h-l)

theorem originalSignedKernel_normalization (q : ℝ) (hq : 1<q)
    (r s : ℕ) (hsr : s≤r) :
    originalSignedKernel q r s=C (q^(r.choose 2))*signedKernel q⁻¹ r s := by
  unfold originalSignedKernel signedKernel
  rw [mul_add,mul_sum]
  congr 1
  apply sum_congr rfl
  intro h hh
  rw [mul_sum]
  apply sum_congr rfl
  intro l hl
  have hhs := (mem_Icc.mp hh).2
  have hhl : h+l≤r := by simp only [mem_range] at hl; omega
  unfold projectiveRow
  calc
    _ = C ((-1:ℝ)^(h+l)*(gaussian q s h*gaussian q (r-h) l*q^((r-h-l).choose 2)))*
        orientationPolynomial h l*gaussianRow q⁻¹ (r-h-l) := by simp only [map_mul]; ring
    _ = _ := by
      rw [kernel_scalar_dual q hq r s h l hsr hhs hhl]
      simp only [map_mul]
      ring

theorem originalSignedKernel_coeff (q : ℝ) (hq : 1<q)
    (r s k : ℕ) (hsr : s<r) :
    (originalSignedKernel q r s).coeff k=q^(r.choose 2)*scalarCoefficient q⁻¹ r s k := by
  have hq0 : 0<q := by linarith
  rw [originalSignedKernel_normalization q hq r s hsr.le,coeff_C_mul,
    signedKernel_coeff_eq q⁻¹ (inv_nonneg.mpr hq0.le) ((inv_lt_one₀ hq0).mpr hq) r s k hsr]

end BoseBurton
