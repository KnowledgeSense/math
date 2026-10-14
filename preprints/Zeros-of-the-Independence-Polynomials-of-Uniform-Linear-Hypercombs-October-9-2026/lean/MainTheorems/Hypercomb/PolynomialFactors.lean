import MainTheorems.Hypercomb.Sector
import MainTheorems.Hypercomb.Coefficients

namespace ResearchMain.Hypercomb

open Polynomial

def RootsInLeftCone (p : ℝ[X]) : Prop := ∀ z : ℂ, aeval z p = 0 → LeftCone z

theorem RootsInLeftCone.of_factor {p L q : ℝ[X]} (hp : RootsInLeftCone p) (he : p = L * q) :
    RootsInLeftCone q := by
  intro z hz
  apply hp z
  rw [he, map_mul, hz, mul_zero]

theorem normalized_factor_quotient {p L q : ℝ[X]} (hp : p.coeff 0 = 1)
    (he : p = L * q) (ht : L.coeff 0 ≠ 0) (hdeg : 0 < L.natDegree) :
    let t := L.coeff 0
    let Q := C t * q
    Q.coeff 0 = 1 ∧ p = (C t⁻¹ * L) * Q ∧ Q.natDegree < p.natDegree := by
  dsimp only
  have hpne : p ≠ 0 := by intro h; rw [h, coeff_zero] at hp; norm_num at hp
  have hLne : L ≠ 0 := by intro h; rw [h, coeff_zero] at ht; exact ht rfl
  have hqne : q ≠ 0 := by intro h; rw [h, mul_zero] at he; exact hpne he
  have hcoeff : L.coeff 0 * q.coeff 0 = 1 := by rw [he, mul_coeff_zero] at hp; exact hp
  have hprod : (C (L.coeff 0)⁻¹ * L) * (C (L.coeff 0) * q) = L * q := by
    calc
      _ = (C (L.coeff 0)⁻¹ * C (L.coeff 0)) * (L * q) := by ring
      _ = L * q := by rw [← C_mul, inv_mul_cancel₀ ht, map_one, one_mul]
  refine ⟨by simpa using hcoeff, he.trans hprod.symm, ?_⟩
  rw [natDegree_C_mul ht, he, natDegree_mul hLne hqne]
  omega

theorem normalize_linear {r : ℝ} (hr : r < 0) :
    C ((X - C r : ℝ[X]).coeff 0)⁻¹ * (X - C r) = 1 + C (-r⁻¹) * X := by
  simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, inv_neg, mul_sub,
    ← C_mul, neg_mul, map_neg]
  rw [inv_mul_cancel₀ (ne_of_lt hr), map_one]
  ring

theorem normalize_quadratic {z : ℂ} (hz : z ≠ 0) :
    let P : ℝ[X] := X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)
    C (P.coeff 0)⁻¹ * P =
      1 + C (-2 * z.re / ‖z‖ ^ 2) * X + C (‖z‖ ^ 2)⁻¹ * X ^ 2 := by
  dsimp only
  have hnorm : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_mul_X_zero, coeff_C_zero,
    ite_eq_right (by decide : ¬0 = 2), zero_sub, neg_zero, zero_add]
  rw [mul_add, mul_sub, ← C_mul, inv_mul_cancel₀ hnorm, map_one]
  have hcoef : (C (-2 * z.re / ‖z‖ ^ 2) : ℝ[X]) = -(C (‖z‖ ^ 2)⁻¹ * C (2 * z.re)) := by
    simp only [div_eq_mul_inv, map_mul, map_neg, map_ofNat]
    ring
  rw [hcoef]
  ring

end ResearchMain.Hypercomb
