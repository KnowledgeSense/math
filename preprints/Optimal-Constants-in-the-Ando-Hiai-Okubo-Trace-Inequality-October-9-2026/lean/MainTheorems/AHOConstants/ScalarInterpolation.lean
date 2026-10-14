import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace ResearchMain.AHOConstants

theorem square_interpolation_power {s D r : ℝ} (hs : 0 ≤ s) (hsq : s ^ 2 = D) :
    s ^ (2 * r) = D ^ r := by
  have h := Real.rpow_mul hs (2 : ℝ) r
  simpa only [Real.rpow_two, hsq] using h

theorem trace_interpolation_scalar {T D s t r : ℝ}
    (hT : 0 < T) (hD : 0 < D) (hs : 0 ≤ s) (ht : 0 ≤ t) (hr : 0 < r)
    (hsq : s ^ 2 = D) (htq : t ^ 2 = T)
    (h : T ≤ T ^ (1 - 2 * r) * (s * t) ^ (2 * r)) : T ≤ D := by
  rw [Real.mul_rpow hs ht, square_interpolation_power hs hsq,
    square_interpolation_power ht htq] at h
  have hcombine : T ^ (1 - 2 * r) * (D ^ r * T ^ r) = T ^ (1 - r) * D ^ r := by
    calc
      T ^ (1 - 2 * r) * (D ^ r * T ^ r) =
          (T ^ (1 - 2 * r) * T ^ r) * D ^ r := by ring
      _ = T ^ ((1 - 2 * r) + r) * D ^ r := by rw [← Real.rpow_add hT]
      _ = T ^ (1 - r) * D ^ r := by congr 2; ring
  rw [hcombine] at h
  have hfac : 0 < T ^ (1 - r) := Real.rpow_pos_of_pos hT _
  have hsplit : T ^ r * T ^ (1 - r) = T := by
    rw [← Real.rpow_add hT, show r + (1 - r) = 1 by ring, Real.rpow_one]
  have hp : T ^ r * T ^ (1 - r) ≤ D ^ r * T ^ (1 - r) := by
    rw [hsplit]
    simpa only [mul_comm] using h
  have hp' := le_of_mul_le_mul_right hp hfac
  exact (Real.rpow_le_rpow_iff hT.le hD.le hr).mp hp'

end ResearchMain.AHOConstants
