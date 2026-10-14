import SphericalTreeFailures.GraphLatticeMass
import SphericalTreeFailures.NormalizedCharacteristic

namespace SphericalTreeFailures

noncomputable def centeredGraphCharacteristic (m k : ℕ) (activity u H t : ℝ) : ℂ :=
  sizeExponential (-u) (t / H) * totalCharacteristic m k activity (t / H)

 theorem centeredGraph_kernel (m k : ℕ) (activity u H t : ℝ) (j : ℤ) :
    sizeExponential (-((j : ℝ) - u) / H) t * centeredGraphCharacteristic m k activity u H t =
      sizeExponential (-j : ℝ) (t / H) * totalCharacteristic m k activity (t / H) := by
  unfold centeredGraphCharacteristic
  rw [← mul_assoc]
  congr 1
  unfold sizeExponential
  rw [← Complex.exp_add]
  apply congrArg Complex.exp
  push_cast
  ring

theorem graphLatticeMass_scaled_inversion (m k : ℕ) (activity : ℝ) (ha : 0 < activity)
    (u H : ℝ) (hH : H ≠ 0) (j : ℤ) :
    (∫ t : ℝ in -(Real.pi * H)..Real.pi * H,
      sizeExponential (-((j : ℝ) - u) / H) t * centeredGraphCharacteristic m k activity u H t) =
        ((2 * Real.pi : ℝ) : ℂ) * ((H * graphLatticeMass m k activity ha j : ℝ) : ℂ) := by
  simp_rw [centeredGraph_kernel]
  have h := intervalIntegral.integral_comp_div
    (fun t => sizeExponential (-j : ℝ) t * totalCharacteristic m k activity t)
    (a := -(Real.pi * H)) (b := Real.pi * H) hH
  rw [show -(Real.pi * H) / H = -Real.pi by field_simp,
    mul_div_cancel_right₀ Real.pi hH, graphLatticeMass_inversion m k activity ha j] at h
  rw [h]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring

end SphericalTreeFailures
