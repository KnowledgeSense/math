import SphericalTreeFailures.LocalLimitMultipliers
import SphericalTreeFailures.NormalizedCharacteristic

namespace SphericalTreeFailures

 theorem phase_shift_identity (x a H t : ℝ) :
    sizeExponential (-x) t * sizeExponential a (t / H) = sizeExponential (-(x - a / H)) t := by
  unfold sizeExponential
  rw [← Complex.exp_add]
  apply congrArg Complex.exp
  push_cast
  ring

theorem forward_kernel_identity (x H t : ℝ) :
    sizeExponential (-x) t * forwardMultiplier H t =
      (H : ℂ) * (sizeExponential (-(x + 1 / H)) t - sizeExponential (-x) t) := by
  have hs := phase_shift_identity x (-1) H t
  have he : -(x - (-1) / H) = -(x + 1 / H) := by ring
  rw [he] at hs
  unfold forwardMultiplier
  calc
    _ = (H : ℂ) * (sizeExponential (-x) t * sizeExponential (-1) (t / H) - sizeExponential (-x) t) := by ring
    _ = _ := by rw [hs]

theorem backward_kernel_identity (x H t : ℝ) :
    sizeExponential (-x) t * backwardMultiplier H t =
      (H : ℂ) * (sizeExponential (-x) t - sizeExponential (-(x - 1 / H)) t) := by
  have hs := phase_shift_identity x 1 H t
  unfold backwardMultiplier
  calc
    _ = (H : ℂ) * (sizeExponential (-x) t - sizeExponential (-x) t * sizeExponential 1 (t / H)) := by ring
    _ = _ := by rw [hs]

theorem second_kernel_identity (x H t : ℝ) :
    sizeExponential (-x) t * secondMultiplier H t =
      (H : ℂ) ^ 2 * (sizeExponential (-(x + 1 / H)) t - 2 * sizeExponential (-x) t +
        sizeExponential (-(x - 1 / H)) t) := by
  have h0 := phase_shift_identity x (-1) H t
  have h1 := phase_shift_identity x 1 H t
  have he : -(x - (-1) / H) = -(x + 1 / H) := by ring
  rw [he] at h0
  rw [secondMultiplier_formula]
  calc
    _ = (H : ℂ) ^ 2 * (sizeExponential (-x) t * sizeExponential (-1) (t / H) -
      2 * sizeExponential (-x) t + sizeExponential (-x) t * sizeExponential 1 (t / H)) := by ring
    _ = _ := by rw [h0, h1]

end SphericalTreeFailures
