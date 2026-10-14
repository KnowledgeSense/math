import ASR312.BalancedRecurrence
import Mathlib.RingTheory.PowerSeries.Schroder
import Mathlib.RingTheory.PowerSeries.Inverse

namespace ASR312

open PowerSeries

noncomputable def R : PowerSeries ℚ := PowerSeries.mk (fun n => (Nat.largeSchroder n : ℚ))
noncomputable def P : PowerSeries ℚ := C (1/2) * (1 + X * R)

@[simp] theorem coeff_R (n : ℕ) : coeff n R = (Nat.largeSchroder n : ℚ) := by simp [R]
@[simp] theorem constantCoeff_R : constantCoeff R = 1 := by simp [← coeff_zero_eq_constantCoeff_apply]

theorem R_eq_map : R = PowerSeries.map (Nat.castRingHom ℚ) largeSchroderSeries := by
  ext n
  simp

theorem R_quadratic : R = 1 + X * R + X * R^2 := by
  have hh := congrArg (PowerSeries.map (Nat.castRingHom ℚ))
    largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq
  simpa only [map_add,map_mul,map_one,map_pow,map_X,← R_eq_map] using hh

theorem R_mul_kernel : R * (1-X-X*R) = 1 := by
  have hh := R_quadratic
  linear_combination hh

theorem kernel_mul_R : (1-X-X*R) * R = 1 := by rw [mul_comm,R_mul_kernel]

theorem one_sub_XR_mul_one_add_R : (1-X*R)*(1+R) = 2 := by
  have hh := R_quadratic
  linear_combination hh

theorem C_half_mul_two : (C (1/2) : PowerSeries ℚ) * 2 = 1 := by
  have htwo : (2 : PowerSeries ℚ) = C (2 : ℚ) := (map_ofNat C 2).symm
  rw [htwo,← map_mul]
  norm_num

theorem P_mul_one_add_R : P * (1+R) = R := by
  calc
    P*(1+R) = (C (1/2) * 2)*R := by
      unfold P
      have hh := R_quadratic
      linear_combination -(C (1/2) : PowerSeries ℚ) * hh
    _ = R := by rw [C_half_mul_two,one_mul]

theorem P_sub_RP : P-R*P = -X*R^2 := by
  have h1 := P_mul_one_add_R
  have h2 := R_quadratic
  have h3 : 2*P = 1+X*R := by
    unfold P
    calc
      2*(C (1/2)*(1+X*R)) = (C (1/2)*2)*(1+X*R) := by ring
      _ = 1+X*R := by rw [C_half_mul_two,one_mul]
  linear_combination h3 - h1 - h2

@[simp] theorem constantCoeff_P : constantCoeff P = 1/2 := by simp [P]

theorem isUnit_R : IsUnit R := by
  exact ⟨⟨R,1-X-X*R,R_mul_kernel,kernel_mul_R⟩,rfl⟩

theorem isUnit_one_sub_XR : IsUnit (1-X*R : PowerSeries ℚ) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  simp

theorem isUnit_one_add_R : IsUnit (1+R : PowerSeries ℚ) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  norm_num

end ASR312
