import Fan.KernelConvolutionRecurrence

noncomputable section
open scoped BigOperators
namespace Fan

def excursionCoeff (z : ℝ) : ℕ → ℝ
  | 0 => 0
  | m+1 => (if m=0 then z else 0)+(z+1)*excursionCoeff z m+
      ∑ j : Fin (m+1),excursionCoeff z j*excursionCoeff z (m-j)

@[simp] theorem excursionCoeff_zero (z : ℝ) : excursionCoeff z 0=0 := by rw [excursionCoeff]

theorem excursionCoeff_succ (z : ℝ) (m : ℕ) :
    excursionCoeff z (m+1) = (if m=0 then z else 0)+(z+1)*excursionCoeff z m+
      ∑ j : Fin (m+1),excursionCoeff z j*excursionCoeff z (m-j) := by rw [excursionCoeff]

theorem excursionCoeff_nonneg {z : ℝ} (hz : 0≤z) (m : ℕ) : 0≤excursionCoeff z m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => simp
    | succ m =>
      rw [excursionCoeff_succ]
      apply add_nonneg
      · apply add_nonneg
        · split_ifs <;> positivity
        · exact mul_nonneg (by linarith) (ih m (by omega))
      · exact Finset.sum_nonneg fun j _ => mul_nonneg (ih j j.isLt) (ih (m-j) (by omega))

theorem excursionCoeff_pos {z : ℝ} (hz : 0<z) (m : ℕ) : 0<excursionCoeff z (m+1) := by
  induction m with
  | zero => simp [excursionCoeff_succ,hz]
  | succ m ih =>
    rw [excursionCoeff_succ]
    apply add_pos_of_pos_of_nonneg
    · simp only [Nat.succ_ne_zero,ite_false,zero_add]
      exact mul_pos (by linarith) ih
    · exact Finset.sum_nonneg fun j _ =>
        mul_nonneg (excursionCoeff_nonneg hz.le _) (excursionCoeff_nonneg hz.le _)

def excursionSeries (z : ℝ) : PowerSeries ℝ := PowerSeries.mk (excursionCoeff z)
def rootSeries (z : ℝ) : PowerSeries ℝ := 1+excursionSeries z

@[simp] theorem excursionSeries_coeff (z : ℝ) (m : ℕ) :
    PowerSeries.coeff m (excursionSeries z)=excursionCoeff z m := by simp [excursionSeries]

@[simp] theorem excursionSeries_constant (z : ℝ) :
    PowerSeries.constantCoeff (excursionSeries z)=0 := by simp [excursionSeries]

@[simp] theorem rootSeries_constant (z : ℝ) :
    PowerSeries.constantCoeff (rootSeries z)=1 := by simp [rootSeries]

theorem rootSeries_coeff_pos {z : ℝ} (hz : 0<z) (m : ℕ) :
    0<PowerSeries.coeff m (rootSeries z) := by
  cases m with
  | zero => simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply,rootSeries_constant] using zero_lt_one
  | succ m => simpa [rootSeries] using excursionCoeff_pos hz m

theorem excursionSeries_equation (z : ℝ) :
    excursionSeries z=PowerSeries.X*(PowerSeries.C z+
      PowerSeries.C (z+1)*excursionSeries z+excursionSeries z^2) := by
  ext m
  cases m with
  | zero => simp
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul]
    rw [map_add,map_add]
    rw [PowerSeries.coeff_C_mul]
    simp only [excursionSeries_coeff,PowerSeries.coeff_C,pow_two,PowerSeries.coeff_mul,
      excursionCoeff_succ]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => excursionCoeff z i*excursionCoeff z j) m,Finset.sum_range]

theorem rootSeries_equation (z : ℝ) :
    rootSeries z = 1+PowerSeries.X*rootSeries z*(rootSeries z+PowerSeries.C (z-1)) := by
  have h := excursionSeries_equation z
  have hc : PowerSeries.C (z+1) = PowerSeries.C z+1 := by simp
  have hd : PowerSeries.C (z-1) = PowerSeries.C z-1 := by simp
  rw [hc] at h
  rw [hd]
  unfold rootSeries
  linear_combination h

end Fan
