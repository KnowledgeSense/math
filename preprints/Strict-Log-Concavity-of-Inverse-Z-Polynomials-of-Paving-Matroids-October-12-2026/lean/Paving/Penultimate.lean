import Paving.ScalarPayment

noncomputable section
namespace Paving

def middleIncrement (C N m : ℝ) : ℝ := C*(N-m+1)/(N*(N+1))
def penultimateRatio (N m : ℝ) : ℝ := (m-1)*(N+1)/(m*(N+2))
def penultimateFloor (C N m : ℝ) : ℝ := C*m*(N-m+1)/((N+1)*(N+m+1))

theorem penultimateRatio_nonneg {N m : ℝ} (hm : 1 ≤ m) (hN : m ≤ N) :
    0 ≤ penultimateRatio N m := by
  unfold penultimateRatio
  have : 0 ≤ m-1 := by linarith
  have : 0 ≤ N+1 := by linarith
  have : 0 ≤ N+2 := by linarith
  positivity

theorem penultimateRatio_lt_one {N m : ℝ} (hm : 1 ≤ m) (hN : m ≤ N) :
    penultimateRatio N m < 1 := by
  have hm0 : 0 < m := by linarith
  have hN2 : 0 < N+2 := by linarith
  unfold penultimateRatio
  apply (div_lt_one (mul_pos hm0 hN2)).mpr
  nlinarith

theorem middleIncrement_positive {C N m : ℝ} (hC : 0 < C) (hm : 1 ≤ m) (hN : m ≤ N) :
    0 < middleIncrement C N m := by
  unfold middleIncrement
  have : 0 < N-m+1 := by linarith
  have : 0 < N := by linarith
  have : 0 < N+1 := by linarith
  positivity

theorem penultimateFloor_positive {C N m : ℝ} (hC : 0 < C) (hm : 1 ≤ m) (hN : m ≤ N) :
    0 < penultimateFloor C N m := by
  unfold penultimateFloor
  have : 0 < m := by linarith
  have : 0 < N-m+1 := by linarith
  have : 0 < N+1 := by linarith
  have : 0 < N+m+1 := by linarith
  positivity

theorem penultimate_reserve_identity {C N m : ℝ} (hm : 1 ≤ m) (hN : m ≤ N) :
    (1-penultimateRatio N m)*penultimateFloor C N m-
      penultimateRatio N m*middleIncrement C N m =
      C*(N-m+1)^2/(m*N*(N+1)*(N+2)) := by
  have hm0 : m≠0 := by linarith
  have hN0 : N≠0 := by linarith
  have hN1 : N+1≠0 := by linarith
  have hN2 : N+2≠0 := by linarith
  have hNm : N+m+1≠0 := by linarith
  unfold penultimateRatio penultimateFloor middleIncrement
  field_simp
  ring

/-- The strict penultimate inequality follows from the actual-weight lower bound. -/
theorem penultimate_strict {C N m p q : ℝ} (hC : 0 < C) (hm : 1 ≤ m) (hN : m ≤ N)
    (hp : penultimateFloor C N m ≤ p) (hq : q < penultimateRatio N m*p) :
    q*(p+middleIncrement C N m) < p^2 := by
  have hf := penultimateFloor_positive hC hm hN
  have hp0 : 0 < p := lt_of_lt_of_le hf hp
  have hd := middleIncrement_positive hC hm hN
  have he := penultimateRatio_lt_one hm hN
  have hmul := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1-penultimateRatio N m by linarith)
  have hid := penultimate_reserve_identity (C:=C) hm hN
  have hreserve : 0 < C*(N-m+1)^2/(m*N*(N+1)*(N+2)) := by
    have : 0 < N-m+1 := by linarith
    have : 0 < m := by linarith
    have : 0 < N := by linarith
    have : 0 < N+1 := by linarith
    have : 0 < N+2 := by linarith
    positivity
  have hpaid : 0 < (1-penultimateRatio N m)*p-penultimateRatio N m*middleIncrement C N m := by
    linarith
  have hstrict := mul_lt_mul_of_pos_right hq (show 0 < p+middleIncrement C N m by linarith)
  have hpositive := mul_pos hp0 hpaid
  nlinarith

end Paving
