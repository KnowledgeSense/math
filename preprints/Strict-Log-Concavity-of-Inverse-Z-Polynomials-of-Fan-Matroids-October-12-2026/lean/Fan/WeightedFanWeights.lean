import Fan.DelannoyContiguous

noncomputable section
namespace Fan

/-- The exact ballot weight in the fan inverse-Z coefficient formula. -/
def ballotWeight (n r : ℕ) : ℝ :=
  if 2*r < n then (((n:ℝ)-2*r)/n)*(n.choose r:ℝ)/4^r else 0

theorem ballotWeight_nonneg (n r : ℕ) : 0 ≤ ballotWeight n r := by
  unfold ballotWeight
  split_ifs with h
  · have hn : (0:ℝ) ≤ n := by positivity
    have hr : (0:ℝ) ≤ (n:ℝ)-2*r := by
      have hh : (2:ℝ)*r < n := by exact_mod_cast h
      linarith
    exact div_nonneg (mul_nonneg (div_nonneg hr hn) (by positivity)) (by positivity)
  · exact le_rfl

theorem ballotWeight_pos {n r : ℕ} (h : 2*r < n) : 0 < ballotWeight n r := by
  rw [ballotWeight,ite_eq_left h]
  have hn : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hr : (0:ℝ) < (n:ℝ)-2*r := by
    have hh : (2:ℝ)*r < n := by exact_mod_cast h
    linarith
  have hc : (0:ℝ) < n.choose r := by exact_mod_cast (Nat.choose_pos (show r≤n by omega))
  positivity

@[simp] theorem ballotWeight_zero (n : ℕ) (hn : 0 < n) : ballotWeight n 0 = 1 := by
  have hne : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [ballotWeight,hn,hne]

theorem ballotWeight_eq_zero {n r : ℕ} (h : n ≤ 2*r) : ballotWeight n r = 0 := by
  simp [ballotWeight,not_lt.mpr h]

theorem ballotWeight_pos_iff (n r : ℕ) : 0 < ballotWeight n r ↔ 2*r < n := by
  constructor
  · intro h
    by_contra hh
    rw [ballotWeight_eq_zero (Nat.le_of_not_gt hh)] at h
    exact (lt_irrefl 0) h
  · exact ballotWeight_pos

/-- Binomial coefficient products increase towards equal indices. -/
theorem choose_pair_mono (n i j : ℕ) (hij : i ≤ j) :
    (n.choose i:ℝ)*n.choose (j+1) ≤ (n.choose (i+1):ℝ)*n.choose j := by
  have hi := choose_real_next n i
  have hj := choose_real_next n j
  push_cast at hi hj
  have hi0 : (0:ℝ) < i+1 := by positivity
  have hj0 : (0:ℝ) < j+1 := by positivity
  have hei : (n.choose (i+1):ℝ) = ((n:ℝ)-i)*n.choose i/((i:ℝ)+1) := by
    apply (eq_div_iff hi0.ne').mpr
    nlinarith only [hi]
  have hej : (n.choose (j+1):ℝ) = ((n:ℝ)-j)*n.choose j/((j:ℝ)+1) := by
    apply (eq_div_iff hj0.ne').mpr
    nlinarith only [hj]
  rw [hei,hej]
  apply (mul_le_mul_iff_left₀ (mul_pos hi0 hj0)).mp
  field_simp
  have hd : (0:ℝ) ≤ (j:ℝ)-i := by
    have hh : (i:ℝ) ≤ j := by exact_mod_cast hij
    linarith
  have hp : 0 ≤ ((j:ℝ)-i)*((n:ℝ)+1)*(n.choose i:ℝ)*n.choose j := by positivity
  nlinarith only [hp]

/-- Adjacent products of the exact ballot weights increase towards the middle. -/
theorem ballotWeight_pair_mono (n i j : ℕ) (hij : i ≤ j) :
    ballotWeight n i * ballotWeight n (j+1) ≤ ballotWeight n (i+1) * ballotWeight n j := by
  by_cases hj : 2*(j+1) < n
  · have hi : 2*i < n := by omega
    have hi1 : 2*(i+1) < n := by omega
    have hj0 : 2*j < n := by omega
    have hn : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
    have hiR : (i:ℝ) ≤ j := by exact_mod_cast hij
    have hjR : (2:ℝ)*((j:ℝ)+1) < n := by exact_mod_cast hj
    have hlin : ((n:ℝ)-2*i)*((n:ℝ)-2*((j:ℝ)+1)) ≤
        ((n:ℝ)-2*((i:ℝ)+1))*((n:ℝ)-2*j) := by nlinarith
    have hchoose := choose_pair_mono n i j hij
    have hproduct := mul_le_mul hlin hchoose (by positivity : (0:ℝ) ≤ (n.choose i:ℝ)*n.choose (j+1))
      (mul_nonneg (by linarith) (by linarith))
    have hden : 0 < (n:ℝ)^2*4^(i+j+1) := by positivity
    have hleft : ballotWeight n i * ballotWeight n (j+1) =
        (((n:ℝ)-2*i)*((n:ℝ)-2*((j:ℝ)+1)))*((n.choose i:ℝ)*n.choose (j+1)) /
          ((n:ℝ)^2*4^(i+j+1)) := by
      rw [ballotWeight,ite_eq_left hi,ballotWeight,ite_eq_left hj]
      push_cast
      simp only [pow_add,pow_succ]
      field_simp
    have hright : ballotWeight n (i+1) * ballotWeight n j =
        (((n:ℝ)-2*((i:ℝ)+1))*((n:ℝ)-2*j))*((n.choose (i+1):ℝ)*n.choose j) /
          ((n:ℝ)^2*4^(i+j+1)) := by
      rw [ballotWeight,ite_eq_left hi1,ballotWeight,ite_eq_left hj0]
      push_cast
      simp only [pow_add,pow_succ]
      field_simp
    rw [hleft,hright]
    exact (div_le_div_iff_of_pos_right hden).mpr hproduct
  · rw [ballotWeight_eq_zero (Nat.le_of_not_gt hj),mul_zero]
    exact mul_nonneg (ballotWeight_nonneg _ _) (ballotWeight_nonneg _ _)

theorem ballotWeight_product_step (n R r : ℕ) (hr : 2*r+2 ≤ R) :
    ballotWeight n r * ballotWeight n (R-r) ≤
      ballotWeight n (r+1) * ballotWeight n (R-r-1) := by
  have h := ballotWeight_pair_mono n r (R-r-1) (by omega)
  simpa only [show R-r-1+1=R-r by omega] using h

theorem ballotWeight_log_concave (n r : ℕ) :
    ballotWeight n r * ballotWeight n (r+2) ≤ (ballotWeight n (r+1))^2 := by
  have h := ballotWeight_pair_mono n r (r+1) (by omega)
  simpa only [pow_two] using h

end Fan
