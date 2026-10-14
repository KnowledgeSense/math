import ASR312.EnumerationSeriesDefinitions

namespace ASR312

open PowerSeries

 theorem S_pivot_recurrence_rat (r k d : ℕ) (hdr : d+1 ≤ r) (hdk : d+1 ≤ k+1)
    (hface : d+1 < k+1 ∨ r ≤ k+1) :
    (S r (k+1) (d+1) : ℚ) = (S r k (d+1) : ℚ) + (S (r-1) k d : ℚ) +
      ∑ p : Fin d, (Nat.largeSchroder p.val : ℚ) *
        ((S (r-(p.val+1)) (k+1-(p.val+1)) (d+1-(p.val+1)) : ℚ) -
          ((r-(p.val+1)-1).choose (d+1-(p.val+1)) : ℚ)) := by
  rw [S_pivot_recurrence r k d hdr hdk hface]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [Nat.cast_sub]
  have hdim : r-(p.val+1)-1+1 = r-(p.val+1) := by have hp := p.isLt; omega
  have hh := emptyFirstRow_count_le_S (r-(p.val+1)-1) (k+1-(p.val+1)) (d+1-(p.val+1)) (by omega)
  simpa only [hdim,Nat.add_sub_add_right] using hh

theorem T_coefficient_recurrence (a b d : ℕ) :
    coeff (d+1) (T a (b+1)) = coeff (d+1) (T a b) + coeff d (T a (b+1)) +
      ∑ p : Fin d, coeff p.val R * (coeff (d-p.val) (T a (b+1)) - coeff (d-p.val) (U a)) := by
  simp only [coeff_T,coeff_R]
  have hh := S_pivot_recurrence_rat (d+1+a) (d+b+1) d (by omega) (by omega)
    (Or.inl (by omega))
  have hr : d+1+a-1 = d+a := by omega
  have hk : d+b+1+1 = d+1+(b+1) := by omega
  have hk' : d+b+1 = d+1+b := by omega
  rw [hr,hk] at hh
  rw [show d+(b+1) = d+b+1 by omega]
  rw [hh,hk']
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  have hp := p.isLt
  rw [coeff_U_pos a (d-p.val) (by omega)]
  have h1 : d+1+a-(p.val+1) = d-p.val+a := by omega
  have h2 : d+1+(b+1)-(p.val+1) = d-p.val+(b+1) := by omega
  have h3 : d+1-(p.val+1) = d-p.val := by omega
  simp only [h1,h2,h3,Nat.add_comm a (d-p.val)]

theorem coeff_R_mul_T_sub_U (a b d : ℕ) :
    coeff d (R*(T a b-U a)) =
      ∑ p : Fin d, coeff p.val R * (coeff (d-p.val) (T a b) - coeff (d-p.val) (U a)) := by
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [map_sub]
  rw [Finset.sum_range_succ]
  have hz : coeff d R * (coeff (d-d) (T a b) - coeff (d-d) (U a)) = 0 := by
    simp only [Nat.sub_self,coeff_zero_eq_constantCoeff_apply,constantCoeff_T,constantCoeff_U,sub_self,mul_zero]
  rw [hz,add_zero]
  exact (Fin.sum_univ_eq_sum_range (fun x => coeff x R * (coeff (d-x) (T a b)-coeff (d-x) (U a))) d).symm

theorem T_series_recurrence (a b : ℕ) :
    T a (b+1) = T a b + X*T a (b+1) + X*(R*(T a (b+1)-U a)) := by
  ext n
  cases n with
  | zero => simp only [coeff_zero_eq_constantCoeff_apply,map_add,map_mul,constantCoeff_X,zero_mul,add_zero,constantCoeff_T]
  | succ n =>
    simp only [map_add,coeff_succ_X_mul,coeff_R_mul_T_sub_U]
    exact T_coefficient_recurrence a b n

theorem T_kernel_recurrence (a b : ℕ) :
    (1-X-X*R)*T a (b+1) = T a b-X*R*U a := by
  have hh := T_series_recurrence a b
  linear_combination hh

theorem T_width_recurrence (a b : ℕ) : T a (b+1) = R*T a b-X*R^2*U a := by
  have hh := congrArg (fun F : PowerSeries ℚ => R*F) (T_kernel_recurrence a b)
  rw [← mul_assoc,R_mul_kernel,one_mul] at hh
  linear_combination hh

end ASR312
