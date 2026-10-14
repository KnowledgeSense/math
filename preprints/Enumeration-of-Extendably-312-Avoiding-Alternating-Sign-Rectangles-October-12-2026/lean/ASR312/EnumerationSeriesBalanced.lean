import ASR312.EnumerationSeriesWidth
import ASR312.SeriesChangeOfVariable

namespace ASR312

open PowerSeries

theorem coeff_U_succ_parameter (a n : ℕ) : coeff n (U (a+1)) = ((a+n).choose n : ℚ) := by
  simp only [U,invOneSubPow,coeff_mk]
  congr 1
  have hh := Nat.choose_symm (show a ≤ a+n by omega)
  have he : a+n-a = n := by omega
  rw [he] at hh
  exact hh.symm

theorem T_balanced_coefficient (a n : ℕ) :
    coeff n (T (a+1) 0) = ∑ h : Fin (n+1), coeff h.val (U (a+1)) * coeff (n-h.val) (T 0 h.val) := by
  simp only [coeff_T,Nat.add_zero]
  rw [S_balanced_recurrence (n+(a+1)) n (by omega)]
  push_cast
  rw [← (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (n+1))) (fun q : Fin (n+1) =>
    (S q.val n q.val : ℚ) * (((n+(a+1)-q.val-1).choose (n-q.val)) : ℚ)))]
  apply Finset.sum_congr rfl
  intro h _
  simp only [Fin.revPerm_apply,Fin.val_rev,coeff_U_succ_parameter]
  have hh := h.isLt
  have he1 : n-h.val+h.val = n := by omega
  have he2 : n+(a+1)-(n-h.val)-1 = a+h.val := by omega
  have he3 : n-(n-h.val) = h.val := by omega
  have he0 : n+1-(h.val+1) = n-h.val := by omega
  rw [he0,he1,he2,he3,mul_comm]

theorem coeff_mul_as_fin (f g : PowerSeries ℚ) (n : ℕ) :
    coeff n (f*g) = ∑ h : Fin (n+1), coeff h.val f * coeff (n-h.val) g := by
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact (Fin.sum_univ_eq_sum_range (fun h => coeff h f * coeff (n-h) g) (n+1)).symm

theorem coeff_subst_XR_mul_P (f : PowerSeries ℚ) (n : ℕ) :
    coeff n (f.subst (X*R)*P) =
      ∑ h : Fin (n+1), coeff h.val f * coeff (n-h.val) (R^h.val*P) := by
  rw [coeff_substitution_weight]
  rw [← Fin.sum_univ_eq_sum_range (fun h => coeff h f * coeff n ((X*R)^h*P)) (n+1)]
  apply Finset.sum_congr rfl
  intro h _
  have he : (X*R)^h.val*P = X^h.val*(R^h.val*P) := by rw [mul_pow,mul_assoc]
  rw [he,coeff_X_pow_mul',ite_eq_left (by omega)]

theorem coeff_balanced_expression (f : PowerSeries ℚ) (n : ℕ) :
    coeff n (P*(f+f.subst (X*R))) =
      ∑ h : Fin (n+1), coeff h.val f * coeff (n-h.val) (T 0 h.val) := by
  rw [mul_add,map_add,mul_comm P f,mul_comm P (f.subst (X*R)),coeff_mul_as_fin,coeff_subst_XR_mul_P,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  rw [T_row_complete,mul_add,mul_one,map_add,mul_comm P (R^h.val)]
  ring

theorem T_balanced_positive (a : ℕ) : T (a+1) 0 = P*(U (a+1)+(U (a+1)).subst (X*R)) := by
  ext n
  rw [T_balanced_coefficient,coeff_balanced_expression]

theorem T_balanced_series (a : ℕ) : T a 0 = P*(U a+(U a).subst (X*R)) := by
  cases a with
  | zero =>
    have hsub : HasSubst (X*R) := HasSubst.X'.mul_left
    have hs : (1 : PowerSeries ℚ).subst (X*R) = 1 := by
      simpa only [coe_substAlgHom] using (map_one (substAlgHom hsub))
    rw [U_zero,hs,T_square,← two_mul_P]
    ring
  | succ a => exact T_balanced_positive a

end ASR312
