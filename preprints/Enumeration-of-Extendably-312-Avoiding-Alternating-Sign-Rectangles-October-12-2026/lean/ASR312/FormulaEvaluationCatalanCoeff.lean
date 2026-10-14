import ASR312.FormulaEvaluationCatalan
import ASR312.FormulaEvaluationBinomial
import ASR312.SeriesChangeOfVariable

noncomputable section
open PowerSeries Finset
open scoped BigOperators
namespace ASR312

def catalanEvenIndexSeries : PowerSeries ℚ := mk (fun j => (catalan (2*j):ℚ))

@[simp] theorem catalanEvenIndexSeries_coeff (j : ℕ) :
    coeff j catalanEvenIndexSeries=(catalan (2*j):ℚ) := by simp [catalanEvenIndexSeries]

theorem evenCatalanSeries_square_subst :
    evenCatalanSeries=catalanEvenIndexSeries.subst (X^2) := by
  ext n
  rw [evenCatalanSeries_coeff,coeff_subst_X_pow (by norm_num : (2:ℕ) ≠ 0),
    catalanEvenIndexSeries_coeff]
  obtain ⟨k,rfl|rfl⟩ := Nat.even_or_odd' n
  · simp
  · simp

theorem evenCatalanSeries_subst_square (t : PowerSeries ℚ) (ht : constantCoeff t=0) :
    evenCatalanSeries.subst t=catalanEvenIndexSeries.subst (t^2) := by
  have hs : HasSubst t := HasSubst.of_constantCoeff_zero' ht
  have hx : HasSubst ((X:PowerSeries ℚ)^2) := HasSubst.of_constantCoeff_zero' (by simp)
  rw [evenCatalanSeries_square_subst,subst_comp_subst_apply hx hs,subst_pow hs,subst_X hs]

theorem catalan_monomial_weight (r : ℤ) (j : ℕ) :
    (X*(X*(1+X)^2):PowerSeries ℚ)^j*(X*B r)=X^(2*j+1)*B (r+2*j) := by
  have hb : B (r+2*j) = B r*(1+X)^(2*j) := by
    rw [show r+2*(j:ℤ)=r+((2*j:ℕ):ℤ) by push_cast; ring,B_add,B_nat]
  rw [hb,mul_pow,mul_pow,← pow_mul]
  rw [pow_add,pow_one,pow_mul]
  ring

theorem catalan_product_coeff (r : ℤ) (d : ℕ) :
    coeff d (X*B r*evenCatalanSeries.subst (X*(1+X))) =
      ∑ j ∈ range d, (catalan (2*j):ℚ)*
        (generalizedBinomial (r+2*j) ((d:ℤ)-1-2*j):ℚ) := by
  have ht : constantCoeff (X*(1+X):PowerSeries ℚ)=0 := by simp
  rw [evenCatalanSeries_subst_square _ ht]
  have he : ((X*(1+X):PowerSeries ℚ)^2)=X*(X*(1+X)^2) := by ring
  rw [he,mul_comm (X*B r),coeff_substitution_weight]
  simp only [catalanEvenIndexSeries_coeff]
  have hm (j : ℕ) : coeff d ((X*(X*(1+X)^2):PowerSeries ℚ)^j*(X*B r)) =
      (generalizedBinomial (r+2*j) ((d:ℤ)-1-2*j):ℚ) := by
    rw [catalan_monomial_weight,coeff_shift_B]
    congr 2
    push_cast
    ring
  simp_rw [hm]
  rw [sum_range_succ]
  have hz : generalizedBinomial (r+2*d) ((d:ℤ)-1-2*d)=0 := by
    unfold generalizedBinomial
    rw [ite_eq_left (by omega)]
  rw [hz,Int.cast_zero,mul_zero,add_zero]

end ASR312
