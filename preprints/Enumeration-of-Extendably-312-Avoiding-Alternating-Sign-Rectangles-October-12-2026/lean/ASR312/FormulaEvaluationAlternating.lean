import ASR312.FormulaEvaluationBinomial

noncomputable section
open PowerSeries Finset
open scoped BigOperators
namespace ASR312

def alternatingTail : PowerSeries ℚ := mk (fun i => if i=0 then 0 else (-1:ℚ)^i)

@[simp] theorem alternatingTail_coeff (i : ℕ) :
    coeff i alternatingTail=if i=0 then 0 else (-1:ℚ)^i := by simp [alternatingTail]

theorem alternatingTail_cancel : alternatingTail*(1+X) = -X := by
  ext n
  rw [mul_add,mul_one,map_add,map_neg]
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_succ_mul_X,alternatingTail_coeff,alternatingTail_coeff]
    cases n with
    | zero => norm_num
    | succ n => simp [pow_add,coeff_X]

theorem B_step (r : ℤ) : B (r+1)=B r*(1+X) := by
  rw [B_add]
  have h : B (1:ℤ)=(1+X:PowerSeries ℚ) := by simpa using B_nat 1
  rw [h]

theorem alternatingTail_mul_B (r : ℤ) : alternatingTail*B r = -X*B (r-1) := by
  have hb : B r=B (r-1)*(1+X) := by simpa using B_step (r-1)
  rw [hb]
  calc
    _ = (alternatingTail*(1+X))*B (r-1) := by ring
    _ = _ := by rw [alternatingTail_cancel]

theorem coeff_product_zero_constant (f g : PowerSeries ℚ) (hf : coeff 0 f=0) (n : ℕ) :
    coeff n (f*g)=∑ i ∈ Icc 1 n, coeff i f*coeff (n-i) g := by
  rw [coeff_product_range]
  symm
  apply sum_subset
  · intro i hi
    have := mem_Icc.mp hi
    exact mem_range.mpr (by omega)
  · intro i hi hnot
    have hi0 : i=0 := by
      have := mem_range.mp hi
      simp only [mem_Icc,not_and] at hnot
      omega
    subst i
    simp [hf]

theorem alternatingTail_binomial_coeff (r d : ℕ) :
    coeff d (alternatingTail*B r) =
      ∑ i ∈ Icc 1 d, (-1:ℚ)^i*(r.choose (d-i):ℚ) := by
  rw [coeff_product_zero_constant _ _ (by simp)]
  apply sum_congr rfl
  intro i hi
  have hi0 : i ≠ 0 := by have := mem_Icc.mp hi; omega
  rw [alternatingTail_coeff,ite_eq_right hi0,coeff_B,Ring.choose_natCast]
  norm_cast

end ASR312
