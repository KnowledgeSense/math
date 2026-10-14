import Dowling.LabeledColorCounts

noncomputable section
namespace Dowling
open scoped Classical
open Finset PowerSeries
variable {I : Type*} [Fintype I]

 def labeledColorSeries (f : ℕ → Polynomial ℝ) : PowerSeries (Polynomial ℝ) :=
  mk fun n => Polynomial.C ((n.factorial : ℝ)⁻¹)*f n

 def labeledColorProduct (f : I → ℕ → Polynomial ℝ) : PowerSeries (Polynomial ℝ) :=
  ∏ c : I, labeledColorSeries (f c)

@[simp] theorem labeledColorSeries_coeff (f : ℕ → Polynomial ℝ) (n : ℕ) :
    coeff n (labeledColorSeries f)=Polynomial.C ((n.factorial : ℝ)⁻¹)*f n := coeff_mk _ _

 theorem derivative_labeledColorSeries (f : ℕ → Polynomial ℝ) :
    derivative (labeledColorSeries f)=labeledColorSeries (fun n => f (n+1)) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_derivative,labeledColorSeries_coeff,labeledColorSeries_coeff]
  have hs : ((n+1).factorial : ℝ)⁻¹*(n+1 : ℝ)=(n.factorial : ℝ)⁻¹ := by
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_inv_rev]
    rw [mul_assoc,inv_mul_cancel₀ (by positivity),mul_one]
  have hc := congrArg (Polynomial.C : ℝ → Polynomial ℝ) hs
  simp only [map_mul,map_add,map_natCast,map_one] at hc
  linear_combination f (n+1)*hc

 theorem candidate_derivative_product {R : Type*} [CommRing R] {J : Type*} (s : Finset J)
    (f : J → PowerSeries R) :
    derivative (∏ d ∈ s, f d)=∑ c ∈ s, ∏ d ∈ s, if d=c then derivative (f d) else f d := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [prod_insert ha]
    have hD := (derivative (R := R)).leibniz (f a) (∏ d ∈ s, f d)
    rw [hD,ih,sum_insert ha]
    simp only [smul_eq_mul]
    have hnew : (∏ d ∈ insert a s, if d=a then derivative (f d) else f d)=
        derivative (f a)*∏ d ∈ s, f d := by
      rw [prod_insert ha,ite_eq_left rfl]
      congr 1
      apply prod_congr rfl
      intro d hd
      exact ite_eq_right (by intro h; subst d; exact ha hd)
    have hold (c : J) (hc : c∈s) :
        (∏ d ∈ insert a s, if d=c then derivative (f d) else f d)=
          f a*∏ d ∈ s, if d=c then derivative (f d) else f d := by
      rw [prod_insert ha,ite_eq_right (by intro h; subst c; exact ha hc)]
    rw [hnew]
    have hsum : (∑ c ∈ s, ∏ d ∈ insert a s, if d=c then derivative (f d) else f d)=
        f a*∑ c ∈ s, ∏ d ∈ s, if d=c then derivative (f d) else f d := by
      rw [mul_sum]
      exact sum_congr rfl hold
    rw [hsum]
    ring

 theorem derivative_labeledColorProduct (f : I → ℕ → Polynomial ℝ) :
    derivative (labeledColorProduct f)=∑ c : I, labeledColorProduct (labeledColorShift f c) := by
  rw [labeledColorProduct,candidate_derivative_product]
  apply sum_congr rfl
  intro c _
  apply prod_congr rfl
  intro d _
  by_cases h : d=c
  · rw [ite_eq_left h,derivative_labeledColorSeries]
    congr 1
    funext n
    simp [labeledColorShift,h]
  · rw [ite_eq_right h]
    congr 1
    funext n
    simp [labeledColorShift,h]

 theorem labeledColorProduct_constant (f : I → ℕ → Polynomial ℝ) :
    coeff 0 (labeledColorProduct f)=∏ c : I, f c 0 := by
  rw [coeff_zero_eq_constantCoeff_apply,labeledColorProduct,map_prod]
  apply prod_congr rfl
  intro c _
  rw [← coeff_zero_eq_constantCoeff_apply,labeledColorSeries_coeff]
  norm_num

end Dowling
