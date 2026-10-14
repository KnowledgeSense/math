import SumsetRanges.LargeDenseStep

open Finset Polynomial
namespace SumsetRanges
open scoped Classical

@[simp] theorem restrictedWeight_zero (c b : ℕ) : restrictedWeight c b 0=1 := by
  simp [restrictedWeight]
@[simp] theorem restrictedWeight_one (c b : ℕ) : restrictedWeight c b 1=c+b := by
  simp [restrictedWeight]

theorem restrictedWeight_nonneg (c b D : ℕ) : 0≤restrictedWeight c b D := by
  unfold restrictedWeight
  split_ifs <;> positivity

theorem choose_le_parameter_mul_previous (c D : ℕ) (hD : 1≤D) :
    c.choose D≤c*c.choose (D-1) := by
  have hr := Nat.choose_succ_right_eq c (D-1)
  have hd : D-1+1=D := by omega
  rw [hd] at hr
  have h1 := Nat.le_mul_of_pos_left (c.choose D) hD
  have h2 := Nat.mul_le_mul_right (c.choose (D-1)) (Nat.sub_le c (D-1))
  nlinarith

theorem restrictedWeight_previous (c b D : ℕ) (hD : 2≤D) :
    restrictedWeight c b D≤(c : ℤ)*restrictedWeight c b (D-1) := by
  have h0 : D≠0 := by omega
  have h1 : D-1≠0 := by omega
  simp only [restrictedWeight,ite_eq_right h0,ite_eq_right h1]
  have ha : (c.choose D : ℤ)≤(c : ℤ)*(c.choose (D-1) : ℤ) := by
    exact_mod_cast choose_le_parameter_mul_previous c D (by omega)
  have hb : (c.choose (D-1) : ℤ)≤(c : ℤ)*(c.choose (D-1-1) : ℤ) := by
    exact_mod_cast choose_le_parameter_mul_previous c (D-1) (by omega)
  have hm := mul_le_mul_of_nonneg_left hb (Int.natCast_nonneg b)
  nlinarith

theorem restrictedWeight_adjacent (h c b μ : ℕ) (hm : μ<h) :
    restrictedWeight c b (h-μ)≤((c+b : ℕ) : ℤ)*restrictedWeight c b (h-(μ+1)) := by
  by_cases he : h-μ=1
  · have he' : h-(μ+1)=0 := by omega
    simp [he,he',Nat.cast_add]
  · have hD : 2≤h-μ := by omega
    have hsub : h-(μ+1)=h-μ-1 := by omega
    rw [hsub]
    have hh := restrictedWeight_previous c b (h-μ) hD
    have hn := restrictedWeight_nonneg c b (h-μ-1)
    have hb' : (0 : ℤ)≤b := Int.natCast_nonneg b
    push_cast
    nlinarith

theorem largeValue_top_linear_step (h c b x : ℕ) (r u : ℕ → ℕ)
    (hh : 2≤h) (hn : nonfreeSize h r u+2*h≤c) :
    largeValue h c b r u x-largeValue h c b (Function.update r h (r h+1)) u x=1 := by
  have he := coefficient_step_product _ _ _ (restrictedPolynomial (denseSet (b-1) x)) h h
    (le_refl h) (sparse_linear_step_factored h c h r u (by simp; omega) hn)
  change largeValue h c b r u x-largeValue h c b (Function.update r h (r h+1)) u x=_ at he
  simpa only [Nat.sub_self,Polynomial.mul_coeff_zero,linearStepRemainder_constant,
    restrictedPolynomial_constant,mul_one] using he

end SumsetRanges
