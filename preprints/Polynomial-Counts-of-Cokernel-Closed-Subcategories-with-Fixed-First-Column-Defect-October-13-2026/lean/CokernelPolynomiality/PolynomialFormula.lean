import CokernelPolynomiality.PointCounting
import CokernelPolynomiality.TopTemplateCount
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.FieldSimp

namespace CokernelPolynomiality
noncomputable section
open Polynomial

 def shiftedFalling (i q : ℕ) : Polynomial ℚ :=
  (descPochhammer ℚ q).comp (X + C (1 - (i : ℚ)))

 theorem shiftedFalling_degree (i q : ℕ) : (shiftedFalling i q).natDegree = q := by
  rw [shiftedFalling,natDegree_comp,descPochhammer_natDegree,natDegree_X_add_C,mul_one]

 theorem shiftedFalling_monic (i q : ℕ) : (shiftedFalling i q).Monic := by
  unfold shiftedFalling
  exact (monic_descPochhammer ℚ q).comp (monic_X_add_C _) (by rw [natDegree_X_add_C]; omega)

 def defectPolynomial (i : ℕ) : Polynomial ℚ :=
  ∑ q : Fin (2*i+1), C ((templateCount i q : ℚ) / (q.val.factorial : ℚ)) * shiftedFalling i q

 theorem defectPolynomial_eval (i n : ℕ) (hi : i ≤ n+1) :
    (defectPolynomial i).eval (n : ℚ) = (r n (n+1-i) : ℚ) := by
  rw [r_binomial_formula n i (n+1-i) (by omega)]
  simp only [defectPolynomial,eval_finsetSum,eval_mul,eval_C,Nat.cast_sum,Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro q _
  have hm : (n : ℚ) + (1-(i:ℚ)) = ((n+1-i : ℕ):ℚ) := by
    rw [Nat.cast_sub hi,Nat.cast_add,Nat.cast_one]
    ring
  simp only [shiftedFalling,eval_comp,eval_add,eval_X,eval_C,hm]
  rw [Nat.cast_choose_eq_descPochhammer_div]
  ring

 theorem defectPolynomial_degree_le (i : ℕ) : (defectPolynomial i).natDegree ≤ 2*i := by
  apply natDegree_sum_le_of_forall_le
  intro q _
  exact (natDegree_C_mul_le _ _).trans ((shiftedFalling_degree i q).le.trans (by omega))

 theorem shiftedFalling_top_coeff (i q : ℕ) : (shiftedFalling i q).coeff q = 1 := by
  have hh := (shiftedFalling i q).coeff_natDegree
  rw [shiftedFalling_degree] at hh
  exact hh.trans (shiftedFalling_monic i q)

 theorem defectPolynomial_top_coeff (i : ℕ) :
    (defectPolynomial i).coeff (2*i) = (i.factorial : ℚ)⁻¹ := by
  classical
  unfold defectPolynomial
  rw [finsetSum_coeff]
  rw [Finset.sum_eq_single (⟨2*i,by omega⟩ : Fin (2*i+1))]
  · rw [coeff_C_mul,shiftedFalling_top_coeff,mul_one,top_template_count]
    have hf := Nat.factorial_mul_descFactorial (show i ≤ 2*i by omega)
    have he : 2*i-i = i := by omega
    rw [he] at hf
    have hq : (i.factorial : ℚ) * ((2*i).descFactorial i : ℚ) = ((2*i).factorial : ℚ) := by
      exact_mod_cast hf
    have hi0 : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    have h20 : ((2*i).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*i)
    apply (div_eq_iff h20).mpr
    calc
      ((2*i).descFactorial i : ℚ) = (i.factorial : ℚ)⁻¹ *
          ((i.factorial : ℚ) * ((2*i).descFactorial i : ℚ)) := by field_simp
      _ = _ := by rw [hq]
  · intro q _ hq
    rw [coeff_C_mul,coeff_eq_zero_of_natDegree_lt,mul_zero]
    rw [shiftedFalling_degree]
    have hn : q.val ≠ 2*i := fun h => hq (Fin.ext h)
    omega
  · simp

 theorem fixedDefectPolynomiality : FixedDefectPolynomiality := by
  intro i
  refine ⟨defectPolynomial i,fun n hn => (defectPolynomial_eval i n hn).symm,?_,defectPolynomial_top_coeff i⟩
  apply natDegree_eq_of_le_of_coeff_ne_zero (defectPolynomial_degree_le i)
  rw [defectPolynomial_top_coeff]
  exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero i)

end
end CokernelPolynomiality
