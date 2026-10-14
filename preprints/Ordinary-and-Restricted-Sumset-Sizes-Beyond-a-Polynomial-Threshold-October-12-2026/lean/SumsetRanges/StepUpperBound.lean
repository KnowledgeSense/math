import SumsetRanges.CoefficientOrder

open Finset Polynomial
namespace SumsetRanges

theorem coeffLE_refl (P : Polynomial ℤ) : CoeffLE P P := fun _ => le_rfl

theorem coeffLE_sum {ι : Type*} (s : Finset ι) (f g : ι → Polynomial ℤ)
    (h : ∀ i∈s,CoeffLE (f i) (g i)) : CoeffLE (∑ i∈s,f i) (∑ i∈s,g i) := by
  intro q
  simp only [finsetSum_coeff]
  exact Finset.sum_le_sum (fun i hi => h i hi q)

theorem coeffLE_natCast_mul {P : Polynomial ℤ} (hP : CoeffNonneg P) (n : ℕ) (hn : 1 ≤ n) :
    CoeffLE P ((n : Polynomial ℤ)*P) := by
  intro q
  rw [coeff_natCast_mul]
  have hn' : (1:ℤ)≤n := by exact_mod_cast hn
  nlinarith [hP q]

theorem coeffLE_natCast {n r : ℕ} (h : n≤r) : CoeffLE (n : Polynomial ℤ) (r : Polynomial ℤ) := by
  intro q
  simp only [coeff_natCast_ite]
  split
  · exact_mod_cast h
  · rfl

theorem ambiguityPolynomial_nonneg (m r : ℕ) : CoeffNonneg (ambiguityPolynomial m r) :=
  coeffNonneg_sum _ _ (fun _l _ => coeffNonneg_X_pow _)

theorem ambiguityPolynomial_le (m r : ℕ) (hm : 2 ≤ m) :
    CoeffLE (ambiguityPolynomial m r) ((X+X^(m-1))^r) := by
  rw [add_comm X (X^(m-1)),add_pow]
  unfold ambiguityPolynomial
  apply coeffLE_sum
  intro l hl
  have hle : l≤r := Nat.le_of_lt_succ (mem_range.mp hl)
  have he : (X^(m-1))^l*X^(r-l) = (X : Polynomial ℤ)^(r+l*(m-2)) := by
    rw [← pow_mul,← pow_add]
    congr 1
    have hm' : m-1=(m-2)+1 := by omega
    rw [hm']
    have hs := Nat.sub_add_cancel hle
    nlinarith
  rw [he,mul_comm _ (r.choose l : Polynomial ℤ)]
  exact coeffLE_natCast_mul (coeffNonneg_X_pow _) _ (Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt (Nat.choose_pos hle)))

theorem ambiguityPolynomial_factor (m r : ℕ) :
    ambiguityPolynomial m r = X^r*(∑ l∈range (r+1),X^(l*(m-2))) := by
  unfold ambiguityPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [pow_add]

theorem sharedBlock_step_factored (m u : ℕ) (hm : 2 ≤ m) :
    (1+X)^m*sharedBlockPolynomial m u-sharedBlockPolynomial m (u+1) =
      X^m*(∑ j∈range u,(u.choose (j+1) : Polynomial ℤ)*(rowPolynomial m)^(u-1-j)*ambiguityPolynomial m j) := by
  rw [sharedBlock_step m u hm,Finset.sum_range_succ']
  simp only [Finset.range_zero,Finset.sum_empty,mul_zero,add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [ambiguityPolynomial_factor]
  rw [show m+(j+1)-1=m+j by omega,show u-(j+1)=u-1-j by omega,pow_add]
  ring

/-- The coefficientwise upper estimate for each shared-atom parameter step. -/
theorem sharedBlock_step_upper (m u : ℕ) (hm : 2 ≤ m) (hu : 1 ≤ u) :
    CoeffLE ((1+X)^m*sharedBlockPolynomial m u-sharedBlockPolynomial m (u+1))
      ((u : Polynomial ℤ)*X^m*(1+X)^(m*(u-1))) := by
  rw [sharedBlock_step_factored m u hm]
  have hid : (u : Polynomial ℤ)*X^m*(1+X)^(m*(u-1)) =
      X^m*(∑ j∈range u,((u*(u-1).choose j : ℕ) : Polynomial ℤ)*
        (rowPolynomial m)^(u-1-j)*(X+X^(m-1))^j) := by
    rw [pow_mul,show (1+X)^m = rowPolynomial m+(X+X^(m-1)) by
      rw [rowPolynomial_eq m hm]; ring]
    rw [add_comm (rowPolynomial m),add_pow,show u-1+1=u by omega]
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  rw [hid]
  refine coeffLE_mul (coeffNonneg_X_pow _) ?_ (coeffLE_refl _) ?_
  · exact coeffNonneg_sum _ _ (fun j _ => coeffNonneg_mul
      (coeffNonneg_mul (coeffNonneg_natCast _) (coeffNonneg_pow (coeffNonneg_rowPolynomial m) _))
      (coeffNonneg_pow (coeffNonneg_add (by simpa using coeffNonneg_X_pow 1) (coeffNonneg_X_pow _)) _))
  · apply coeffLE_sum
    intro j hj
    have hc : u.choose (j+1) ≤ u*(u-1).choose j := by
      have he := Nat.add_one_mul_choose_eq (u-1) j
      rw [show u-1+1=u by omega] at he
      nlinarith
    apply coeffLE_mul
    · exact coeffNonneg_mul (coeffNonneg_natCast _) (coeffNonneg_pow (coeffNonneg_rowPolynomial m) _)
    · exact coeffNonneg_pow (coeffNonneg_add (by simpa using coeffNonneg_X_pow 1) (coeffNonneg_X_pow _)) _
    · exact coeffLE_mul (coeffNonneg_natCast _) (coeffNonneg_pow (coeffNonneg_rowPolynomial m) _)
        (coeffLE_natCast hc) (coeffLE_refl _)
    · exact ambiguityPolynomial_le m j hm

end SumsetRanges
