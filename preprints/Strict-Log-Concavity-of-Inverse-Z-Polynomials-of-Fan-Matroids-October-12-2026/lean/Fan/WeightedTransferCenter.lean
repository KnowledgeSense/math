import Fan.WeightedTransferTail

noncomputable section
open scoped BigOperators
namespace Fan

theorem delannoyMean_eval_pos (z : ℝ) (hz : 0 ≤ z) (a b : ℕ) :
    0<(delannoyMeanPolynomial a b).eval z := by
  simp only [delannoyMeanPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial]
  apply Finset.sum_pos'
  · intro i _
    positivity
  · refine ⟨0,by simp,?_⟩
    norm_num

theorem delannoy_balance_difference (z : ℝ) (a b : ℕ) :
    delannoy z (a+1) b-delannoy z a (b+1)=
      ((b:ℝ)-a)*z*(delannoyMeanPolynomial a b).eval z := by
  have h1 := congrArg (Polynomial.eval z) (delannoy_raise_left a b)
  have h2 := congrArg (Polynomial.eval z) (delannoy_raise_left b a)
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_one,
    Polynomial.eval_X,Polynomial.eval_C,delannoyPolynomial_eval] at h1 h2
  rw [delannoy_symm z (b+1) a,delannoy_symm z b a,delannoyMeanPolynomial_symm b a] at h2
  push_cast at h1 h2
  linarith

theorem delannoy_balance_lt (z : ℝ) (hz : 0<z) (a b : ℕ) (hab : a<b) :
    delannoy z a (b+1)<delannoy z (a+1) b := by
  apply sub_pos.mp
  rw [delannoy_balance_difference]
  exact mul_pos (mul_pos (sub_pos.mpr (by exact_mod_cast hab)) hz) (delannoyMean_eval_pos z hz.le a b)

theorem kernelEntry_nonneg (z : ℝ) (hz : 0 ≤ z) (n k r : ℕ) :
    0 ≤ kernelEntry z n k r := by
  unfold kernelEntry
  split_ifs
  · exact (delannoy_pos hz _ _).le
  · exact le_rfl

theorem kernelEntry_symm (z : ℝ) (n k r : ℕ) (hk : k ≤ n) :
    kernelEntry z n (n-k) r=kernelEntry z n k r := by
  unfold kernelEntry
  have he : r ≤ n-k ∧ n-k+r ≤ n ↔ r ≤ k ∧ k+r ≤ n := by omega
  simp only [he]
  split_ifs
  · rw [Nat.sub_sub_self hk,delannoy_symm]
  · rfl

theorem kernelEntry_towards_center (z : ℝ) (hz : 0<z) (n k r : ℕ) (hk : 2*k+2 ≤ n) :
    kernelEntry z n k r ≤ kernelEntry z n (k+1) r := by
  by_cases hr : r ≤ k
  · have h0 : r ≤ k ∧ k+r ≤ n := by omega
    have h1 : r ≤ k+1 ∧ k+1+r ≤ n := by omega
    simp only [kernelEntry,h0,h1]
    have he1 : n-k-r=(n-k-1-r)+1 := by omega
    have he2 : k+1-r=(k-r)+1 := by omega
    have he3 : n-(k+1)-r=n-k-1-r := by omega
    rw [he1,he2,he3]
    exact (delannoy_balance_lt z hz (k-r) (n-k-1-r) (by omega)).le
  · have h0 : kernelEntry z n k r=0 := by simp only [kernelEntry,hr,false_and,ite_false]
    rw [h0]
    exact kernelEntry_nonneg z hz.le n (k+1) r

theorem kernelEntry_center_zero_strict (z : ℝ) (hz : 0<z) (n k : ℕ) (hk : 2*k+2 ≤ n) :
    kernelEntry z n k 0<kernelEntry z n (k+1) 0 := by
  have h0 : 0 ≤ k ∧ k+0 ≤ n := by omega
  have h1 : 0 ≤ k+1 ∧ k+1+0 ≤ n := by omega
  simp only [kernelEntry,h0,h1,Nat.sub_zero]
  have he : n-k=(n-(k+1))+1 := by omega
  rw [he]
  exact delannoy_balance_lt z hz k (n-(k+1)) (by omega)

end Fan
