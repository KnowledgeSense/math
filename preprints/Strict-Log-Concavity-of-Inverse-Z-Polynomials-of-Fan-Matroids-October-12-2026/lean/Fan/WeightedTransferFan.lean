import Fan.WeightedTransfer
import Fan.WeightedFanWeights

noncomputable section
open scoped BigOperators
namespace Fan

theorem weightedKernel_formula (z : ℝ) (n k : ℕ) (hk : k ≤ n) (x : ℕ → ℝ) :
    weightedKernel z n k x=
      ∑ r∈Finset.range (min k (n-k)+1),x r*delannoy z (k-r) (n-k-r) := by
  unfold weightedKernel
  rw [← Finset.sum_range (fun r => kernelEntry z n k r*x r)]
  have hm : min k (n-k) ≤ n := (min_le_left _ _).trans hk
  have he : (∑ r∈Finset.range (n+1),kernelEntry z n k r*x r)=
      ∑ r∈Finset.range (min k (n-k)+1),kernelEntry z n k r*x r := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro r _ hr
    have hnot : ¬(r ≤ k ∧ k+r ≤ n) := by
      simp only [Finset.mem_range,not_lt] at hr
      omega
    simp only [kernelEntry,ite_eq_right hnot,zero_mul]
  rw [he]
  apply Finset.sum_congr rfl
  intro r hr
  have hmem : r ≤ k ∧ k+r ≤ n := by have := Finset.mem_range.mp hr; omega
  simp only [kernelEntry,ite_eq_left hmem,mul_comm]

/-- The exact ballot-weight coefficient formula; rank zero has the source's unit convention. -/
def fanCoefficient (n k : ℕ) : ℝ :=
  if n=0 then (if k=0 then 1 else 0) else
    2^(n-1)*weightedKernel (1/2) n k (ballotWeight n)

theorem fanCoefficient_eq_weighted (n k : ℕ) (hn : 0<n) :
    fanCoefficient n k=2^(n-1)*weightedKernel (1/2) n k (ballotWeight n) := by
  simp only [fanCoefficient,ite_eq_right (Nat.ne_of_gt hn)]

theorem fanCoefficient_formula (n k : ℕ) (hn : 0<n) (hk : k ≤ n) :
    fanCoefficient n k=2^(n-1)*
      ∑ r∈Finset.range (min k (n-k)+1),ballotWeight n r*delannoy (1/2) (k-r) (n-k-r) := by
  rw [fanCoefficient_eq_weighted n k hn,weightedKernel_formula (1/2) n k hk]

theorem fanCoefficient_pos (n k : ℕ) (hn : 0<n) (hk : k ≤ n) : 0<fanCoefficient n k := by
  rw [fanCoefficient_eq_weighted n k hn]
  apply mul_pos (by positivity)
  apply weightedKernel_pos (1/2) (by norm_num) n k hk (ballotWeight n) (ballotWeight_nonneg n)
  rw [ballotWeight_zero n hn]
  exact zero_lt_one

theorem fanCoefficient_symm (n k : ℕ) (hn : 0<n) (hk : k ≤ n) :
    fanCoefficient n (n-k)=fanCoefficient n k := by
  rw [fanCoefficient_eq_weighted n (n-k) hn,fanCoefficient_eq_weighted n k hn,
    weightedKernel_symm (1/2) n k hk]

theorem fanCoefficient_strict_log_concave (n k : ℕ) (hn : 0<n) (hk : 1 ≤ k) (hkn : k<n) :
    fanCoefficient n (k-1)*fanCoefficient n (k+1)<fanCoefficient n k^2 := by
  have hx0 : 0<ballotWeight n 0 := by rw [ballotWeight_zero n hn]; exact zero_lt_one
  have h := weightedKernel_strict_log_concave (1/2) (by norm_num) n k hk hkn
    (ballotWeight n) (ballotWeight_nonneg n) hx0 (ballotWeight_product_step n)
  rw [fanCoefficient_eq_weighted n (k-1) hn,fanCoefficient_eq_weighted n (k+1) hn,
    fanCoefficient_eq_weighted n k hn]
  have hp : 0<(2:ℝ)^(n-1) := by positivity
  nlinarith [mul_pos (sq_pos_of_pos hp) (sub_pos.mpr h)]

theorem fanCoefficient_rank_zero (k : ℕ) : fanCoefficient 0 k=if k=0 then 1 else 0 := by
  simp [fanCoefficient]

theorem fanCoefficient_rank_one_zero : fanCoefficient 1 0=1 := by
  rw [fanCoefficient_formula 1 0 (by decide) (by decide)]
  norm_num [ballotWeight]

theorem fanCoefficient_rank_one_one : fanCoefficient 1 1=1 := by
  have h := fanCoefficient_symm 1 0 (by decide) (by decide)
  simpa only [Nat.sub_zero,fanCoefficient_rank_one_zero] using h

theorem fanCoefficient_outside (n k : ℕ) (hn : 0<n) (hk : n<k) : fanCoefficient n k=0 := by
  rw [fanCoefficient_eq_weighted n k hn]
  have he : weightedKernel (1/2) n k (ballotWeight n)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : ¬(i.val ≤ k ∧ k+i.val ≤ n) := by omega
    simp only [kernelEntry,ite_eq_right hi,zero_mul]
  rw [he,mul_zero]

end Fan
