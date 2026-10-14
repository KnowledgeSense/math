import Dowling.JointlessActualCoefficientsElimination

noncomputable section
namespace Dowling
open PowerSeries Finset

/-- An arbitrary literal sequence on the quadratic parameter t x². -/
def quadraticWeightSeries (v : ℕ→ℝ) : PowerSeries (Polynomial ℝ) :=
  PowerSeries.mk (fun d => if d%2=0 then Polynomial.C (v (d/2))*Polynomial.X^(d/2) else 0)

theorem quadraticWeightSeries_even (v : ℕ→ℝ) (j : ℕ) :
    coeff (2*j) (quadraticWeightSeries v)=Polynomial.C (v j)*Polynomial.X^j := by
  simp [quadraticWeightSeries]

theorem quadraticWeightSeries_odd (v : ℕ→ℝ) (j : ℕ) :
    coeff (2*j+1) (quadraticWeightSeries v)=0 := by
  simp [quadraticWeightSeries]

def quadraticWeightedKernel (v : ℕ→ℝ) (a : ℝ) : PowerSeries (Polynomial ℝ) :=
  quadraticWeightSeries v*(dowlingBinomialSeries a*
    (dowlingBinomialSeries a).subst (C Polynomial.X*X))

def quadraticWeightedRow (v : ℕ→ℝ) (a : ℝ) (n k : ℕ) : ℝ :=
  if k≤n then ∑ j∈range (min k (n-k)+1),v j*dowlingBinomialWeight a (k-j)*
    dowlingBinomialWeight a (n-k-j) else 0

theorem quadraticWeightedKernel_row (v : ℕ→ℝ) (a : ℝ) (n : ℕ) :
    coeff n (quadraticWeightedKernel v a)=
      ∑ j∈range (n/2+1),Polynomial.C (v j)*Polynomial.X^j*dowlingBinomialRow a (n-2*j) := by
  rw [quadraticWeightedKernel,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [dowling_sum_even _ (by intro j; rw [quadraticWeightSeries_odd,zero_mul])]
  apply sum_congr rfl
  intro j hj
  rw [quadraticWeightSeries_even,dowlingBinomialProduct_coeff]

theorem quadraticWeightedKernel_coeff (v : ℕ→ℝ) (a : ℝ) (n k : ℕ) :
    (coeff n (quadraticWeightedKernel v a)).coeff k=quadraticWeightedRow v a n k := by
  rw [quadraticWeightedKernel_row,Polynomial.finsetSum_coeff]
  have hterm (j : ℕ) (hj : j∈range (n/2+1)) :=
    dowlingBinomialRow_shifted_coeff a (v j) n k j (by have := mem_range.mp hj; omega)
  rw [Finset.sum_congr rfl hterm]
  by_cases hk : k≤n
  · rw [quadraticWeightedRow,ite_eq_left hk]
    symm
    calc
      _ = ∑ j∈range (min k (n-k)+1),if j≤k ∧ k+j≤n then
          v j*dowlingBinomialWeight a (k-j)*dowlingBinomialWeight a (n-k-j) else 0 := by
        apply sum_congr rfl
        intro j hj
        rw [ite_eq_left (by have := mem_range.mp hj; omega)]
      _ = _ := by
        apply sum_subset
        · intro j hj
          apply mem_range.mpr
          have := mem_range.mp hj
          omega
        · intro j hj hnot
          rw [ite_eq_right (by have := mem_range.mp hj; simp only [mem_range] at hnot; omega)]
  · rw [quadraticWeightedRow,ite_eq_right hk]
    apply sum_eq_zero
    intro j hj
    rw [ite_eq_right (by omega)]

theorem quadraticWeightSeries_derivative (v : ℕ→ℝ) :
    X*derivative (quadraticWeightSeries v)=quadraticWeightSeries (fun j => (2*j : ℝ)*v j) := by
  apply PowerSeries.ext
  intro d
  rw [candidate_coeff_X_derivative]
  by_cases he : d%2=0
  · rw [show d=2*(d/2) by omega,quadraticWeightSeries_even,quadraticWeightSeries_even]
    simp only [Nat.cast_mul,Nat.cast_ofNat,map_mul,map_ofNat,map_natCast]
    ring
  · rw [show d=2*(d/2)+1 by omega,quadraticWeightSeries_odd,quadraticWeightSeries_odd,mul_zero]

theorem quadraticWeightSeries_shift (v : ℕ→ℝ) :
    C Polynomial.X*X^2*quadraticWeightSeries v=
      quadraticWeightSeries (fun j => if j=0 then 0 else v (j-1)) := by
  apply PowerSeries.ext
  intro d
  rw [mul_assoc,coeff_C_mul,coeff_X_pow_mul']
  by_cases he : d%2=0
  · rw [show d=2*(d/2) by omega,quadraticWeightSeries_even]
    cases h : d/2 with
    | zero => simp
    | succ j =>
      rw [ite_eq_left (by omega),show 2*(j+1)-2=2*j by omega,quadraticWeightSeries_even]
      simp only [Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel_right]
      ring
  · rw [show d=2*(d/2)+1 by omega,quadraticWeightSeries_odd]
    cases h : d/2 with
    | zero => simp
    | succ j =>
      rw [ite_eq_left (by omega),show 2*(j+1)+1-2=2*j+1 by omega,quadraticWeightSeries_odd,mul_zero]

end Dowling
