import Dowling.JointlessActualCoefficientsWeighted

noncomputable section
namespace Dowling
open PowerSeries Finset

def binomialProductSeries (a : ℝ) : PowerSeries (Polynomial ℝ) :=
  dowlingBinomialSeries a*(dowlingBinomialSeries a).subst (C Polynomial.X*X)

theorem binomialProductSeries_euler (a : ℝ) :
    X*derivative (binomialProductSeries a)+C (Polynomial.C a)*binomialProductSeries a=
      C (Polynomial.C a)*(1-C Polynomial.X*X^2)*binomialProductSeries (a+1) := by
  simp only [binomialProductSeries,Derivation.leibniz,smul_eq_mul]
  rw [dowlingBinomialSeries_derivative,dowlingBinomialSeries_scaled_derivative]
  linear_combination C (Polynomial.C a)*dowlingBinomialProduct_euler a

theorem quadraticWeightedKernel_euler (v : ℕ→ℝ) (a : ℝ) :
    X*derivative (quadraticWeightedKernel v a)+C (Polynomial.C a)*quadraticWeightedKernel v a=
      quadraticWeightedKernel (fun j => (2*j : ℝ)*v j) a+
      C (Polynomial.C a)*(quadraticWeightedKernel v (a+1)-
        quadraticWeightedKernel (fun j => if j=0 then 0 else v (j-1)) (a+1)) := by
  have h := binomialProductSeries_euler a
  have hd := quadraticWeightSeries_derivative v
  have hs := quadraticWeightSeries_shift v
  change X*derivative (quadraticWeightSeries v*binomialProductSeries a)+
    C (Polynomial.C a)*(quadraticWeightSeries v*binomialProductSeries a)=_
  simp only [Derivation.leibniz,smul_eq_mul]
  change _=quadraticWeightSeries (fun j => (2*j : ℝ)*v j)*binomialProductSeries a+
    C (Polynomial.C a)*(quadraticWeightSeries v*binomialProductSeries (a+1)-
      quadraticWeightSeries (fun j => if j=0 then 0 else v (j-1))*binomialProductSeries (a+1))
  rw [← hd,← hs]
  linear_combination quadraticWeightSeries v*h

theorem quadraticWeightedRow_euler (v : ℕ→ℝ) (a : ℝ) (n k : ℕ) :
    ((n : ℝ)+a)*quadraticWeightedRow v a n k=
      quadraticWeightedRow (fun j => (2*j : ℝ)*v j) a n k+
      a*(quadraticWeightedRow v (a+1) n k-
        quadraticWeightedRow (fun j => if j=0 then 0 else v (j-1)) (a+1) n k) := by
  have h := congrArg (fun f : PowerSeries (Polynomial ℝ) => (coeff n f).coeff k)
    (quadraticWeightedKernel_euler v a)
  rw [map_add,candidate_coeff_X_derivative,coeff_C_mul,map_add,coeff_C_mul,map_sub] at h
  have hn : (n : Polynomial ℝ)=Polynomial.C (n : ℝ) := by simp
  rw [hn] at h
  simp only [Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_C_mul,
    quadraticWeightedKernel_coeff] at h
  linear_combination h

/-- Exponent raising for arbitrary signed quadratic weights at fixed total
rank. Only the finitely supported denominators n+a−2j are divided out. -/
theorem quadraticWeightedRow_raise {a : ℝ} (ha : 0<a) (v : ℕ→ℝ) (n k : ℕ) :
    quadraticWeightedRow v a n k=
      quadraticWeightedRow (fun j => a*(v j/(n+a-2*j)-
        if j=0 then 0 else v (j-1)/(n+a-2*(j-1)))) (a+1) n k := by
  let g : ℕ→ℝ := fun j => v j/(n+a-2*j)
  have h := quadraticWeightedRow_euler g a n k
  by_cases hk : k≤n
  · simp only [quadraticWeightedRow,ite_eq_left hk] at h ⊢
    have hleft : ((n : ℝ)+a)*(∑ j∈range (min k (n-k)+1),g j*dowlingBinomialWeight a (k-j)*dowlingBinomialWeight a (n-k-j))-
        (∑ j∈range (min k (n-k)+1),(2*j : ℝ)*g j*dowlingBinomialWeight a (k-j)*dowlingBinomialWeight a (n-k-j))=
        ∑ j∈range (min k (n-k)+1),v j*dowlingBinomialWeight a (k-j)*dowlingBinomialWeight a (n-k-j) := by
      rw [Finset.mul_sum,← Finset.sum_sub_distrib]
      apply sum_congr rfl
      intro j hj
      have hjn : (2*j : ℝ)≤n := by exact_mod_cast (show 2*j≤n by have := mem_range.mp hj; omega)
      have hd : (n : ℝ)+a-2*j≠0 := by linarith
      dsimp [g]
      field_simp
    rw [← hleft]
    rw [h]
    rw [add_sub_cancel_left,← Finset.sum_sub_distrib,Finset.mul_sum]
    apply sum_congr rfl
    intro j hj
    dsimp [g]
    cases j with
    | zero => simp; ring
    | succ j =>
      simp only [Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel_right,Nat.cast_add,Nat.cast_one]
      ring
  · simp [quadraticWeightedRow,hk]

end Dowling
