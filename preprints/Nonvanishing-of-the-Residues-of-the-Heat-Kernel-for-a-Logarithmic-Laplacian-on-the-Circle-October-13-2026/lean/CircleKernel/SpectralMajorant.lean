import CircleKernel.DirichletExponential

noncomputable section
open Filter Asymptotics Finset
open scoped Topology
namespace CircleKernel

theorem spectralRemainderTerm_bound (M : ℕ) (hM : 0 < M) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C ≥ 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t : ℂ, ‖t‖ ≤ R → ∀ σ : ℝ, σ ≤ t.re →
      ‖spectralRemainderTerm M n t‖ ≤ C*(n : ℝ)^(-2*σ-(M : ℝ)) := by
  obtain ⟨B,hB,N,hrem⟩ := uniform_normalized_spectral_remainder M hM R hR
  let E := Real.exp (|spectralConstant| * R)
  have hE : 0 ≤ E := Real.exp_nonneg _
  refine ⟨E*B,mul_nonneg hE hB,max N 1,?_⟩
  intro n hn t ht σ hσ
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hc : ‖Complex.exp (-(spectralConstant : ℂ)*t)‖ ≤ E := by
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
  have hd : ‖dirichletExponential n (2*t)‖ ≤ (n : ℝ)^(-2*σ) := by
    have h := dirichletExponential_norm_le n hn1 (2*t) (2*σ) (by
      norm_num [Complex.mul_re]
      linarith)
    simpa only [neg_mul] using h
  rw [spectralRemainderTerm, norm_mul, norm_mul]
  calc
    _ ≤ (E*(n : ℝ)^(-2*σ)) * (B/(n : ℝ)^M) :=
      mul_le_mul (mul_le_mul hc hd (norm_nonneg _) hE) (hrem n hnN t ht)
        (norm_nonneg _) (mul_nonneg hE (Real.rpow_nonneg (le_of_lt hn0) _))
    _ = (E*B)*(n : ℝ)^(-2*σ-(M : ℝ)) := by
      rw [sub_eq_add_neg, Real.rpow_add hn0, Real.rpow_neg (le_of_lt hn0), Real.rpow_natCast]
      ring

end CircleKernel
