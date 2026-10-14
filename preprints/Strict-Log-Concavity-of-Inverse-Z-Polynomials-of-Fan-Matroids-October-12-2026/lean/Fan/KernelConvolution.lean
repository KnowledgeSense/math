import Fan.KernelConvolutionSeries

noncomputable section
open scoped BigOperators
namespace Fan

private theorem imbalance_recurrence_unique (z : ℝ) (P Q : ℕ → PowerSeries ℝ)
    (hbase : P 0=Q 0)
    (hconst : ∀ e,PowerSeries.coeff 0 (P e)=PowerSeries.coeff 0 (Q e))
    (hP : ∀ e,P (e+1)=P e+PowerSeries.X*P (e+2)+PowerSeries.C (z-1)*PowerSeries.X*P (e+1))
    (hQ : ∀ e,Q (e+1)=Q e+PowerSeries.X*Q (e+2)+PowerSeries.C (z-1)*PowerSeries.X*Q (e+1)) :
    ∀ e,P e=Q e := by
  have hcoeff (m : ℕ) : ∀ e,PowerSeries.coeff m (P e)=PowerSeries.coeff m (Q e) := by
    induction m with
    | zero => exact hconst
    | succ m ih =>
      intro e
      induction e with
      | zero => rw [hbase]
      | succ e ihe =>
        have hp := congrArg (PowerSeries.coeff (m+1)) (hP e)
        have hq := congrArg (PowerSeries.coeff (m+1)) (hQ e)
        rw [mul_assoc] at hp hq
        simp only [map_add,PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_C_mul] at hp hq
        rw [ih (e+2),ih (e+1),ihe] at hp
        exact hp.trans hq.symm
  intro e
  exact PowerSeries.ext fun m => hcoeff m e

theorem imbalanceSeries_root (z : ℝ) (e : ℕ) :
    imbalanceSeries z e=imbalanceSeries z 0*rootSeries z^e := by
  apply imbalance_recurrence_unique z (imbalanceSeries z)
    (fun e => imbalanceSeries z 0*rootSeries z^e)
  · simp
  · intro e
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply,imbalanceSeries]
  · exact imbalanceSeries_recurrence z
  · intro e
    have h := rootSeries_equation z
    simp only [pow_succ]
    linear_combination (imbalanceSeries z 0*rootSeries z^e)*h

def convolutionRho (z : ℝ) (j : ℕ) : ℝ := PowerSeries.coeff j (rootSeries z^2)

theorem convolutionRho_pos {z : ℝ} (hz : 0<z) (j : ℕ) : 0<convolutionRho z j := by
  rw [convolutionRho,pow_two,PowerSeries.coeff_mul]
  apply Finset.sum_pos'
  · intro x _
    exact (mul_pos (rootSeries_coeff_pos hz x.1) (rootSeries_coeff_pos hz x.2)).le
  · refine ⟨(0,j),by simp,?_⟩
    exact mul_pos (rootSeries_coeff_pos hz 0) (rootSeries_coeff_pos hz j)

theorem imbalanceSeries_step_two (z : ℝ) (e : ℕ) :
    imbalanceSeries z (e+2)=rootSeries z^2*imbalanceSeries z e := by
  rw [imbalanceSeries_root z (e+2),imbalanceSeries_root z e,pow_add]
  ring

/-- The original fixed-imbalance Delannoy convolution, with a positive common kernel. -/
theorem delannoy_imbalance_convolution (z : ℝ) (e m : ℕ) :
    delannoy z m (m+e+2)=∑ j∈Finset.range (m+1),
      convolutionRho z j*delannoy z (m-j) (m-j+e) := by
  have h := congrArg (PowerSeries.coeff m) (imbalanceSeries_step_two z e)
  rw [PowerSeries.coeff_mul] at h
  simp only [imbalanceSeries_coeff] at h
  change delannoy z m (m+(e+2)) = ∑ x∈Finset.antidiagonal m,
    convolutionRho z x.1*delannoy z x.2 (x.2+e) at h
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun j k => convolutionRho z j*delannoy z k (k+e)) m] at h
  simpa only [Nat.add_assoc] using h

end Fan
