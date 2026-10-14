import CircleKernel.HarmonicAsymptotic
import CircleKernel.HarmonicEigenvalues
import CircleResidues.Definitions

noncomputable section
open Filter Asymptotics Finset
open scoped Topology
namespace CircleKernel

theorem sourceCoefficient_cast_succ (j : ℕ) :
    (CircleResidues.sourceCoefficient (j+1) : ℝ) =
      (2-4/(2 : ℝ)^(j+1)) * (bernoulli (j+1) : ℝ)/(j+1) := by
  unfold CircleResidues.sourceCoefficient
  rw [show (1 : ℤ)-((j+1 : ℕ) : ℤ) = -(j : ℤ) by omega,
    zpow_neg, zpow_natCast]
  push_cast
  rw [pow_succ]
  field_simp
  ring

def eigenvalueError (M n : ℕ) : ℝ :=
  circleEigenvalue n-2*Real.log n-spectralConstant -
    ∑ j ∈ range M, (CircleResidues.sourceCoefficient (j+1) : ℝ)/(n : ℝ)^(j+1)

theorem eigenvalueError_eq (M n : ℕ) (hn : 0 < n) :
    eigenvalueError M n = 4*harmonicError M (2*n)-2*harmonicError M n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hs : (∑ j ∈ range M, (CircleResidues.sourceCoefficient (j+1) : ℝ)/(n : ℝ)^(j+1)) =
      2*(∑ j ∈ range M, (bernoulli (j+1) : ℝ)/(j+1)/(n : ℝ)^(j+1)) -
      4*(∑ j ∈ range M, (bernoulli (j+1) : ℝ)/(j+1)/((2 : ℝ)*n)^(j+1)) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j hj
    rw [sourceCoefficient_cast_succ, mul_pow]
    ring
  simp only [eigenvalueError, harmonicError, spectralConstant, circleEigenvalue_harmonic,
    Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0]
  linear_combination -hs

theorem eigenvalueError_bigO (M : ℕ) (hM : 0 < M) :
    eigenvalueError M =O[atTop] (fun n : ℕ => 1/(n : ℝ)^M) := by
  have htwo : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by omega : ∀ n : ℕ, n ≤ 2*n) tendsto_id
  have ht := (harmonicError_bigO M hM).comp_tendsto htwo
  have hb : (fun n : ℕ => 1/((2*n : ℕ) : ℝ)^M) =O[atTop]
      (fun n : ℕ => 1/(n : ℝ)^M) := by
    have h := (isBigO_refl (fun n : ℕ => 1/(n : ℝ)^M) atTop).const_mul_left (1/(2 : ℝ)^M)
    apply h.congr_left
    intro n
    push_cast
    rw [mul_pow]
    ring
  have h := ((ht.trans hb).const_mul_left 4).sub ((harmonicError_bigO M hM).const_mul_left 2)
  apply h.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (eigenvalueError_eq M n (by omega)).symm

/-- The exact Bernoulli coefficients of the original circle eigenvalues, to every order. -/
theorem eigenvalue_all_order (M : ℕ) (hM : 0 < M) :
    (fun n : ℕ => circleEigenvalue n-2*Real.log n-spectralConstant -
      ∑ j ∈ range M, (CircleResidues.sourceCoefficient (j+1) : ℝ)/(n : ℝ)^(j+1))
      =O[atTop] (fun n : ℕ => 1/(n : ℝ)^M) :=
  (eigenvalueError_bigO M hM).congr_left (fun _ => rfl)

end CircleKernel
