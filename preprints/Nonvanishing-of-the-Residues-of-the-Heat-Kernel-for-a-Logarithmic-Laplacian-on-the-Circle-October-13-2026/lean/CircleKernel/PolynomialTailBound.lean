import CircleKernel.BellPolynomials
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.Polynomial

noncomputable section
open Finset Polynomial
namespace CircleKernel

def polynomialHead (p : ℂ[X]) (M : ℕ) : ℂ[X] :=
  ∑ j ∈ range M, monomial j (p.coeff j)

@[simp] theorem polynomialHead_coeff (p : ℂ[X]) (M j : ℕ) :
    (polynomialHead p M).coeff j = if j < M then p.coeff j else 0 := by
  simp [polynomialHead, finsetSum_coeff, coeff_monomial, eq_comm]

@[simp] theorem polynomialHead_eval (p : ℂ[X]) (M : ℕ) (z : ℂ) :
    (polynomialHead p M).eval z = ∑ j ∈ range M, p.coeff j*z^j := by
  simp [polynomialHead, eval_finsetSum]

theorem polynomial_tail_bound (p : ℂ[X]) (M : ℕ) :
    ∃ B ≥ 0, ∀ z : ℂ, ‖z‖ ≤ 1 →
      ‖p.eval z-∑ j ∈ range M, p.coeff j*z^j‖ ≤ B*‖z‖^M := by
  have hd : X^M ∣ p-polynomialHead p M := by
    apply X_pow_dvd_iff.mpr
    intro j hj
    simp [hj]
  obtain ⟨q,hq⟩ := hd
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    q.continuous.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro z hz
  have hz' : z ∈ Metric.closedBall (0 : ℂ) 1 := by simpa using hz
  have he := congrArg (fun p : ℂ[X] => p.eval z) hq
  simp only [eval_sub, polynomialHead_eval, eval_mul, eval_pow, eval_X] at he
  rw [he, norm_mul, norm_pow]
  calc
    ‖z‖^M*‖q.eval z‖ ≤ ‖z‖^M*max B 0 :=
      mul_le_mul_of_nonneg_left ((hB z hz').trans (le_max_left _ _)) (by positivity)
    _ = _ := mul_comm _ _

end CircleKernel
