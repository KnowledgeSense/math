import MainTheorems.EulerianPencil.BoundaryLocations

namespace ResearchMain.EulerianPencil

open Polynomial

theorem reciprocalQuadratic_monic (r : ℝ) : (reciprocalQuadratic r).Monic := by
  unfold reciprocalQuadratic
  monicity <;> norm_num

theorem reciprocalQuadratic_natDegree (r : ℝ) : (reciprocalQuadratic r).natDegree = 2 := by
  unfold reciprocalQuadratic
  compute_degree <;> norm_num

theorem reciprocalQuadratic_eval (r x : ℝ) : (reciprocalQuadratic r).eval x = x ^ 2 - r * x + 1 := by
  norm_num [reciprocalQuadratic]

theorem reciprocalQuadratic_derivative_eval (r x : ℝ) :
    (derivative (reciprocalQuadratic r)).eval x = 2 * x - r := by
  norm_num [reciprocalQuadratic]

theorem reciprocalQuadratic_splits_iff (r : ℝ) :
    (reciprocalQuadratic r).Splits ↔ r ≤ -2 ∨ 2 ≤ r := by
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero
      (by rw [degree_eq_natDegree (reciprocalQuadratic_monic r).ne_zero,
        reciprocalQuadratic_natDegree]; norm_num)
    rw [reciprocalQuadratic_eval] at hx
    have hd : 0 ≤ r ^ 2 - 4 := by nlinarith [sq_nonneg (2 * x - r)]
    by_contra hn
    push Not at hn
    nlinarith
  · intro hr
    have hd : 0 ≤ r ^ 2 - 4 := by rcases hr with hr | hr <;> nlinarith
    apply Splits.of_natDegree_eq_two (reciprocalQuadratic_natDegree r) (x := (r + Real.sqrt (r ^ 2 - 4)) / 2)
    rw [reciprocalQuadratic_eval]
    nlinarith [Real.sq_sqrt hd]

theorem reciprocalQuadratic_simpleRoots_iff (r : ℝ) :
    SimpleRoots (reciprocalQuadratic r) ↔ r ≠ -2 ∧ r ≠ 2 := by
  constructor
  · intro hs
    constructor
    · intro hr
      have h := hs (-1) (by norm_num [reciprocalQuadratic_eval, hr])
      simp [reciprocalQuadratic_derivative_eval, hr] at h
    · intro hr
      have h := hs 1 (by norm_num [reciprocalQuadratic_eval, hr])
      simp [reciprocalQuadratic_derivative_eval, hr] at h
  · intro hr x hx hd
    rw [reciprocalQuadratic_eval] at hx
    rw [reciprocalQuadratic_derivative_eval] at hd
    have he : r = -2 ∨ r = 2 := by
      have hsq : r ^ 2 = 4 := by nlinarith
      rcases mul_eq_zero.mp (show (r + 2) * (r - 2) = 0 by nlinarith) with he | he
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    exact he.elim hr.1 hr.2

theorem reciprocalQuadratic_endpoint_neg : reciprocalQuadratic (-2) = (X + 1) ^ 2 := by
  unfold reciprocalQuadratic
  simp only [map_neg, map_ofNat]
  ring

theorem reciprocalQuadratic_endpoint_pos : reciprocalQuadratic 2 = (X - 1) ^ 2 := by
  unfold reciprocalQuadratic
  simp only [map_ofNat]
  ring

theorem reciprocalQuadratic_nonreal_norm {r : ℝ} {z : ℂ} (hz : z.im ≠ 0)
    (he : (complexify (reciprocalQuadratic r)).eval z = 0) : Complex.normSq z = 1 := by
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  simp [complexify, reciprocalQuadratic, pow_two, Complex.mul_re, Complex.mul_im] at hre him
  have hx : 2 * z.re - r = 0 := by
    apply (mul_eq_zero.mp (show z.im * (2 * z.re - r) = 0 by nlinarith)).resolve_left hz
  rw [Complex.normSq_apply]
  have hr : r = 2 * z.re := by linarith
  rw [hr] at hre
  nlinarith

end ResearchMain.EulerianPencil
