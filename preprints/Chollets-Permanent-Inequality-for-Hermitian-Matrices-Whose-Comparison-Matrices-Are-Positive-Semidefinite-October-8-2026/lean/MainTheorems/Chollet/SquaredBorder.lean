import MainTheorems.Chollet.PencilShift
import MainTheorems.Chollet.BorderIdentities

noncomputable section

namespace ResearchMain.Chollet

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
theorem border_hadamard_conjugate (a : ℝ) (z : I → ℂ) (B : Matrix I I ℂ) :
    hadamard (border a z B) (conjugate (border a z B)) =
      border (a ^ 2) (fun i => ((‖z i‖ ^ 2 : ℝ) : ℂ))
        (hadamard B (conjugate B)) := by
  ext i j
  cases i with
  | inl u =>
    cases u
    cases j with
    | inl v =>
      cases v
      change (a : ℂ) * star (a : ℂ) = ((a ^ 2 : ℝ) : ℂ)
      simp [pow_two]
    | inr j =>
      change star (z j) * star (star (z j)) = star ((‖z j‖ ^ 2 : ℝ) : ℂ)
      simp only [Complex.star_def, Complex.conj_conj, Complex.conj_ofReal]
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  | inr i =>
    cases j with
    | inl u =>
      cases u
      change z i * star (z i) = ((‖z i‖ ^ 2 : ℝ) : ℂ)
      simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    | inr j => rfl

omit [Fintype I] [DecidableEq I] in
theorem normalizedBorder_squared (a : ℝ) (z : I → ℂ) (ha : 0 < a) :
    normalizedBorder (a ^ 2) (fun i => ((‖z i‖ ^ 2 : ℝ) : ℂ)) =
      fun i => ((‖normalizedBorder a z i‖ ^ 2 : ℝ) : ℂ) := by
  funext i
  simp only [normalizedBorder, Real.sqrt_sq ha.le, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr ha), div_pow,
    Real.sq_sqrt ha.le, Complex.ofReal_div]

theorem border_squared_permanent (a : ℝ) (z : I → ℂ) (B : Matrix I I ℂ)
    (ha : 0 < a) :
    (squaredEntries (border a z B)).permanent = a ^ 2 *
      ((hadamard B (conjugate B)).permanent.re +
        (rankFirst (hadamard B (conjugate B))
          (fun i => ((‖normalizedBorder a z i‖ ^ 2 : ℝ) : ℂ))).re) := by
  rw [← permanent_hadamard_conjugate, border_hadamard_conjugate,
    border_permanent_normalized _ _ _ (sq_pos_of_pos ha), normalizedBorder_squared a z ha]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, zero_mul, sub_zero]

end ResearchMain.Chollet
