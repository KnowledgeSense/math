import MainTheorems.EulerianPencil.LiftedPencils

namespace ResearchMain.EulerianPencil

open Polynomial

theorem quadraticLift_eval_one {m : ℕ} {f : ℝ[X]} (hf : f.natDegree ≤ m) :
    (quadraticLift m f).eval 1 = f.eval 2 := by
  apply Polynomial.induction_with_natDegree_le
    (fun f => (quadraticLift m f).eval 1 = f.eval 2) m
  · simp
  · intro j a _ hj
    rw [quadraticLift_C_mul, quadraticLift_X_pow hj]
    norm_num
  · intro f g _ _ ihf ihg
    simp only [quadraticLift_add, eval_add, ihf, ihg]
  · exact hf

theorem eulerianReal_eval_one (n : ℕ) :
    ((eulerian n).map (Int.castRingHom ℝ)).eval 1 = (n.factorial : ℝ) := by
  rw [eval_map]
  simp [eulerian_eval_one]

theorem oddH_eval_two (m : ℕ) : (oddH m).eval 2 = ((2 * m + 1).factorial : ℝ) := by
  have he := congrArg (fun f : ℝ[X] => f.eval 1) (eulerian_quadraticLift m).1
  rw [eulerianReal_eval_one, quadraticLift_eval_one (oddH_natDegree m).le] at he
  exact he.symm

theorem evenH_eval_two (m : ℕ) : (evenH m).eval 2 = ((2 * m + 2).factorial : ℝ) / 2 := by
  have he := congrArg (fun f : ℝ[X] => f.eval 1) (eulerian_quadraticLift m).2
  rw [eulerianReal_eval_one, eval_mul, quadraticLift_eval_one (evenH_natDegree m).le] at he
  norm_num at he
  linarith

theorem oddH_positive_at_neg_two (m : ℕ) : 0 < (oddH m).eval (-2) :=
  zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg (fun _ => oddH_roots_lt_neg_two m)
    (by rw [(oddH_monic m).leadingCoeff]; norm_num)

theorem evenH_positive_at_neg_two (m : ℕ) : 0 < (evenH m).eval (-2) :=
  zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg (fun _ => evenH_roots_lt_neg_two m)
    (by rw [(evenH_monic m).leadingCoeff]; norm_num)

theorem oddH_successor_at_neg_two (m : ℕ) :
    (oddH (m + 1)).eval (-2) = 2 * (evenH m).eval (-2) := by
  rw [oddH, evenH, reduction_eval (oddF_degree_le (m + 1)) (by norm_num),
    reduction_eval (evenF_degree_le m) (by norm_num)]
  norm_num
  rw [oddF, evenF]
  simp only [T, eval_add, eval_mul, eval_C, eval_X, eval_one]
  norm_num
  rw [pow_succ]
  ring

theorem oddH_ratio_at_two (m : ℕ) :
    (oddH (m + 1)).eval 2 / (oddH m).eval 2 = (2 * m + 3 : ℝ) * (2 * m + 2) := by
  rw [oddH_eval_two, oddH_eval_two]
  rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by omega,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  have hp : ((2 * m + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  field_simp
  ring

theorem evenH_ratio_at_two (m : ℕ) :
    (evenH (m + 1)).eval 2 / (evenH m).eval 2 = (2 * m + 4 : ℝ) * (2 * m + 3) := by
  rw [evenH_eval_two, evenH_eval_two]
  rw [show 2 * (m + 1) + 2 = (2 * m + 2) + 1 + 1 by omega,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  have hp : ((2 * m + 2).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  field_simp
  ring

theorem evenH_ratio_at_neg_two (m : ℕ) :
    (evenH (m + 1)).eval (-2) / (evenH m).eval (-2) =
      (oddH (m + 2)).eval (-2) / (oddH (m + 1)).eval (-2) := by
  rw [show m + 2 = (m + 1) + 1 by omega, oddH_successor_at_neg_two,
    oddH_successor_at_neg_two]
  exact (mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)).symm

theorem oddH_boundary_order (m : ℕ) :
    (oddH (m + 1)).eval (-2) / (oddH m).eval (-2) < (2 * m + 3 : ℝ) * (2 * m + 2) := by
  rw [← oddH_ratio_at_two]
  exact (oddH_interlacingPair m).ratio_strictMonoOn (fun _ => oddH_roots_lt_neg_two m)
    (by norm_num) (by norm_num) (by norm_num)

theorem evenH_boundary_order (m : ℕ) :
    (evenH (m + 1)).eval (-2) / (evenH m).eval (-2) < (2 * m + 4 : ℝ) * (2 * m + 3) := by
  rw [← evenH_ratio_at_two]
  exact (evenH_interlacingPair m).ratio_strictMonoOn (fun _ => evenH_roots_lt_neg_two m)
    (by norm_num) (by norm_num) (by norm_num)

end ResearchMain.EulerianPencil
