import MainTheorems.EulerianPencil.ReducedRoots

namespace ResearchMain.EulerianPencil

open Polynomial

theorem reduction_residue_sign {m : ℕ} {f g : ℝ[X]} (hf : f.natDegree ≤ m + 1)
    (hg : g.natDegree ≤ m) (ht : g.coeff m ≠ 0) (hr : RootInterval g)
    (hw : ∀ r : ℝ, 0 < (pencilWronskian f g).eval r) {x : ℝ}
    (hx : (reduction m g).eval x = 0) :
    (reduction (m + 1) f).eval x * (derivative (reduction m g)).eval x < 0 := by
  have hx2 : x ≠ 2 := by rintro rfl; exact ht ((reduction_at_two m g).symm.trans hx)
  have hx0 : x - 2 ≠ 0 := sub_ne_zero.mpr hx2
  let r : ℝ := 1 / (x - 2)
  have hg0 : g.eval r = 0 := by
    rw [reduction_eval hg hx2] at hx
    exact (mul_eq_zero.mp hx).resolve_left (pow_ne_zero m hx0)
  have hn : x - 2 < 0 := by
    have hroot := reduction_roots_lt_neg_two hg ht hr hx
    linarith
  have hder := congrArg (fun p : ℝ[X] => p.eval x) (reduction_derivative hg)
  simp only [eval_mul, eval_sub, eval_X, eval_C, eval_natCast, hx, mul_zero, zero_sub] at hder
  rw [reduction_eval (X_derivative_degree_le hg) hx2, eval_mul, eval_X] at hder
  have hfval := reduction_eval hf hx2
  have hwval := hw r
  simp only [pencilWronskian, eval_sub, eval_mul, hg0, mul_zero, zero_sub] at hwval
  have he : (x - 2) * ((reduction (m + 1) f).eval x *
      (derivative (reduction m g)).eval x) =
        ((x - 2) ^ m) ^ 2 * (-(f.eval r * (derivative g).eval r)) := by
    rw [hfval, pow_succ]
    calc
      (x - 2) * (((x - 2) ^ m * (x - 2) * f.eval r) *
        (derivative (reduction m g)).eval x) =
          (x - 2) ^ m * (x - 2) * f.eval r *
            ((x - 2) * (derivative (reduction m g)).eval x) := by ring
      _ = _ := by
        rw [hder]
        dsimp [r]
        field_simp [hx0]
  have hp : 0 < (x - 2) * ((reduction (m + 1) f).eval x *
      (derivative (reduction m g)).eval x) := by
    rw [he]
    exact mul_pos (sq_pos_of_ne_zero (pow_ne_zero m hx0)) hwval
  nlinarith

theorem oddH_residue_sign (m : ℕ) {x : ℝ} (hx : (oddH m).eval x = 0) :
    (oddH (m + 1)).eval x * (derivative (oddH m)).eval x < 0 :=
  reduction_residue_sign (oddF_degree_le (m + 1)) (oddF_degree_le m)
    (oddF_top_positive m).ne' (oddF_rootInterval m) (oddF_wronskian_positive m) hx

theorem evenH_residue_sign (m : ℕ) {x : ℝ} (hx : (evenH m).eval x = 0) :
    (evenH (m + 1)).eval x * (derivative (evenH m)).eval x < 0 :=
  reduction_residue_sign (evenF_degree_le (m + 1)) (evenF_degree_le m)
    (evenF_top_positive m).ne' (evenF_rootInterval m) (evenF_wronskian_positive m) hx

end ResearchMain.EulerianPencil
