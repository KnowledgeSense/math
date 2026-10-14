import MainTheorems.EulerianPencil.ReflectionFactors

namespace ResearchMain.EulerianPencil

open Polynomial

theorem X_derivative_degree_le {m : ℕ} {f : ℝ[X]} (hd : f.natDegree ≤ m) :
    (X * derivative f).natDegree ≤ m := by
  by_cases hm : f.natDegree = 0
  · simp [derivative_of_natDegree_zero hm]
  · have hmul := natDegree_mul_le (p := (X : ℝ[X])) (q := derivative f)
    have hder := natDegree_derivative_le f
    simp only [natDegree_X] at hmul
    omega

theorem weighted_derivative_shifted (j : ℕ) :
    (X - C 2 : ℝ[X]) * derivative ((X - C 2) ^ j) =
      (j : ℝ[X]) * (X - C 2) ^ j := by
  cases j with
  | zero => simp
  | succ j =>
    rw [derivative_pow]
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero, Nat.add_sub_cancel,
      mul_one, map_natCast, pow_succ]
    ring

theorem reduction_derivative {m : ℕ} {f : ℝ[X]} (hf : f.natDegree ≤ m) :
    (X - C 2) * derivative (reduction m f) =
      (m : ℝ[X]) * reduction m f - reduction m (X * derivative f) := by
  apply Polynomial.induction_with_natDegree_le
    (fun f => (X - C 2) * derivative (reduction m f) =
      (m : ℝ[X]) * reduction m f - reduction m (X * derivative f)) m
  · simp
  · intro j a _ hj
    have he : X * derivative (C a * X ^ j : ℝ[X]) = C a * (X * derivative (X ^ j)) := by
      simp [derivative_mul]
      ring
    rw [he, weighted_derivative_X, reduction_C_mul, ← map_natCast C j,
      reduction_C_mul, reduction_C_mul, reduction_X_pow hj]
    simp only [derivative_mul, derivative_C, zero_mul, zero_add, map_natCast]
    rw [show (X - C 2) * (C a * derivative ((X - C 2) ^ (m - j))) =
      C a * ((X - C 2) * derivative ((X - C 2) ^ (m - j))) by ring,
      weighted_derivative_shifted, Nat.cast_sub hj]
    ring
  · intro f g _ _ ihf ihg
    rw [reduction_add, derivative_add, mul_add, ihf, ihg]
    simp only [derivative_add, mul_add, reduction_add]
    ring
  · exact hf

theorem reduction_simpleRoots {m : ℕ} {f : ℝ[X]} (hd : f.natDegree ≤ m)
    (ht : f.coeff m ≠ 0) (hs : SimpleRoots f) : SimpleRoots (reduction m f) := by
  intro x hx hdx
  have hx2 : x ≠ 2 := by
    rintro rfl
    exact ht ((reduction_at_two m f).symm.trans hx)
  have hx0 : x - 2 ≠ 0 := sub_ne_zero.mpr hx2
  have hp : (x - 2) ^ m ≠ 0 := pow_ne_zero m hx0
  have hf : f.eval (1 / (x - 2)) = 0 := by
    rw [reduction_eval hd hx2] at hx
    exact (mul_eq_zero.mp hx).resolve_left hp
  have hdf := hs (1 / (x - 2)) hf
  have hd0 := X_derivative_degree_le hd
  have he := congrArg (fun p : ℝ[X] => p.eval x) (reduction_derivative hd)
  simp only [eval_mul, eval_sub, eval_X, eval_C, eval_natCast, hx, hdx, mul_zero, zero_sub] at he
  have hr : (reduction m (X * derivative f)).eval x = 0 := by linarith
  rw [reduction_eval hd0 hx2, eval_mul, eval_X] at hr
  exact (mul_ne_zero hp (mul_ne_zero (one_div_ne_zero hx0) hdf)) hr

theorem reduction_roots_lt_neg_two {m : ℕ} {f : ℝ[X]} (hd : f.natDegree ≤ m)
    (ht : f.coeff m ≠ 0) (h : RootInterval f) {x : ℝ}
    (hx : (reduction m f).eval x = 0) : x < -2 := by
  have hx2 : x ≠ 2 := by rintro rfl; exact ht ((reduction_at_two m f).symm.trans hx)
  have hx0 : x - 2 ≠ 0 := sub_ne_zero.mpr hx2
  have hf : f.eval (1 / (x - 2)) = 0 := by
    rw [reduction_eval hd hx2] at hx
    exact (mul_eq_zero.mp hx).resolve_left (pow_ne_zero m hx0)
  have hr := h.2.2 (1 / (x - 2)) ((mem_roots h.1).mpr hf)
  have hn : x - 2 < 0 := one_div_neg.mp hr.2
  have hm := mul_lt_mul_of_neg_right hr.1 hn
  rw [one_div, inv_mul_cancel₀ hx0] at hm
  linarith

theorem oddH_simpleRoots (m : ℕ) : SimpleRoots (oddH m) :=
  reduction_simpleRoots (oddF_degree_le m) (oddF_top_positive m).ne' (oddF_simpleRoots m)

theorem evenH_simpleRoots (m : ℕ) : SimpleRoots (evenH m) :=
  reduction_simpleRoots (evenF_degree_le m) (evenF_top_positive m).ne' (evenF_simpleRoots m)

theorem oddH_separable (m : ℕ) : (oddH m).Separable :=
  separable_of_simpleRoots (oddH_splits m) (oddH_monic m).ne_zero (oddH_simpleRoots m)

theorem evenH_separable (m : ℕ) : (evenH m).Separable :=
  separable_of_simpleRoots (evenH_splits m) (evenH_monic m).ne_zero (evenH_simpleRoots m)

theorem oddH_roots_lt_neg_two (m : ℕ) {x : ℝ} (hx : (oddH m).eval x = 0) : x < -2 :=
  reduction_roots_lt_neg_two (oddF_degree_le m) (oddF_top_positive m).ne'
    (oddF_rootInterval m) hx

theorem evenH_roots_lt_neg_two (m : ℕ) {x : ℝ} (hx : (evenH m).eval x = 0) : x < -2 :=
  reduction_roots_lt_neg_two (evenF_degree_le m) (evenF_top_positive m).ne'
    (evenF_rootInterval m) hx

end ResearchMain.EulerianPencil
