import MainTheorems.EulerianPencil.SimpleRoots
import Mathlib.Topology.Order.IntermediateValue

namespace ResearchMain.EulerianPencil

open Polynomial

noncomputable def pencilWronskian (f g : ℝ[X]) : ℝ[X] := derivative f * g - f * derivative g

theorem no_common_root_of_simple_pencils {f g : ℝ[X]} (hg : SimpleRoots g)
    (hp : ∀ k : ℝ, SimpleRoots (f + C k * g)) (x : ℝ) (hx : g.eval x = 0) : f.eval x ≠ 0 := by
  intro hf
  have hd := hg x hx
  let k := -(derivative f).eval x / (derivative g).eval x
  have hq : (f + C k * g).eval x = 0 := by simp [hf, hx]
  apply hp k x hq
  simp only [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add,
    eval_add, eval_mul, eval_C]
  dsimp [k]
  rw [div_mul_cancel₀ _ hd]
  ring

theorem pencilWronskian_ne_zero {f g : ℝ[X]} (hg : SimpleRoots g)
    (hp : ∀ k : ℝ, SimpleRoots (f + C k * g)) (x : ℝ) :
    (pencilWronskian f g).eval x ≠ 0 := by
  by_cases hx : g.eval x = 0
  · have hf := no_common_root_of_simple_pencils hg hp x hx
    have hd := hg x hx
    simp only [pencilWronskian, eval_sub, eval_mul, hx, mul_zero, zero_sub]
    exact neg_ne_zero.mpr (mul_ne_zero hf hd)
  · intro he
    let k := -f.eval x / g.eval x
    have hq : (f + C k * g).eval x = 0 := by
      simp only [eval_add, eval_mul, eval_C]
      dsimp [k]
      rw [div_mul_cancel₀ _ hx]
      ring
    apply hp k x hq
    simp only [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add,
      eval_add, eval_mul, eval_C]
    dsimp [k]
    simp only [pencilWronskian, eval_sub, eval_mul] at he
    field_simp [hx]
    linear_combination he

theorem polynomial_positive_of_no_roots {f : ℝ[X]} (hn : ∀ x : ℝ, f.eval x ≠ 0)
    (h0 : 0 < f.eval 0) (x : ℝ) : 0 < f.eval x := by
  by_contra hx
  have hx0 : f.eval x ≤ 0 := not_lt.mp hx
  rcases le_total x 0 with hleft | hright
  · obtain ⟨y, _, hy⟩ := intermediate_value_Icc hleft f.continuous.continuousOn
      (show 0 ∈ Set.Icc (f.eval x) (f.eval 0) from ⟨hx0, h0.le⟩)
    exact hn y hy
  · obtain ⟨y, _, hy⟩ := intermediate_value_Icc' hright f.continuous.continuousOn
      (show 0 ∈ Set.Icc (f.eval x) (f.eval 0) from ⟨hx0, h0.le⟩)
    exact hn y hy

theorem oddF_first_nonnegative (m : ℕ) : 0 ≤ (oddF m).coeff 1 := by
  induction m with
  | zero => simp [oddF, coeff_one]
  | succ m ih =>
    rw [oddF, T_coeff_succ _ 0, U_coeff, U_coeff, oddF_constant]
    norm_num
    positivity

theorem oddF_first_step (m : ℕ) :
    (oddF (m + 1)).coeff 1 = 4 * (oddF m).coeff 1 + 6 := by
  rw [oddF, T_coeff_succ _ 0, U_coeff, U_coeff, oddF_constant]
  norm_num
  ring

theorem oddF_wronskian_positive (m : ℕ) (x : ℝ) :
    0 < (pencilWronskian (oddF (m + 1)) (oddF m)).eval x := by
  apply polynomial_positive_of_no_roots
    (pencilWronskian_ne_zero (oddF_simpleRoots m) (oddF_pencil_simpleRoots m))
  simp only [pencilWronskian, eval_sub, eval_mul, ← coeff_zero_eq_eval_zero, coeff_derivative]
  rw [oddF_constant, oddF_constant, oddF_first_step]
  have := oddF_first_nonnegative m
  norm_num
  linarith

theorem evenF_wronskian_positive (m : ℕ) (x : ℝ) :
    0 < (pencilWronskian (evenF (m + 1)) (evenF m)).eval x := by
  apply polynomial_positive_of_no_roots
    (pencilWronskian_ne_zero (evenF_simpleRoots m) (evenF_pencil_simpleRoots m))
  simp only [pencilWronskian, eval_sub, eval_mul, ← coeff_zero_eq_eval_zero, coeff_derivative]
  rw [evenF_constant, evenF_constant, evenF, evenF, U_coeff, U_coeff, oddF_first_step]
  have := oddF_first_nonnegative m
  norm_num
  linarith

end ResearchMain.EulerianPencil
