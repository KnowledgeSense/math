import MainTheorems.EulerianPencil.ComplexFractions
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace ResearchMain.EulerianPencil

open Polynomial Filter
open scoped Topology

theorem real_nodal_erase_eval {g : ℝ[X]} (hs : g.Splits) (hm : g.Monic)
    (hr : g.Separable) {r : ℝ} (hr' : r ∈ rootNodes g) {x : ℝ} (hx : g.eval x ≠ 0) :
    (Lagrange.nodal ((rootNodes g).erase r) id).eval x = g.eval x / (x - r) := by
  have hxr : x ≠ r := by rintro rfl; exact hx ((rootNodes_mem hm.ne_zero).mp hr')
  apply (eq_div_iff (sub_ne_zero.mpr hxr)).mpr
  have he := congrArg (fun p : ℝ[X] => p.eval x)
    (Lagrange.nodal_eq_mul_nodal_erase (v := (id : ℝ → ℝ)) hr')
  rw [nodal_rootNodes hs hm hr] at he
  simpa [mul_comm] using he.symm

theorem real_partial_fraction {m : ℕ} {f g : ℝ[X]} (hf : f.Monic) (hg : g.Monic)
    (df : f.natDegree = m + 1) (dg : g.natDegree = m) (hs : g.Splits) (hr : g.Separable)
    {x : ℝ} (hx : g.eval x ≠ 0) :
    f.eval x / g.eval x = x + (f /ₘ g).coeff 0 +
      ∑ r ∈ rootNodes g, (f.eval r / (derivative g).eval r) / (x - r) := by
  classical
  have he := congrArg (fun p : ℝ[X] => p.eval x)
    (partial_fraction_polynomial hf hg df dg hs hr)
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_finsetSum] at he
  rw [he, add_div, mul_div_cancel_right₀ _ hx, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr'
  rw [real_nodal_erase_eval hs hg hr hr' hx]
  field_simp

theorem real_ratio_derivative {m : ℕ} {f g : ℝ[X]} (hf : f.Monic) (hg : g.Monic)
    (df : f.natDegree = m + 1) (dg : g.natDegree = m) (hs : g.Splits) (hr : g.Separable)
    {x : ℝ} (hx : g.eval x ≠ 0) :
    (pencilWronskian f g).eval x / g.eval x ^ 2 =
      1 + ∑ r ∈ rootNodes g, -(f.eval r / (derivative g).eval r) / (x - r) ^ 2 := by
  classical
  have hsum : HasDerivAt (fun y : ℝ => ∑ r ∈ rootNodes g,
      (f.eval r / (derivative g).eval r) / (y - r))
      (∑ r ∈ rootNodes g, -(f.eval r / (derivative g).eval r) / (x - r) ^ 2) x := by
    apply HasDerivAt.fun_sum
    intro r hr'
    have hxr : x - r ≠ 0 := sub_ne_zero.mpr
      (fun he => hx (he ▸ (rootNodes_mem hg.ne_zero).mp hr'))
    convert (hasDerivAt_const x (f.eval r / (derivative g).eval r)).fun_div
      ((hasDerivAt_id x).sub_const r) hxr using 1 <;> simp
  have hright := ((hasDerivAt_id x).add_const ((f /ₘ g).coeff 0)).add hsum
  have hnear : (fun y : ℝ => f.eval y / g.eval y) =ᶠ[𝓝 x]
      (fun y => y + (f /ₘ g).coeff 0 + ∑ r ∈ rootNodes g,
        (f.eval r / (derivative g).eval r) / (y - r)) := by
    filter_upwards [g.continuous.continuousAt.eventually_ne hx] with y hy
    exact real_partial_fraction hf hg df dg hs hr hy
  have hleft := (f.hasDerivAt x).div (g.hasDerivAt x) hx
  have he := hleft.unique (hright.congr_of_eventuallyEq hnear)
  simpa only [pencilWronskian, eval_sub, eval_mul] using he

theorem residue_wronskian_positive {m : ℕ} {f g : ℝ[X]} (hf : f.Monic) (hg : g.Monic)
    (df : f.natDegree = m + 1) (dg : g.natDegree = m) (hs : g.Splits) (hr : g.Separable)
    (hsgn : ∀ r : ℝ, g.eval r = 0 → f.eval r * (derivative g).eval r < 0) (x : ℝ) :
    0 < (pencilWronskian f g).eval x := by
  by_cases hx : g.eval x = 0
  · simpa [pencilWronskian, hx] using neg_pos.mpr (hsgn x hx)
  · have he := real_ratio_derivative hf hg df dg hs hr hx
    have hsum : 0 ≤ ∑ r ∈ rootNodes g,
        -(f.eval r / (derivative g).eval r) / (x - r) ^ 2 := by
      apply Finset.sum_nonneg
      intro r hr'
      exact div_nonneg (neg_pos.mpr (residue_negative
        (hsgn r ((rootNodes_mem hg.ne_zero).mp hr')))).le (sq_nonneg _)
    have hp : 0 < (pencilWronskian f g).eval x / g.eval x ^ 2 := by rw [he]; linarith
    exact (div_pos_iff.mp hp).resolve_right (by rintro ⟨_, hn⟩; linarith [sq_nonneg (g.eval x)]) |>.1

theorem residue_pencil_simpleRoots {m : ℕ} {f g : ℝ[X]} (hf : f.Monic) (hg : g.Monic)
    (df : f.natDegree = m + 1) (dg : g.natDegree = m) (hs : g.Splits) (hr : g.Separable)
    (hsgn : ∀ r : ℝ, g.eval r = 0 → f.eval r * (derivative g).eval r < 0) (k : ℝ) :
    SimpleRoots (f + C k * g) := by
  intro x hx hdx
  have hw := residue_wronskian_positive hf hg df dg hs hr hsgn x
  simp only [eval_add, eval_mul, eval_C] at hx
  simp only [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add,
    eval_add, eval_mul, eval_C] at hdx
  have hz : (pencilWronskian f g).eval x = 0 := by
    simp only [pencilWronskian, eval_sub, eval_mul]
    linear_combination g.eval x * hdx - (derivative g).eval x * hx
  linarith

theorem oddH_pencil_simpleRoots (m : ℕ) (k : ℝ) : SimpleRoots (oddH (m + 1) + C k * oddH m) :=
  residue_pencil_simpleRoots (oddH_monic (m + 1)) (oddH_monic m) (oddH_natDegree (m + 1))
    (oddH_natDegree m) (oddH_splits m) (oddH_separable m) (fun _ => oddH_residue_sign m) k

theorem evenH_pencil_simpleRoots (m : ℕ) (k : ℝ) : SimpleRoots (evenH (m + 1) + C k * evenH m) :=
  residue_pencil_simpleRoots (evenH_monic (m + 1)) (evenH_monic m) (evenH_natDegree (m + 1))
    (evenH_natDegree m) (evenH_splits m) (evenH_separable m) (fun _ => evenH_residue_sign m) k

end ResearchMain.EulerianPencil
