import MainTheorems.EulerianPencil.Pencils

namespace ResearchMain.EulerianPencil

open Polynomial

noncomputable def laguerre (f : ℝ[X]) (x : ℝ) : ℝ :=
  (derivative f).eval x ^ 2 - f.eval x * (derivative (derivative f)).eval x

theorem laguerre_mul (f g : ℝ[X]) (x : ℝ) :
    laguerre (f * g) x = f.eval x ^ 2 * laguerre g x + g.eval x ^ 2 * laguerre f x := by
  simp [laguerre, derivative_mul, derivative_add]
  ring

theorem laguerre_linear (a x : ℝ) : laguerre (X - C a) x = 1 := by simp [laguerre]

theorem laguerre_C (a x : ℝ) : laguerre (C a) x = 0 := by simp [laguerre]

theorem laguerre_product_nonnegative (r : Multiset ℝ) (x : ℝ) :
    0 ≤ laguerre (r.map (fun a => (X - C a : ℝ[X]))).prod x := by
  induction r using Multiset.induction_on with
  | empty => simp [laguerre]
  | cons a r ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, laguerre_mul, laguerre_linear, mul_one]
    exact add_nonneg (mul_nonneg (sq_nonneg _) ih) (sq_nonneg _)

theorem laguerre_nonnegative {f : ℝ[X]} (hs : f.Splits) (x : ℝ) : 0 ≤ laguerre f x := by
  nth_rw 1 [hs.eq_prod_roots]
  rw [laguerre_mul, laguerre_C, mul_zero, add_zero]
  exact mul_nonneg (sq_nonneg _) (laguerre_product_nonnegative _ _)

def RootInterval (f : ℝ[X]) : Prop :=
  f ≠ 0 ∧ f.Splits ∧ ∀ r ∈ f.roots, -(1 / 4 : ℝ) < r ∧ r < 0

theorem eval_ne_zero_outside {f : ℝ[X]} (h : RootInterval f) {x : ℝ}
    (hx : x ≤ -(1 / 4 : ℝ) ∨ 0 ≤ x) : f.eval x ≠ 0 := by
  intro hz
  have hr := h.2.2 x ((mem_roots h.1).mpr hz)
  rcases hx with hx | hx <;> linarith

theorem inverse_root_sum_nonpositive {f : ℝ[X]} (h : RootInterval f) {x : ℝ}
    (hx : x ≤ -(1 / 4 : ℝ)) : (f.roots.map (fun r => 1 / (x - r))).sum ≤ 0 := by
  have hn : 0 ≤ (f.roots.map (fun r => -(1 / (x - r)))).sum := by
    apply Multiset.sum_nonneg
    intro a ha
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp ha
    exact neg_nonneg.mpr (le_of_lt (one_div_neg.mpr (by have := h.2.2 r hr; linarith)))
  simpa only [Multiset.sum_map_neg, neg_nonneg] using hn

theorem inverse_root_sum_nonnegative {f : ℝ[X]} (h : RootInterval f) {x : ℝ}
    (hx : 0 ≤ x) : 0 ≤ (f.roots.map (fun r => 1 / (x - r))).sum := by
  apply Multiset.sum_nonneg
  intro a ha
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp ha
  exact le_of_lt (one_div_pos.mpr (by have := h.2.2 r hr; linarith))

theorem U_eval_ne_zero_outside {f : ℝ[X]} (h : RootInterval f) {x : ℝ}
    (hx : x ≤ -(1 / 4 : ℝ) ∨ 0 ≤ x) : (U f).eval x ≠ 0 := by
  have hf := eval_ne_zero_outside h hx
  have hd := h.2.1.eval_derivative_eq_eval_mul_sum hf
  have hp : 0 < 1 + x * (f.roots.map (fun r => 1 / (x - r))).sum := by
    rcases hx with hx | hx
    · have hs := inverse_root_sum_nonpositive h hx
      have : 0 ≤ x * (f.roots.map (fun r => 1 / (x - r))).sum :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) hs
      linarith
    · have hs := inverse_root_sum_nonnegative h hx
      have := mul_nonneg hx hs
      linarith
  simp only [U, eval_add, eval_mul, eval_X]
  rw [hd, show f.eval x + x * (f.eval x * (f.roots.map (fun r => 1 / (x - r))).sum) =
    f.eval x * (1 + x * (f.roots.map (fun r => 1 / (x - r))).sum) by ring]
  exact mul_ne_zero hf hp.ne'

theorem T_eval_ne_zero_outside {f : ℝ[X]} (h : RootInterval f) {x : ℝ}
    (hx : x ≤ -(1 / 4 : ℝ) ∨ 0 ≤ x) : (T f).eval x ≠ 0 := by
  have hf := eval_ne_zero_outside h hx
  have hd := h.2.1.eval_derivative_eq_eval_mul_sum hf
  have hp : 1 + 6 * x + x * (1 + 4 * x) *
      (f.roots.map (fun r => 1 / (x - r))).sum ≠ 0 := by
    rcases hx with hx | hx
    · have hs := inverse_root_sum_nonpositive h hx
      have hv : 0 ≤ x * (1 + 4 * x) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      have := mul_nonpos_of_nonneg_of_nonpos hv hs
      linarith
    · have hs := inverse_root_sum_nonnegative h hx
      have hv := mul_nonneg hx (show 0 ≤ 1 + 4 * x by linarith)
      have := mul_nonneg hv hs
      linarith
  simp only [T, eval_add, eval_mul, eval_X, eval_one, eval_C]
  rw [hd, show (1 + 6 * x) * f.eval x + x * (1 + 4 * x) *
    (f.eval x * (f.roots.map (fun r => 1 / (x - r))).sum) =
    f.eval x * (1 + 6 * x + x * (1 + 4 * x) *
      (f.roots.map (fun r => 1 / (x - r))).sum) by ring]
  exact mul_ne_zero hf hp

theorem U_rootInterval {f : ℝ[X]} (h : RootInterval f) : RootInterval (U f) := by
  have hz := U_eval_ne_zero_outside h (Or.inr (le_refl 0))
  refine ⟨fun he => hz (by simp [he]), U_preserves_splits h.2.1, ?_⟩
  intro r hr
  have he := (mem_roots (fun he => hz (by simp [he]))).mp hr
  constructor
  · by_contra hl
    exact U_eval_ne_zero_outside h (Or.inl (not_lt.mp hl)) he
  · by_contra hl
    exact U_eval_ne_zero_outside h (Or.inr (not_lt.mp hl)) he

theorem T_rootInterval {f : ℝ[X]} (h : RootInterval f) : RootInterval (T f) := by
  have hz := T_eval_ne_zero_outside h (Or.inr (le_refl 0))
  refine ⟨fun he => hz (by simp [he]), T_preserves_splits h.2.1, ?_⟩
  intro r hr
  have he := (mem_roots (fun he => hz (by simp [he]))).mp hr
  constructor
  · by_contra hl
    exact T_eval_ne_zero_outside h (Or.inl (not_lt.mp hl)) he
  · by_contra hl
    exact T_eval_ne_zero_outside h (Or.inr (not_lt.mp hl)) he

theorem oddF_rootInterval (m : ℕ) : RootInterval (oddF m) := by
  induction m with
  | zero => simp [oddF, RootInterval]
  | succ m ih => exact T_rootInterval (U_rootInterval ih)

theorem evenF_rootInterval (m : ℕ) : RootInterval (evenF m) := U_rootInterval (oddF_rootInterval m)

end ResearchMain.EulerianPencil
