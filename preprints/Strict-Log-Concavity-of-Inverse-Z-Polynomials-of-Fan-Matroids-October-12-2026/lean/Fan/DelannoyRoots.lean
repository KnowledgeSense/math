import Fan.DelannoyKernel
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Algebra.Polynomial.Splits

noncomputable section
open Polynomial
namespace Fan

/-- Differentiation preserves splitting for real polynomials. -/
theorem real_splits_derivative {p : Polynomial ℝ} (hp : p.Splits) : p.derivative.Splits := by
  apply splits_iff_card_roots.mpr
  apply le_antisymm (card_roots' _) 
  have h := card_roots_le_derivative p
  rw [← hp.natDegree_eq_card_roots] at h
  rw [natDegree_derivative]
  omega

private theorem sum_map_pos {α : Type*} (s : Multiset α) (f : α → ℝ)
    (hs : s ≠ 0) (hf : ∀ a ∈ s, 0 < f a) : 0 < (s.map f).sum := by
  induction s using Multiset.induction_on with
  | empty => exact (hs rfl).elim
  | @cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    apply add_pos_of_pos_of_nonneg (hf a (by simp))
    apply Multiset.sum_nonneg
    intro x hx
    obtain ⟨b,hb,rfl⟩ := Multiset.mem_map.mp hx
    exact (hf b (by simp [hb])).le

/-- The roots of a real derivative remain in any interval containing all original roots. -/
theorem real_derivative_roots_in_interval {p : Polynomial ℝ} (hp : p.Splits)
    {a b : ℝ} (hr : ∀ x ∈ p.roots, a ≤ x ∧ x ≤ b) :
    ∀ x ∈ p.derivative.roots, a ≤ x ∧ x ≤ b := by
  intro x hx
  have hd : p.derivative ≠ 0 := ne_zero_of_mem_roots hx
  have hn : p.natDegree ≠ 0 := fun h => hd (derivative_eq_zero.mpr h)
  have hp0 : p ≠ 0 := by intro h; simp [h] at hn
  have hroots := hp.roots_ne_zero hn
  have hex : p.derivative.eval x = 0 := (mem_roots hd).mp hx
  have hsum (hnot : x ∉ p.roots) : (p.roots.map (fun y => 1 / (x-y))).sum = 0 := by
    have he : p.eval x ≠ 0 := by intro h; exact hnot ((mem_roots hp0).mpr h)
    have h := hp.eval_derivative_eq_eval_mul_sum he
    rw [hex] at h
    exact (mul_eq_zero.mp h.symm).resolve_left he
  constructor
  · by_contra ha
    have hlt : x < a := lt_of_not_ge ha
    have hnot : x ∉ p.roots := by intro h; have := (hr x h).1; linarith
    have hs := sum_map_pos p.roots (fun y => -(1 / (x-y))) hroots (by
      intro y hy
      have := (hr y hy).1
      exact neg_pos.mpr (one_div_neg.mpr (by linarith)))
    rw [Multiset.sum_map_neg, hsum hnot] at hs
    linarith
  · by_contra hb
    have hlt : b < x := lt_of_not_ge hb
    have hnot : x ∉ p.roots := by intro h; have := (hr x h).2; linarith
    have hs := sum_map_pos p.roots (fun y => 1 / (x-y)) hroots (by
      intro y hy
      have := (hr y hy).2
      exact one_div_pos.mpr (by linarith))
    rw [hsum hnot] at hs
    linarith

end Fan
