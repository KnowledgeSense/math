import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

noncomputable section
open Finset
namespace Paving

/-- A finite nonnegative mixture has positive value if its weights sum to one. -/
theorem mixture_positive {ι : Type*} (s : Finset ι) (w x : ι→ℝ)
    (hw : ∀i∈s,0≤w i) (hs : ∑i∈s,w i=1) (hx : ∀i∈s,0<x i) :
    0<∑i∈s,w i*x i := by
  have hex : ∃i∈s,0<w i := by
    by_contra! h
    have hz : ∑i∈s,w i=0 := sum_eq_zero (fun i hi => le_antisymm (h i hi) (hw i hi))
    linarith
  obtain ⟨i,hi,hwpos⟩ := hex
  exact lt_of_lt_of_le (mul_pos hwpos (hx i hi))
    (single_le_sum (fun j hj => mul_nonneg (hw j hj) (hx j hj).le) hi)

/-- Lower and upper ratio bounds persist under nonnegative mixing. -/
theorem mixture_linear_bounds {ι : Type*} (s : Finset ι) (w x y : ι→ℝ) (L U : ℝ)
    (hw : ∀i∈s,0≤w i) (hL : ∀i∈s,L*x i≤y i) (hU : ∀i∈s,y i≤U*x i) :
    L*(∑i∈s,w i*x i)≤∑i∈s,w i*y i ∧
      (∑i∈s,w i*y i)≤U*(∑i∈s,w i*x i) := by
  constructor
  · rw [mul_sum]
    apply sum_le_sum
    intro i hi
    simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left (hL i hi) (hw i hi)
  · rw [mul_sum]
    apply sum_le_sum
    intro i hi
    simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left (hU i hi) (hw i hi)

/-- Separated consecutive ratio intervals imply a strict Turán inequality. -/
theorem strict_turan_of_separated_bounds {p q r L U : ℝ}
    (hp : 0<p) (hq : 0<q) (hL : L*p≤q) (hU : r≤U*q) (hsep : U<L) :
    p*r<q^2 := by
  have h1 := mul_le_mul_of_nonneg_left hU hp.le
  have h2 := mul_lt_mul_of_pos_right hsep (mul_pos hp hq)
  have h3 := mul_le_mul_of_nonneg_right hL hq.le
  nlinarith

/-- A strictly increasing approach to a symmetric middle pair is sufficient. -/
theorem middle_pair_strict {p q : ℝ} (hq : 0<q) (h : p<q) : p*q<q^2 := by
  nlinarith [mul_lt_mul_of_pos_right h hq]

end Paving
