import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

namespace ResearchMain.AHOConstants

open scoped BigOperators

variable {m : ℕ}

def Circulation (p q a b : Fin (m + 1) → ℝ) : Prop :=
  (∀ i, 0 ≤ a i ∧ a i ≤ 1 / 2 ∧ 0 ≤ b i ∧ b i ≤ 1 / 2) ∧
  (∀ i, a i + b i = q i) ∧
  (∀ i, a (finRotate (m + 1) i) + b i = p (finRotate (m + 1) i))

def Feasible (p q : Fin (m + 1) → ℝ) : Prop :=
  ∃ a b, Circulation p q a b

theorem Circulation.step {p q a b : Fin (m + 1) → ℝ}
    (h : Circulation p q a b) (i : Fin (m + 1)) :
    a (finRotate (m + 1) i) - a i = p (finRotate (m + 1) i) - q i := by
  have hq := h.2.1 i
  have hp := h.2.2 i
  linarith

theorem Circulation.previous {p q a b : Fin (m + 1) → ℝ}
    (h : Circulation p q a b) (i : Fin (m + 1)) :
    a i + b ((finRotate (m + 1)).symm i) = p i := by
  simpa using h.2.2 ((finRotate (m + 1)).symm i)

theorem Circulation.total {p q a b : Fin (m + 1) → ℝ}
    (h : Circulation p q a b) :
    (∑ i, p i) = ∑ i, q i := by
  have ha := Equiv.sum_comp (finRotate (m + 1)) a
  have hp := Equiv.sum_comp (finRotate (m + 1)) p
  have hq := congrArg (fun f : Fin (m + 1) → ℝ => ∑ i, f i) (funext h.2.1)
  have hc := congrArg (fun f : Fin (m + 1) → ℝ => ∑ i, f i) (funext h.2.2)
  simp only [Finset.sum_add_distrib] at hq hc
  rw [ha, hp] at hc
  linarith

theorem Circulation.weight_sum {p q a b : Fin (m + 1) → ℝ}
    (h : Circulation p q a b) (hq : (∑ i, q i) = 1) :
    (∑ i, (a i + b i)) = 1 := by
  simpa only [h.2.1] using hq

theorem single_pair_feasible {p q : Fin 1 → ℝ}
    (hp : p 0 = 1) (hq : q 0 = 1) : Feasible p q := by
  refine ⟨fun _ => 1 / 2, fun _ => 1 / 2, ?_⟩
  constructor
  · intro i
    norm_num
  constructor
  · intro i
    have hi : i = 0 := by
      apply Fin.ext
      have := i.isLt
      simp only [Fin.val_zero]
      omega
    subst i
    norm_num [hq]
  · intro i
    have hi : i = 0 := by
      apply Fin.ext
      have := i.isLt
      simp only [Fin.val_zero]
      omega
    subst i
    have hr : finRotate 1 (0 : Fin 1) = 0 := by
      apply Fin.ext
      have := (finRotate 1 (0 : Fin 1)).isLt
      simp only [Fin.val_zero]
      omega
    change (1 / 2 : ℝ) + 1 / 2 = p (finRotate 1 0)
    rw [hr, hp]
    norm_num

theorem single_pair_unique {p q a b : Fin 1 → ℝ}
    (h : Circulation p q a b) (hq : q 0 = 1) : a 0 = 1 / 2 ∧ b 0 = 1 / 2 := by
  have hab := h.2.1 0
  have ha := h.1 0
  rw [hq] at hab
  constructor <;> linarith

end ResearchMain.AHOConstants
