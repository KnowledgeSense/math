import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic

noncomputable section
namespace Dowling
open scoped Classical
open Finset PowerSeries
variable {I : Type*} [Fintype I]

 def labeledColorCount {n : ℕ} (w : Fin n → I) (c : I) : ℕ :=
  (univ.filter (fun i => w i=c)).card

 def labeledColorSum (f : I → ℕ → Polynomial ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ w : Fin n → I, ∏ c : I, f c (labeledColorCount w c)

 def labeledColorShift (f : I → ℕ → Polynomial ℝ) (c : I) : I → ℕ → Polynomial ℝ :=
  fun d j => if d=c then f d (j+1) else f d j

omit [Fintype I] in
theorem labeledColorCount_cons {n : ℕ} (c d : I) (w : Fin n → I) :
    labeledColorCount (Fin.cons c w) d=(if c=d then 1 else 0)+labeledColorCount w d := by
  unfold labeledColorCount
  simp only [card_filter]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ]

 theorem labeledColorSum_zero (f : I → ℕ → Polynomial ℝ) :
    labeledColorSum f 0=∏ c : I, f c 0 := by
  simp [labeledColorSum,labeledColorCount]

 theorem labeledColorSum_succ (f : I → ℕ → Polynomial ℝ) (n : ℕ) :
    labeledColorSum f (n+1)=∑ c : I, labeledColorSum (labeledColorShift f c) n := by
  unfold labeledColorSum
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => I)).sum_comp]
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro w _
  apply prod_congr rfl
  intro d _
  change f d (labeledColorCount (Fin.cons c w) d)=labeledColorShift f c d (labeledColorCount w d)
  rw [labeledColorCount_cons]
  by_cases h : c=d
  · subst d
    simp [labeledColorShift,Nat.add_comm]
  · simp [labeledColorShift,h,Ne.symm h]

end Dowling
