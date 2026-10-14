import MainTheorems.AHOConstants.ClosedWalkTrace
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fin.Tuple.Basic

namespace ResearchMain.AHOConstants

open scoped BigOperators

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

omit [Fintype I] [DecidableEq I] in
theorem snoc_succ_tail {n : ℕ} (f : Fin (n + 1) → I) (b : I) (i : Fin (n + 1)) :
    @Fin.snoc (n + 1) (fun _ => I) f b i.succ =
      @Fin.snoc n (fun _ => I) (fun j => f j.succ) b i := by
  have h := Fin.cons_snoc_eq_snoc_cons (f 0) (Fin.tail f) b
  rw [Fin.cons_self_tail] at h
  have hi := congrFun h i.succ
  simp only [Fin.cons_succ] at hi
  convert hi.symm using 1
  rfl

omit [Fintype I] [DecidableEq I] in
theorem openWalkTerm_eq_product (M : Matrix I I R) (xs : List (Matrix I I R))
    (a b : I) (f : Fin xs.length → I) :
    openWalkTerm M xs a b f =
      ∏ i : Fin (xs.length + 1), (M :: xs).get i (@Fin.cons xs.length (fun _ => I) a f i)
        (@Fin.snoc xs.length (fun _ => I) f b i) := by
  induction xs generalizing M a b with
  | nil => simp [openWalkTerm, Fin.snoc_zero]
  | cons N xs ih =>
    have hrow : @Fin.cons xs.length (fun _ => I) (f 0) (fun i => f i.succ) = f := Fin.cons_self_tail f
    calc
      openWalkTerm M (N :: xs) a b f = M a (f 0) *
          (∏ i : Fin (xs.length + 1), (N :: xs).get i
            (@Fin.cons xs.length (fun _ => I) (f 0) (fun j => f j.succ) i)
            (@Fin.snoc xs.length (fun _ => I) (fun j => f j.succ) b i)) := by
        rw [openWalkTerm, ih]
      _ = M a (f 0) * (∏ i : Fin (xs.length + 1),
          (N :: xs).get i (f i) (@Fin.snoc (xs.length + 1) (fun _ => I) f b i.succ)) := by
        apply congrArg (fun x => M a (f 0) * x)
        apply Finset.prod_congr rfl
        intro i hi
        rw [hrow, snoc_succ_tail]
      _ = _ := by
        have h := (Fin.prod_univ_succ (fun i : Fin ((N :: xs).length + 1) =>
            (M :: N :: xs).get i (@Fin.cons (xs.length + 1) (fun _ => I) a f i)
              (@Fin.snoc (xs.length + 1) (fun _ => I) f b i))).symm
        simp only [List.get_eq_getElem, Fin.val_zero, Fin.val_succ,
          List.getElem_cons_succ, Fin.cons_zero,
          Fin.cons_succ, Fin.snoc_apply_zero] at h
        convert h using 1
        rfl

omit [Fintype I] [DecidableEq I] in
theorem closedWalkTerm_eq_product (M : Matrix I I R) (xs : List (Matrix I I R))
    (f : Fin (xs.length + 1) → I) :
    closedWalkTerm M xs f =
      ∏ i : Fin (xs.length + 1), (M :: xs).get i (f i) (f (finRotate _ i)) := by
  unfold closedWalkTerm
  rw [openWalkTerm_eq_product]
  have hrow : @Fin.cons xs.length (fun _ => I) (f 0) (fun i => f i.succ) = f := Fin.cons_self_tail f
  have hcol : @Fin.snoc xs.length (fun _ => I) (fun i => f i.succ) (f 0) =
      fun i => f (finRotate _ i) := by
    rw [Fin.snoc_eq_cons_rotate, hrow]
  rw [hrow, hcol]

theorem closed_walk_trace_product (M : Matrix I I R) (xs : List (Matrix I I R)) :
    Matrix.trace (M :: xs).prod = ∑ f : Fin (xs.length + 1) → I,
      ∏ i : Fin (xs.length + 1), (M :: xs).get i (f i) (f (finRotate _ i)) := by
  rw [closed_walk_trace_expansion]
  apply Finset.sum_congr rfl
  intro f hf
  exact closedWalkTerm_eq_product M xs f

set_option backward.isDefEq.respectTransparency false in
theorem closed_walk_trace_ofFn {m : ℕ} (M : Fin (m + 1) → Matrix I I R) :
    Matrix.trace (List.ofFn M).prod =
      ∑ f : Fin (m + 1) → I, ∏ i : Fin (m + 1), M i (f i) (f (finRotate _ i)) := by
  have h := closed_walk_trace_product (M 0) (List.ofFn (fun i : Fin m => M i.succ))
  convert h using 1
  · rw [List.ofFn_succ]
  · have hlen : (List.ofFn (fun i : Fin m => M i.succ)).length = m := List.length_ofFn
    generalize hs : List.ofFn (fun i : Fin m => M i.succ) = xs at hlen ⊢
    subst m
    have hall : M 0 :: xs = List.ofFn M := by
      rw [List.ofFn_succ, hs]
    apply Finset.sum_congr rfl
    intro f hf
    apply Finset.prod_congr rfl
    intro i hi
    have hget : (M 0 :: xs).get i = M i := by
      have h := congrArg (fun ys : List (Matrix I I R) => ys[i.val]?) hall
      rw [List.getElem?_eq_getElem i.isLt,
        List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using i.isLt),
        List.getElem_ofFn] at h
      exact Option.some.inj h
    rw [hget]

end ResearchMain.AHOConstants
