import TerminalLogConcavity.DecoratedPath
import TerminalLogConcavity.CoefficientOrder

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial

/-- Transfer recurrence for independent-set weights along a path. -/
noncomputable def weightedPathFrom (ws : List (ℕ[X] × ℕ[X])) (z : ℕ[X] × ℕ[X]) : ℕ[X] × ℕ[X] :=
  match ws with
  | [] => z
  | w :: ws =>
    let t := weightedPathFrom ws z
    (w.1 * t.1 + w.2 * t.2, w.1 * t.1)
noncomputable def weightedPath (ws : List (ℕ[X] × ℕ[X])) : ℕ[X] × ℕ[X] := weightedPathFrom ws (1,1)

theorem pathStateSum_eq_weightedPath (ds : List Decoration) :
    pathStateSum ds = weightedPath (ds.map (fun D => (D.A, D.B))) := by
  induction ds with
  | nil => rfl
  | cons D ds ih => simp only [pathStateSum, List.map_cons, weightedPath, weightedPathFrom] at *; rw [ih]

theorem weightedPathFrom_append (xs ys : List (ℕ[X] × ℕ[X])) (z : ℕ[X] × ℕ[X]) :
    weightedPathFrom (xs ++ ys) z = weightedPathFrom xs (weightedPathFrom ys z) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, weightedPathFrom, ih]

theorem weightedPathFrom_mono (ws : List (ℕ[X] × ℕ[X])) {z z' : ℕ[X] × ℕ[X]}
    (h1 : CoeffLE z.1 z'.1) (h2 : CoeffLE z.2 z'.2) :
    CoeffLE (weightedPathFrom ws z).1 (weightedPathFrom ws z').1 ∧
      CoeffLE (weightedPathFrom ws z).2 (weightedPathFrom ws z').2 := by
  induction ws with
  | nil => exact ⟨h1,h2⟩
  | cons w ws ih => exact ⟨((CoeffLE.refl w.1).mul ih.1).add ((CoeffLE.refl w.2).mul ih.2),
      (CoeffLE.refl w.1).mul ih.1⟩

theorem weightedPath_excluded_le (ws : List (ℕ[X] × ℕ[X])) :
    CoeffLE (weightedPath ws).2 (weightedPath ws).1 := by
  cases ws with
  | nil => exact CoeffLE.refl _
  | cons w ws => exact CoeffLE.le_add_right _ _

theorem weightedPathFrom_scale (ws : List (ℕ[X] × ℕ[X])) (s : ℕ[X]) :
    weightedPathFrom ws (s,s) = (s * (weightedPath ws).1, s * (weightedPath ws).2) := by
  induction ws with
  | nil => simp [weightedPathFrom, weightedPath]
  | cons w ws ih =>
    simp only [weightedPathFrom, ih, weightedPath]
    congr 1 <;> ring

theorem weightedPath_bridge_bounds (xs ys : List (ℕ[X] × ℕ[X])) (w : ℕ[X] × ℕ[X]) :
    CoeffLE (w.1 * (weightedPath xs).1 * (weightedPath ys).1)
      (weightedPath (xs ++ w :: ys)).1 ∧
    CoeffLE (weightedPath (xs ++ w :: ys)).1
      ((w.1 + w.2) * (weightedPath xs).1 * (weightedPath ys).1) := by
  have hy := weightedPath_excluded_le ys
  have lower := weightedPathFrom_mono xs
    (z := (w.1 * (weightedPath ys).1, w.1 * (weightedPath ys).1))
    (z' := (w.1 * (weightedPath ys).1 + w.2 * (weightedPath ys).2, w.1 * (weightedPath ys).1))
    (CoeffLE.le_add_right (w.1 * (weightedPath ys).1) (w.2 * (weightedPath ys).2))
    (CoeffLE.refl (w.1 * (weightedPath ys).1))
  have upper1 : CoeffLE (w.1 * (weightedPath ys).1 + w.2 * (weightedPath ys).2)
      ((w.1 + w.2) * (weightedPath ys).1) := by
    rw [add_mul]
    exact (CoeffLE.refl _).add ((CoeffLE.refl _).mul hy)
  have upper2 : CoeffLE (w.1 * (weightedPath ys).1) ((w.1 + w.2) * (weightedPath ys).1) := by
    rw [add_mul]
    exact CoeffLE.le_add_right _ _
  have upper := weightedPathFrom_mono xs
    (z := (w.1 * (weightedPath ys).1 + w.2 * (weightedPath ys).2, w.1 * (weightedPath ys).1))
    (z' := ((w.1 + w.2) * (weightedPath ys).1, (w.1 + w.2) * (weightedPath ys).1)) upper1 upper2
  rw [weightedPathFrom_scale] at lower upper
  change CoeffLE _ (weightedPathFrom (xs ++ w :: ys) (1,1)).1 ∧
    CoeffLE (weightedPathFrom (xs ++ w :: ys) (1,1)).1 _
  rw [weightedPathFrom_append]
  constructor
  · simpa only [weightedPath, weightedPathFrom, mul_assoc, mul_left_comm, mul_comm] using lower.1
  · simpa only [weightedPath, weightedPathFrom, mul_assoc, mul_left_comm, mul_comm] using upper.1

theorem weightedPath_mono {xs ys : List (ℕ[X] × ℕ[X])}
    (h : List.Forall₂ (fun x y => CoeffLE x.1 y.1 ∧ CoeffLE x.2 y.2) xs ys) :
    CoeffLE (weightedPath xs).1 (weightedPath ys).1 ∧
      CoeffLE (weightedPath xs).2 (weightedPath ys).2 := by
  induction h with
  | nil => exact ⟨CoeffLE.refl _, CoeffLE.refl _⟩
  | cons hw h ih => exact ⟨(hw.1.mul ih.1).add (hw.2.mul ih.2), hw.1.mul ih.1⟩

theorem forall₂_map_intersperse {α β γ : Type*} (R : β → γ → Prop) (f : α → β) (g : α → γ)
    (s : β) (t : γ) (l : List α) (hst : R s t) (h : ∀ x ∈ l, R (f x) (g x)) :
    List.Forall₂ R ((l.map f).intersperse s) ((l.map g).intersperse t) := by
  induction l with
  | nil => exact .nil
  | cons a l ih =>
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    cases l with
    | nil => exact .cons ha .nil
    | cons b l => exact .cons ha (.cons hst ht)

theorem map_intersperse {α β : Type*} (f : α → β) (sep : α) (l : List α) :
    (l.intersperse sep).map f = (l.map f).intersperse (f sep) := by
  induction l with
  | nil => rfl
  | cons a l ih => cases l with
    | nil => rfl
    | cons b l => simp only [List.intersperse_cons_cons, List.map_cons, ih]

theorem weightedPath_bridge_product_bounds (ls : List (List (ℕ[X] × ℕ[X])))
    (w : ℕ[X] × ℕ[X]) (hw : CoeffLE 1 w.1) :
    CoeffLE (ls.map (fun l => (weightedPath l).1)).prod
      (weightedPath ((ls.intersperse [w]).flatten)).1 ∧
    CoeffLE (weightedPath ((ls.intersperse [w]).flatten)).1
      ((w.1 + w.2) ^ (ls.length - 1) * (ls.map (fun l => (weightedPath l).1)).prod) := by
  induction ls with
  | nil => simp only [List.map_nil, List.prod_nil, List.intersperse_nil, List.flatten_nil,
      List.length_nil, Nat.zero_sub, pow_zero, mul_one]; exact ⟨CoeffLE.refl _, CoeffLE.refl _⟩
  | cons l ls ih =>
    cases ls with
    | nil => simpa only [List.intersperse_singleton, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        List.length_cons, List.length_nil, Nat.zero_add, Nat.sub_self, pow_zero, one_mul, mul_one]
        using (show CoeffLE (weightedPath l).1 (weightedPath l).1 ∧
          CoeffLE (weightedPath l).1 (weightedPath l).1 from ⟨CoeffLE.refl _, CoeffLE.refl _⟩)
    | cons l' ls =>
      have hb := weightedPath_bridge_bounds l (((l' :: ls).intersperse [w]).flatten) w
      simp only [List.intersperse_cons_cons, List.flatten_cons, List.singleton_append,
        List.map_cons, List.prod_cons, List.length_cons] at *
      constructor
      · have h := (hw.mul (CoeffLE.refl (weightedPath l).1)).mul ih.1
        apply CoeffLE.trans _ hb.1
        simpa only [one_mul] using h
      · have h := (CoeffLE.refl ((w.1 + w.2) * (weightedPath l).1)).mul ih.2
        apply hb.2.trans
        convert h using 1 ; simp only [Nat.add_sub_cancel, pow_succ] ; ring

theorem pathStateSum_bridge_product_bounds (ls : List (List Decoration)) (D : Decoration)
    (hw : CoeffLE 1 D.A) :
    CoeffLE (ls.map (fun l => (pathStateSum l).1)).prod
      (pathStateSum ((ls.intersperse [D]).flatten)).1 ∧
    CoeffLE (pathStateSum ((ls.intersperse [D]).flatten)).1
      ((D.A + D.B) ^ (ls.length - 1) * (ls.map (fun l => (pathStateSum l).1)).prod) := by
  have h := weightedPath_bridge_product_bounds
    (ls.map (fun l => l.map (fun D => (D.A,D.B)))) (D.A,D.B) hw
  simpa only [pathStateSum_eq_weightedPath, List.map_flatten, map_intersperse,
    List.map_map, Function.comp_def, List.map_cons, List.map_nil, List.length_map] using h

end TerminalLogConcavity
