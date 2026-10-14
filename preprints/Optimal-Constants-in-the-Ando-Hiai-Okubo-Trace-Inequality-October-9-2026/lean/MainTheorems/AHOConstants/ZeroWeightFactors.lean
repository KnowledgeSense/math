import MainTheorems.AHOConstants.SchattenHolder

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open ResearchMain.DiagonalSchatten

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def positiveFactors (fs : List (SchattenFactor I)) : List (SchattenFactor I) :=
  fs.filter (fun f => 0 < f.weight)

theorem positiveFactors_product {fs : List (SchattenFactor I)}
    (hn : ∀ f ∈ fs, 0 ≤ f.weight)
    (hz : ∀ f ∈ fs, f.weight = 0 → f.matrix = 1) :
    ((positiveFactors fs).map SchattenFactor.matrix).prod =
      (fs.map SchattenFactor.matrix).prod := by
  classical
  revert hn hz
  induction fs with
  | nil => intro _ _; rfl
  | cons f fs ih =>
    intro hn hz
    have ht := ih (fun g hg => hn g (by simp [hg]))
      (fun g hg => hz g (by simp [hg]))
    by_cases hp : 0 < f.weight
    · simpa [positiveFactors, hp] using congrArg (fun X => f.matrix * X) ht
    · have hw : f.weight = 0 := le_antisymm (le_of_not_gt hp) (hn f (by simp))
      simpa [positiveFactors, hp, hz f (by simp) hw] using ht

theorem positiveFactors_weight_sum {fs : List (SchattenFactor I)}
    (hn : ∀ f ∈ fs, 0 ≤ f.weight) :
    ((positiveFactors fs).map SchattenFactor.weight).sum =
      (fs.map SchattenFactor.weight).sum := by
  classical
  revert hn
  induction fs with
  | nil => intro _; rfl
  | cons f fs ih =>
    intro hn
    have ht := ih (fun g hg => hn g (by simp [hg]))
    by_cases hp : 0 < f.weight
    · simpa [positiveFactors, hp] using congrArg (fun x => f.weight + x) ht
    · have hw : f.weight = 0 := le_antisymm (le_of_not_gt hp) (hn f (by simp))
      simpa [positiveFactors, hp, hw] using ht

theorem list_product_bound {α : Type*} (xs : List α) (f g : α → ℝ)
    (h : ∀ x ∈ xs, 0 ≤ f x ∧ f x ≤ g x) :
    (xs.map f).prod ≤ (xs.map g).prod := by
  revert h
  induction xs with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    have hn : 0 ≤ (xs.map f).prod := by
      apply List.prod_nonneg
      intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      exact (h y (by simp [hy])).1
    exact mul_le_mul hx.2 ht hn (hx.1.trans hx.2)

theorem list_product_rpow {α : Type*} {D : ℝ} (hD : 0 < D)
    (xs : List α) (w : α → ℝ) :
    (xs.map (fun x => D ^ w x)).prod = D ^ (xs.map w).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, ih, Real.rpow_add hD]

theorem weighted_schatten_trace_bound [Nonempty I] {D : ℝ} (hD : 0 < D)
    (fs : List (SchattenFactor I)) (hn : ∀ f ∈ fs, 0 ≤ f.weight)
    (hsum : (fs.map SchattenFactor.weight).sum = 1)
    (hz : ∀ f ∈ fs, f.weight = 0 → f.matrix = 1)
    (hb : ∀ f ∈ fs, 0 < f.weight → schattenNorm (1 / f.weight) f.matrix ≤ D ^ f.weight) :
    ‖Matrix.trace ((fs.map SchattenFactor.matrix).prod)‖ ≤ D := by
  classical
  have hp : ∀ f ∈ positiveFactors fs, 0 < f.weight := by
    intro f hf
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp hf).2
  have hps : ((positiveFactors fs).map SchattenFactor.weight).sum = 1 :=
    (positiveFactors_weight_sum hn).trans hsum
  have hh := schatten_list_trace_holder (positiveFactors fs) hp hps
  rw [positiveFactors_product hn hz] at hh
  have hbound := list_product_bound (positiveFactors fs)
    (fun f => schattenNorm (1 / f.weight) f.matrix) (fun f => D ^ f.weight)
    (by intro f hf; exact ⟨schattenNorm_nonneg _ _,
      hb f (List.mem_filter.mp hf).1 (hp f hf)⟩)
  rw [list_product_rpow hD, hps, Real.rpow_one] at hbound
  exact hh.trans hbound

end ResearchMain.AHOConstants
