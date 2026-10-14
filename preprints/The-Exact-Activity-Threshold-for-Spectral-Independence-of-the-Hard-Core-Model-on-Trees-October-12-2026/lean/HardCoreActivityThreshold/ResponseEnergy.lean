import HardCoreActivityThreshold.ForestPropagation
import HardCoreActivityThreshold.RootOddsConstruction

/-! Finite-depth squared boundary response, computed from the actual hard-core law. -/
namespace HardCoreActivityThreshold
open Finset Forest
attribute [local instance] Classical.propDecidable

noncomputable def responseEnergy (h : ℕ) (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) : ℝ :=
  ∑ v, if A.depth v < h then (parentEffect A activity ha v)^2 else 0

theorem responseEnergy_nonneg (h : ℕ) (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) : 0 ≤ responseEnergy h A activity ha := by
  apply sum_nonneg
  intro v _
  split_ifs
  · positivity
  · rfl

@[simp] theorem responseEnergy_zero (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) : responseEnergy 0 A activity ha = 0 := by
  simp [responseEnergy]

@[simp] theorem responseEnergy_empty (h : ℕ) (activity : ForestExpr.empty.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) : responseEnergy h .empty activity ha = 0 := by
  exact sum_eq_zero (fun v _ => v.elim)

theorem responseEnergy_union (h : ℕ) (A B : ForestExpr)
    (activity : (A.union B).Vertex → ℝ) (ha : ∀ v, 0 < activity v) :
    responseEnergy h (A.union B) activity ha =
      responseEnergy h A (fun v => activity (.inl v)) (fun v => ha (.inl v)) +
      responseEnergy h B (fun v => activity (.inr v)) (fun v => ha (.inr v)) := by
  unfold responseEnergy
  rw [Fintype.sum_sum_type]
  simp only [ForestExpr.depth, parentEffect, forestMarginal_union_left, forestMarginal_union_right]

theorem responseEnergy_root (h : ℕ) (A : ForestExpr)
    (activity : A.root.Vertex → ℝ) (ha : ∀ v, 0 < activity v) :
    responseEnergy (h+1) A.root activity ha = downwardOccupation A activity ^ 2 *
      (1 + responseEnergy h A (fun v => activity (some v)) (fun v => ha (some v))) := by
  unfold responseEnergy
  rw [Fintype.sum_option]
  simp only [ForestExpr.depth, Nat.zero_lt_succ, ↓reduceIte, parentEffect_root, neg_sq,
    Nat.add_lt_add_iff_right, parentEffect_child, mul_pow]
  rw [mul_add, mul_one, mul_sum]
  congr 1
  apply sum_congr rfl
  intro v _
  split_ifs <;> simp

theorem responseEnergy_copies (h : ℕ) (A : ForestExpr) (a : ℝ) (ha : 0 < a) (n : ℕ) :
    responseEnergy h (rootCopies A n) (fun _ => a) (fun _ => ha) =
      n * responseEnergy h A.root (fun _ => a) (fun _ => ha) := by
  induction n with
  | zero => simp [rootCopies]
  | succ n ih =>
    rw [rootCopies, responseEnergy_union, ih]
    push_cast
    ring

end HardCoreActivityThreshold
