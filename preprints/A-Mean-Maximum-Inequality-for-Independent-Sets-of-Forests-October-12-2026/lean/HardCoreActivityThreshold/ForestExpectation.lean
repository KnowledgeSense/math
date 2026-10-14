import HardCoreActivityThreshold.BooleanForest

/-! Exact conditional expectation identities for the hard-core tree recursion. -/
namespace HardCoreActivityThreshold
open Finset Forest
attribute [local instance] Classical.propDecidable

theorem sum_option_config {V : Type*} [Fintype V] [Fintype (Option V → Bool)] [Fintype (V → Bool)] (f : (Option V → Bool) → ℝ) :
    (∑ x, f x) = ∑ b : Bool, ∑ y : V → Bool, f (fun v => v.elim b y) := by
  rw [← (Equiv.piOptionEquivProd (β := fun _ : Option V => Bool)).symm.sum_comp f]
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro y _
  congr 1
  funext v
  cases v <;> rfl

theorem sum_union_config {V W : Type*} [Fintype V] [Fintype W]
    [Fintype (V ⊕ W → Bool)] [Fintype (V → Bool)] [Fintype (W → Bool)]
    (f : (V ⊕ W → Bool) → ℝ) :
    (∑ x, f x) = ∑ y : V → Bool, ∑ z : W → Bool, f (Sum.elim y z) := by
  rw [← (Equiv.sumArrowEquivProdArrow V W Bool).symm.sum_comp f]
  exact Fintype.sum_prod_type _

theorem forestLaw_union_expectation (A B : ForestExpr) (activity : (A.union B).Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (parent : Bool)
    (f : (A.Vertex → Bool) → ℝ) (g : (B.Vertex → Bool) → ℝ) :
    (forestLaw (A.union B) activity ha parent).expectation
      (fun x => f (fun v => x (.inl v)) * g (fun v => x (.inr v))) =
      (forestLaw A (fun v => activity (.inl v)) (fun v => ha (.inl v)) parent).expectation f *
      (forestLaw B (fun v => activity (.inr v)) (fun v => ha (.inr v)) parent).expectation g := by
  unfold FiniteLaw.expectation
  rw [sum_union_config (V := A.Vertex) (W := B.Vertex) (fun x =>
    (forestLaw (A.union B) activity ha parent).mass x *
      (f (fun v => x (.inl v)) * g (fun v => x (.inr v))))]
  simp only [forestLaw_union_mass, Sum.elim_inl, Sum.elim_inr]
  rw [sum_mul_sum]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro z _
  ring

theorem forestLaw_root_free_expectation (A : ForestExpr) (activity : A.root.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (f : (A.root.Vertex → Bool) → ℝ) :
    (forestLaw A.root activity ha false).expectation f =
      (1 - downwardOccupation A activity) *
        (forestLaw A (fun v => activity (some v)) (fun v => ha (some v)) false).expectation
          (fun y => f (fun v => v.elim false y)) +
      downwardOccupation A activity *
        (forestLaw A (fun v => activity (some v)) (fun v => ha (some v)) true).expectation
          (fun y => f (fun v => v.elim true y)) := by
  unfold FiniteLaw.expectation
  rw [sum_option_config (V := A.Vertex) (fun x => (forestLaw A.root activity ha false).mass x * f x)]
  simp only [Fintype.sum_bool, forestLaw_root_free_mass, Option.elim_none, Option.elim_some,
    Bool.false_eq_true, ↓reduceIte, mul_assoc]
  rw [← mul_sum, ← mul_sum]
  ring

theorem forestLaw_root_forced_expectation (A : ForestExpr) (activity : A.root.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (f : (A.root.Vertex → Bool) → ℝ) :
    (forestLaw A.root activity ha true).expectation f =
      (forestLaw A (fun v => activity (some v)) (fun v => ha (some v)) false).expectation
        (fun y => f (fun v => v.elim false y)) := by
  unfold FiniteLaw.expectation
  rw [sum_option_config (V := A.Vertex) (fun x => (forestLaw A.root activity ha true).mass x * f x)]
  simp only [Fintype.sum_bool, forestLaw_root_forced_mass, Option.elim_none, Option.elim_some,
    Bool.false_eq_true, ↓reduceIte, zero_mul, sum_const_zero, zero_add]

noncomputable def boolOccupation {V : Type*} (v : V) (x : V → Bool) : ℝ := if x v then 1 else 0

noncomputable def forestMarginal (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (parent : Bool) (v : A.Vertex) : ℝ :=
  (forestLaw A activity ha parent).expectation (boolOccupation v)

theorem forestMarginal_root_free (A : ForestExpr) (activity : A.root.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) :
    forestMarginal A.root activity ha false none = downwardOccupation A activity := by
  unfold forestMarginal
  rw [forestLaw_root_free_expectation]
  simp [boolOccupation]

@[simp] theorem forestMarginal_root_forced (A : ForestExpr) (activity : A.root.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) : forestMarginal A.root activity ha true none = 0 := by
  unfold forestMarginal
  rw [forestLaw_root_forced_expectation]
  simp [boolOccupation]

theorem forestMarginal_child_free (A : ForestExpr) (activity : A.root.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) :
    forestMarginal A.root activity ha false (some v) =
      (1 - downwardOccupation A activity) *
        forestMarginal A (fun v => activity (some v)) (fun v => ha (some v)) false v +
      downwardOccupation A activity *
        forestMarginal A (fun v => activity (some v)) (fun v => ha (some v)) true v := by
  unfold forestMarginal
  rw [forestLaw_root_free_expectation]
  rfl

theorem forestMarginal_child_forced (A : ForestExpr) (activity : A.root.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) :
    forestMarginal A.root activity ha true (some v) =
      forestMarginal A (fun v => activity (some v)) (fun v => ha (some v)) false v := by
  unfold forestMarginal
  rw [forestLaw_root_forced_expectation]
  rfl

end HardCoreActivityThreshold
