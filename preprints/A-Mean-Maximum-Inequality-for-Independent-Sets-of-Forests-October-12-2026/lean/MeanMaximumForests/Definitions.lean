import Mathlib.Basic.Real.Basic

/-! Algebraic objects for the invariant-cone argument. -/
namespace MeanMaximumForests

@[ext] structure ConeVector where
  p : ℝ
  q : ℝ
  x : ℝ
  y : ℝ

def unitVector : ConeVector := ⟨1, 1, 0, 0⟩
def product (v w : ConeVector) : ConeVector :=
  ⟨v.p * w.p, v.q * w.q, v.x * w.p + v.p * w.x, v.y * w.q + v.q * w.y⟩
def plant (c : ℝ) (f : Bool) (v : ConeVector) : ConeVector :=
  let b : ℝ := if f then 0 else 1
  ⟨v.p + v.q, v.p, v.x + v.y + (1 - c * b) * v.q - c * b * v.p,
    v.x - c * b * v.p⟩

inductive ForestExpr where
  | empty
  | union (left right : ForestExpr)
  | root (children : ForestExpr)

def flag : ForestExpr → Bool
  | .empty => false
  | .union a b => flag a || flag b
  | .root a => !(flag a)
def vector (c : ℝ) : ForestExpr → ConeVector
  | .empty => unitVector
  | .union a b => product (vector c a) (vector c b)
  | .root a => plant c (flag a) (vector c a)

structure InvariantConditions (c : ℝ) (C : Bool → Set ConeVector) : Prop where
  empty : unitVector ∈ C false
  product : ∀ f g v w, v ∈ C f → w ∈ C g → product v w ∈ C (f || g)
  plant : ∀ f v, v ∈ C f → plant c f v ∈ C (!f)
  sign : ∀ f v, v ∈ C f → 0 ≤ (MeanMaximumForests.plant c f v).x

end MeanMaximumForests
