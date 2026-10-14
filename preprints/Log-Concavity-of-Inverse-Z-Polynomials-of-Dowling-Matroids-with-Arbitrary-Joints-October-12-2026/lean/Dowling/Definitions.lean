import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/-! Literal complete gain graph with arbitrary retained joints.
The adjoined zero is `none`, not the identity of the group. -/
noncomputable section
namespace Dowling
open scoped Classical

variable (G : Type*) [Group G] (n : ℕ)

/-- One chosen orientation of every link; reversing it inverts its gain. -/
structure Link where
  tail : Fin n
  head : Fin n
  ordered : tail < head
  gain : G

/-- Joints and links remain distinct ground elements. -/
abbrev Edge := Sum (Fin n) (Link G n)

/-- Right gain action extended by a fixed zero. -/
def gainAct (x : Option G) (g : G) : Option G := x.map (· * g)

/-- The joint at i is retained precisely when i belongs to X. -/
def ground (X : Set (Fin n)) : Set (Edge G n) :=
  {e | match e with
    | Sum.inl i => i ∈ X
    | Sum.inr _ => True}

/-- An assignment satisfies the actual gain equation of an edge. -/
def Satisfies (x : Fin n → Option G) : Edge G n → Prop
  | Sum.inl i => x i = none
  | Sum.inr e => x e.head = gainAct G (x e.tail) e.gain

/-- All simultaneous solutions of the selected edge equations. -/
def solutions (S : Set (Edge G n)) : Set (Fin n → Option G) :=
  {x | ∀ e ∈ S, Satisfies G n x e}

end Dowling
