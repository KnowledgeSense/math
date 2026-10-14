import Dowling.BalancedComponents
import Dowling.GainCirclesLinks

noncomputable section
namespace Dowling
variable {G : Type*} [Group G] {n : ℕ}

/-- Balanced components in the ordinary gain-graph convention: every genuine
polygon has identity gain and the component contains no retained joint. -/
def PolygonBalancedComponent (S : Set (Edge G n)) :=
  {c : Component S // ∃ i, Quotient.mk (componentSetoid S) i = c ∧ PolygonBalancedAt S i}

def polygonBalancedCount (S : Set (Edge G n)) : ℕ := Nat.card (PolygonBalancedComponent S)

def balancedComponentPolygonEquiv (S : Set (Edge G n)) :
    BalancedComponent S ≃ PolygonBalancedComponent S where
  toFun c := ⟨c.val, by
    obtain ⟨i,hi,hb⟩ := c.property
    exact ⟨i,hi,(balancedAt_iff_polygonBalancedAt i).mp hb⟩⟩
  invFun c := ⟨c.val, by
    obtain ⟨i,hi,hb⟩ := c.property
    exact ⟨i,hi,(balancedAt_iff_polygonBalancedAt i).mpr hb⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem balancedCount_eq_polygonBalancedCount (S : Set (Edge G n)) :
    balancedCount S = polygonBalancedCount S :=
  Nat.card_congr (balancedComponentPolygonEquiv S)

/-- Every subset of the actual retained-joint ground has precisely the standard
frame-matroid rank. Isolated vertices and all forced-zero components are included. -/
theorem matroid_eRk_source [Finite G] (X : Set (Fin n)) (S : Set (Edge G n))
    (hS : S ⊆ ground G n X) :
    (matroid G n X).eRk S = ((n - polygonBalancedCount S : ℕ) : ℕ∞) := by
  rw [matroid_eRk_balanced X S hS, balancedCount_eq_polygonBalancedCount]

end Dowling
