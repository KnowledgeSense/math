import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Int.Defs
import Lean.Elab.Tactic.Omega

namespace ResearchMain.PreorderReciprocity

variable {E : Type*} [Fintype E] [Preorder E]

def IsIdeal (I : Finset E) : Prop :=
  ∀ ⦃i j : E⦄, j ∈ I → i ≤ j → i ∈ I

def ClosedIntegerPoints (r s : ℤ) (x : E → ℤ) : Prop :=
  (∀ e, 0 ≤ x e) ∧
  ∀ I : Finset E, I.Nonempty → IsIdeal I →
    ∑ e ∈ I, x e ≤ r * I.card + s

def StrictIntegerPoints (r s : ℤ) (x : E → ℤ) : Prop :=
  (∀ e, 0 < x e) ∧
  ∀ I : Finset E, I.Nonempty → IsIdeal I →
    ∑ e ∈ I, x e < r * I.card + s

theorem univ_isIdeal : IsIdeal (Finset.univ : Finset E) := by
  intro i j _ _
  exact Finset.mem_univ i

theorem integer_coordinate_bound {r s : ℤ} {x : E → ℤ}
    (hx : ClosedIntegerPoints r s x) (e : E) :
    x e ≤ r * Fintype.card E + s := by
  have he : (Finset.univ : Finset E).Nonempty := ⟨e, Finset.mem_univ e⟩
  have hs := hx.2 Finset.univ he univ_isIdeal
  have hb : x e ≤ ∑ i : E, x i :=
    Finset.single_le_sum (fun i _ => hx.1 i) (Finset.mem_univ e)
  simpa using hb.trans hs

theorem zero_parameters {x : E → ℤ} :
    ClosedIntegerPoints 0 0 x ↔ x = 0 := by
  constructor
  · intro hx
    funext e
    have hb := integer_coordinate_bound hx e
    have hp := hx.1 e
    simp only [zero_mul, add_zero] at hb
    exact le_antisymm hb hp
  · rintro rfl
    simp [ClosedIntegerPoints]

end ResearchMain.PreorderReciprocity
