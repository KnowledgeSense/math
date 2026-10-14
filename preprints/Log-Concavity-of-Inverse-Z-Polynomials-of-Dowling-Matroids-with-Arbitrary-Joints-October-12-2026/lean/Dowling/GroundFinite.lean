import Dowling.Definitions
import Mathlib.Data.Fintype.Basic

noncomputable section
namespace Dowling
variable (G : Type*) [Group G] (n : ℕ)

def linkEquiv : Link G n ≃ {v : Fin n × Fin n × G // v.1 < v.2.1} where
  toFun e := ⟨(e.tail,e.head,e.gain),e.ordered⟩
  invFun v := ⟨v.val.1,v.val.2.1,v.property,v.val.2.2⟩
  left_inv e := by cases e; rfl
  right_inv v := by cases v; rfl

instance [Finite G] : Finite (Link G n) := by
  let := Fintype.ofFinite G
  exact Finite.of_equiv {v : Fin n × Fin n × G // v.1 < v.2.1} (linkEquiv G n).symm
instance [Fintype G] : Fintype (Link G n) := Fintype.ofFinite _

instance [Finite G] : Finite (Edge G n) := by
  let := Fintype.ofFinite G
  exact Finite.of_fintype (Edge G n)

end Dowling
