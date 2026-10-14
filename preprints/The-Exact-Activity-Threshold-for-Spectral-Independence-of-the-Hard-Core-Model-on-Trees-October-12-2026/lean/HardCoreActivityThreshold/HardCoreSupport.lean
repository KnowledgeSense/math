import HardCoreActivityThreshold.SupportHeatBath
import Mathlib.Data.Fintype.EquivFin

/-! The actual heat-bath state space for positive hard-core activities. -/
namespace HardCoreActivityThreshold
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Removing zero-mass states leaves exactly the independent configurations. -/
def hardCoreSupportEquiv (G : SimpleGraph V) (activity : V → ℝ) (ha : ∀ v, 0 < activity v) :
    (hardCoreLaw G activity ha).Support ≃ {s : Finset V // Independent G s} where
  toFun s := ⟨s.val, (hardCoreLaw_support G activity ha s.val).mp s.property⟩
  invFun s := ⟨s.val, (hardCoreLaw_support G activity ha s.val).mpr s.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

omit [DecidableEq V] in
/-- A nonempty vertex set gives at least two genuine states: the empty set and a singleton. -/
theorem hardCore_support_card_ge_two [Nonempty V] (G : SimpleGraph V)
    (activity : V → ℝ) (ha : ∀ v, 0 < activity v) :
    2 ≤ Fintype.card (hardCoreLaw G activity ha).Support := by
  classical
  apply Nat.succ_le_of_lt
  apply Fintype.one_lt_card_iff.mpr
  let v : V := Classical.ofNonempty
  refine ⟨⟨∅, (hardCoreLaw_support G activity ha ∅).mpr (independent_empty G)⟩,
    ⟨{v}, (hardCoreLaw_support G activity ha {v}).mpr (independent_singleton G v)⟩, ?_⟩
  intro he
  have h := congrArg Subtype.val he
  exact (Finset.singleton_ne_empty v) h.symm

end HardCoreActivityThreshold
