import MeanMaximumForests.Data.Generators
import Mathlib.Data.List.Nodup

namespace MeanMaximumForests

/-- A primitive integer vector has no common positive divisor other than one. -/
def IntegerVector.Primitive (v : IntegerVector) : Prop :=
  Nat.gcd (Nat.gcd v.p.natAbs v.q.natAbs) (Nat.gcd v.x.natAbs v.y.natAbs) = 1

/-- Every signed coordinate is representable using at most `b` magnitude bits. -/
def IntegerVector.CoordinatesBelow (v : IntegerVector) (b : ℕ) : Prop :=
  v.p.natAbs < 2 ^ b ∧ v.q.natAbs < 2 ^ b ∧ v.x.natAbs < 2 ^ b ∧ v.y.natAbs < 2 ^ b

namespace Release
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Exact primality-of-content checks for the first release generator list. -/
theorem generators0_primitive : ∀ i : Fin 32, (generators0 i).Primitive := by unfold IntegerVector.Primitive; decide

/-- Exact primality-of-content checks for the second release generator list. -/
theorem generators1_primitive : ∀ i : Fin 331, (generators1 i).Primitive := by unfold IntegerVector.Primitive; decide

theorem generators0_bits : ∀ i : Fin 32, (generators0 i).CoordinatesBelow 87 := by unfold IntegerVector.CoordinatesBelow; decide

theorem generators1_bits : ∀ i : Fin 331, (generators1 i).CoordinatesBelow 87 := by unfold IntegerVector.CoordinatesBelow; decide

theorem generators0_nodup : ((List.finRange 32).map generators0).Nodup := by decide

theorem generators1_nodup : ((List.finRange 331).map generators1).Nodup := by decide

theorem generators0_injective : Function.Injective generators0 := by
  intro i j h
  exact List.inj_on_of_nodup_map generators0_nodup (by simp) (by simp) h

theorem generators1_injective : Function.Injective generators1 := by
  intro i j h
  exact List.inj_on_of_nodup_map generators1_nodup (by simp) (by simp) h

end Release
end MeanMaximumForests
