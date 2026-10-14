import MeanMaximumForests.Data.Bases0

namespace MeanMaximumForests.Release
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def products00Row025Array : Array (OperationRecord 32) := #[
.recession ⟨0, by decide⟩,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 11,
.basis 24,
.basis 24,
.basis 25,
.basis 25,
.basis 25,
.basis 25,
.basis 25,
.basis 30,
.basis 25,
.basis 30,
.basis 25,
.basis 30,
.basis 25,
.basis 30,
.basis 11,
.basis 17,
.basis 19,
.basis 21,
.basis 12,
.multiple ⟨20, by decide⟩,
.basis 16,
.basis 14,
.basis 13,
.multiple ⟨25, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨31, by decide⟩
]
def products00Row025 (i : Fin 32) : OperationRecord 32 :=
  products00Row025Array[i.val]'(by change i.val < 32; exact i.isLt)
theorem products00Row025_valid : ∀ j : Fin 32, 25 ≤ j.val → (decode0 ((generators0 ⟨25, by decide⟩).product (generators0 j)) (products00Row025 j)).Valid generators0 ((generators0 ⟨25, by decide⟩).product (generators0 j)) := by
  decide

end MeanMaximumForests.Release
