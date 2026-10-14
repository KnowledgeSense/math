import MeanMaximumForests.Data.Bases0

namespace MeanMaximumForests.Release
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def products00Row001Array : Array (OperationRecord 32) := #[
.recession ⟨0, by decide⟩,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.multiple ⟨1, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨31, by decide⟩
]
def products00Row001 (i : Fin 32) : OperationRecord 32 :=
  products00Row001Array[i.val]'(by change i.val < 32; exact i.isLt)
theorem products00Row001_valid : ∀ j : Fin 32, 1 ≤ j.val → (decode0 ((generators0 ⟨1, by decide⟩).product (generators0 j)) (products00Row001 j)).Valid generators0 ((generators0 ⟨1, by decide⟩).product (generators0 j)) := by
  decide

end MeanMaximumForests.Release
