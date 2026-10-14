import MeanMaximumForests.Data.Bases0

namespace MeanMaximumForests.Release
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def products00Row000Array : Array (OperationRecord 32) := #[
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.recession ⟨0, by decide⟩,
.multiple ⟨0, by decide⟩,
.multiple ⟨30, by decide⟩,
.zero
]
def products00Row000 (i : Fin 32) : OperationRecord 32 :=
  products00Row000Array[i.val]'(by change i.val < 32; exact i.isLt)
theorem products00Row000_valid : ∀ j : Fin 32, 0 ≤ j.val → (decode0 ((generators0 ⟨0, by decide⟩).product (generators0 j)) (products00Row000 j)).Valid generators0 ((generators0 ⟨0, by decide⟩).product (generators0 j)) := by
  decide

end MeanMaximumForests.Release
