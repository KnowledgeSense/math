import MeanMaximumForests.Data.Bases0

namespace MeanMaximumForests.Release
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def products00Row010Array : Array (OperationRecord 32) := #[
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
.multiple ⟨2, by decide⟩,
.basis 11,
.basis 23,
.multiple ⟨4, by decide⟩,
.basis 22,
.multiple ⟨6, by decide⟩,
.basis 25,
.basis 27,
.multiple ⟨8, by decide⟩,
.basis 26,
.multiple ⟨10, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨31, by decide⟩
]
def products00Row010 (i : Fin 32) : OperationRecord 32 :=
  products00Row010Array[i.val]'(by change i.val < 32; exact i.isLt)
theorem products00Row010_valid : ∀ j : Fin 32, 10 ≤ j.val → (decode0 ((generators0 ⟨10, by decide⟩).product (generators0 j)) (products00Row010 j)).Valid generators0 ((generators0 ⟨10, by decide⟩).product (generators0 j)) := by
  decide

end MeanMaximumForests.Release
