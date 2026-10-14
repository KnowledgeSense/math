import MeanMaximumForests.Data.Bases0

namespace MeanMaximumForests.Release
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def products00Row007Array : Array (OperationRecord 32) := #[
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
.basis 11,
.basis 5,
.multiple ⟨1, by decide⟩,
.multiple ⟨2, by decide⟩,
.multiple ⟨3, by decide⟩,
.basis 24,
.multiple ⟨4, by decide⟩,
.multiple ⟨5, by decide⟩,
.multiple ⟨6, by decide⟩,
.multiple ⟨7, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨31, by decide⟩
]
def products00Row007 (i : Fin 32) : OperationRecord 32 :=
  products00Row007Array[i.val]'(by change i.val < 32; exact i.isLt)
theorem products00Row007_valid : ∀ j : Fin 32, 7 ≤ j.val → (decode0 ((generators0 ⟨7, by decide⟩).product (generators0 j)) (products00Row007 j)).Valid generators0 ((generators0 ⟨7, by decide⟩).product (generators0 j)) := by
  decide

end MeanMaximumForests.Release
