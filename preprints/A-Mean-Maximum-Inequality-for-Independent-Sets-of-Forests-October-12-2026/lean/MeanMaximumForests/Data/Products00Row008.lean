import MeanMaximumForests.Data.Bases0

namespace MeanMaximumForests.Release
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def products00Row008Array : Array (OperationRecord 32) := #[
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
.multiple ⟨2, by decide⟩,
.basis 23,
.multiple ⟨4, by decide⟩,
.basis 25,
.basis 22,
.multiple ⟨6, by decide⟩,
.basis 27,
.multiple ⟨8, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨31, by decide⟩
]
def products00Row008 (i : Fin 32) : OperationRecord 32 :=
  products00Row008Array[i.val]'(by change i.val < 32; exact i.isLt)
theorem products00Row008_valid : ∀ j : Fin 32, 8 ≤ j.val → (decode0 ((generators0 ⟨8, by decide⟩).product (generators0 j)) (products00Row008 j)).Valid generators0 ((generators0 ⟨8, by decide⟩).product (generators0 j)) := by
  decide

end MeanMaximumForests.Release
