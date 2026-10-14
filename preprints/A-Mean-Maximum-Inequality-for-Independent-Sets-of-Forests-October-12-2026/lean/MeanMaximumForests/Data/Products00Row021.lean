import MeanMaximumForests.Data.Bases0

namespace MeanMaximumForests.Release
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def products00Row021Array : Array (OperationRecord 32) := #[
.recession ⟨0, by decide⟩,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.multiple ⟨2, by decide⟩,
.basis 23,
.multiple ⟨4, by decide⟩,
.basis 22,
.multiple ⟨6, by decide⟩,
.basis 27,
.multiple ⟨8, by decide⟩,
.basis 26,
.multiple ⟨10, by decide⟩,
.basis 29,
.multiple ⟨12, by decide⟩,
.basis 25,
.basis 28,
.multiple ⟨14, by decide⟩,
.basis 20,
.multiple ⟨16, by decide⟩,
.basis 17,
.basis 18,
.multiple ⟨18, by decide⟩,
.basis 10,
.multiple ⟨21, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨31, by decide⟩
]
def products00Row021 (i : Fin 32) : OperationRecord 32 :=
  products00Row021Array[i.val]'(by change i.val < 32; exact i.isLt)
theorem products00Row021_valid : ∀ j : Fin 32, 21 ≤ j.val → (decode0 ((generators0 ⟨21, by decide⟩).product (generators0 j)) (products00Row021 j)).Valid generators0 ((generators0 ⟨21, by decide⟩).product (generators0 j)) := by
  decide

end MeanMaximumForests.Release
