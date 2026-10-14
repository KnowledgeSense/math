import MeanMaximumForests.Data.Bases0

namespace MeanMaximumForests.Release
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def products00Row031Array : Array (OperationRecord 32) := #[
.zero,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.multiple ⟨31, by decide⟩,
.zero,
.zero
]
def products00Row031 (i : Fin 32) : OperationRecord 32 :=
  products00Row031Array[i.val]'(by change i.val < 32; exact i.isLt)
theorem products00Row031_valid : ∀ j : Fin 32, 31 ≤ j.val → (decode0 ((generators0 ⟨31, by decide⟩).product (generators0 j)) (products00Row031 j)).Valid generators0 ((generators0 ⟨31, by decide⟩).product (generators0 j)) := by
  decide

end MeanMaximumForests.Release
