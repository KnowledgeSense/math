import MeanMaximumForests.Data.Bases0

namespace MeanMaximumForests.Release
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def products00Row030Array : Array (OperationRecord 32) := #[
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨30, by decide⟩,
.zero,
.zero
]
def products00Row030 (i : Fin 32) : OperationRecord 32 :=
  products00Row030Array[i.val]'(by change i.val < 32; exact i.isLt)
theorem products00Row030_valid : ∀ j : Fin 32, 30 ≤ j.val → (decode0 ((generators0 ⟨30, by decide⟩).product (generators0 j)) (products00Row030 j)).Valid generators0 ((generators0 ⟨30, by decide⟩).product (generators0 j)) := by
  decide

end MeanMaximumForests.Release
