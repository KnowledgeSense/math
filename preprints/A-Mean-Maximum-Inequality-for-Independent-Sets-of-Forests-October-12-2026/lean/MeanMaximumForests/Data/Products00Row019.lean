import MeanMaximumForests.Data.Bases0

namespace MeanMaximumForests.Release
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def products00Row019Array : Array (OperationRecord 32) := #[
.recession ⟨0, by decide⟩,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.basis 5,
.multiple ⟨1, by decide⟩,
.multiple ⟨2, by decide⟩,
.multiple ⟨3, by decide⟩,
.multiple ⟨4, by decide⟩,
.multiple ⟨5, by decide⟩,
.multiple ⟨6, by decide⟩,
.multiple ⟨7, by decide⟩,
.multiple ⟨8, by decide⟩,
.multiple ⟨9, by decide⟩,
.multiple ⟨10, by decide⟩,
.multiple ⟨11, by decide⟩,
.basis 25,
.multiple ⟨12, by decide⟩,
.multiple ⟨13, by decide⟩,
.multiple ⟨14, by decide⟩,
.multiple ⟨15, by decide⟩,
.basis 30,
.multiple ⟨16, by decide⟩,
.multiple ⟨17, by decide⟩,
.multiple ⟨18, by decide⟩,
.multiple ⟨19, by decide⟩,
.multiple ⟨30, by decide⟩,
.multiple ⟨31, by decide⟩
]
def products00Row019 (i : Fin 32) : OperationRecord 32 :=
  products00Row019Array[i.val]'(by change i.val < 32; exact i.isLt)
theorem products00Row019_valid : ∀ j : Fin 32, 19 ≤ j.val → (decode0 ((generators0 ⟨19, by decide⟩).product (generators0 j)) (products00Row019 j)).Valid generators0 ((generators0 ⟨19, by decide⟩).product (generators0 j)) := by
  decide

end MeanMaximumForests.Release
