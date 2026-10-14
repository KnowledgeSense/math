import MeanMaximumForests.Data.Bases1

namespace MeanMaximumForests.Release
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def roots0Array : Array (OperationRecord 331) := #[
.recession ⟨328, by decide⟩,
.recession ⟨327, by decide⟩,
.recession ⟨326, by decide⟩,
.recession ⟨325, by decide⟩,
.recession ⟨324, by decide⟩,
.recession ⟨323, by decide⟩,
.recession ⟨322, by decide⟩,
.recession ⟨321, by decide⟩,
.recession ⟨320, by decide⟩,
.recession ⟨319, by decide⟩,
.recession ⟨318, by decide⟩,
.recession ⟨317, by decide⟩,
.recession ⟨316, by decide⟩,
.recession ⟨315, by decide⟩,
.recession ⟨314, by decide⟩,
.recession ⟨313, by decide⟩,
.recession ⟨312, by decide⟩,
.recession ⟨311, by decide⟩,
.recession ⟨310, by decide⟩,
.recession ⟨309, by decide⟩,
.basis 7,
.recession ⟨308, by decide⟩,
.recession ⟨307, by decide⟩,
.recession ⟨306, by decide⟩,
.recession ⟨305, by decide⟩,
.basis 1,
.recession ⟨304, by decide⟩,
.recession ⟨303, by decide⟩,
.basis 245,
.recession ⟨302, by decide⟩,
.basis 12,
.multiple ⟨329, by decide⟩
]
def roots0 (i : Fin 32) : OperationRecord 331 :=
  roots0Array[i.val]'(by change i.val < 32; exact i.isLt)
theorem roots0_valid : ∀ i : Fin 32, (decode1 ((generators0 i).root100 false) (roots0 i)).Valid generators1 ((generators0 i).root100 false) := by
  decide

end MeanMaximumForests.Release
