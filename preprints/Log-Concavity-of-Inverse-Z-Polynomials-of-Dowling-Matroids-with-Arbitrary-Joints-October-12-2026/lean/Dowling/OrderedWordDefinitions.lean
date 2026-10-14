import Dowling.PartitionFibers

noncomputable section
namespace Dowling
open scoped Classical BigOperators

/-- A labelled list of nonempty free blocks and one optional zero block. -/
def OccupiedWord (n k : ℕ) := {w : Fin n → Option (Fin k) // ∀ c, ∃ i, w i=some c}

namespace OccupiedWord
variable {n k : ℕ}

def fiber (w : OccupiedWord n k) (c : Option (Fin k)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => w.val i=c)

theorem fiber_nonempty (w : OccupiedWord n k) (c : Fin k) : (w.fiber (some c)).Nonempty := by
  obtain ⟨i,hi⟩ := w.property c
  exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩

/-- The unique canonical anchor is the least vertex in each free block. -/
def root (w : OccupiedWord n k) (c : Fin k) : Fin n :=
  (w.fiber (some c)).min' (w.fiber_nonempty c)

theorem root_color (w : OccupiedWord n k) (c : Fin k) : w.val (w.root c)=some c := by
  have h : w.root c ∈ w.fiber (some c) := Finset.min'_mem (w.fiber (some c)) (w.fiber_nonempty c)
  exact (Finset.mem_filter.mp h).2

theorem root_le (w : OccupiedWord n k) (c : Fin k) (i : Fin n) (hi : w.val i=some c) : w.root c ≤ i :=
  Finset.min'_le (w.fiber (some c)) i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)

theorem root_injective (w : OccupiedWord n k) : Function.Injective w.root := by
  intro c d h
  apply Option.some.inj
  exact (w.root_color c).symm.trans ((congrArg w.val h).trans (w.root_color d))

/-- Only non-anchor vertices carry independent labels; anchors are normalized to one. -/
def Nonanchor (w : OccupiedWord n k) (c : Fin k) :=
  {i : Fin n // w.val i=some c ∧ i≠w.root c}

instance (w : OccupiedWord n k) (c : Fin k) : Fintype (w.Nonanchor c) :=
  inferInstanceAs (Fintype {i : Fin n // w.val i=some c ∧ i≠w.root c})

def Labels (G : Type*) (w : OccupiedWord n k) := ∀ c : Fin k, w.Nonanchor c → G

instance (G : Type*) [Fintype G] (w : OccupiedWord n k) : Fintype (w.Labels G) :=
  inferInstanceAs (Fintype (∀ c : Fin k, w.Nonanchor c → G))

theorem nonanchor_card (w : OccupiedWord n k) (c : Fin k) :
    Fintype.card (w.Nonanchor c) = (w.fiber (some c)).card-1 := by
  change Fintype.card {i : Fin n // w.val i=some c ∧ i≠w.root c} = _
  rw [Fintype.card_subtype]
  have he : Finset.univ.filter (fun i => w.val i=some c ∧ i≠w.root c) =
      (w.fiber (some c)).erase (w.root c) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,fiber]
    tauto
  rw [he,Finset.card_erase_of_mem]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,w.root_color c⟩

theorem labels_card (G : Type*) [Fintype G] (w : OccupiedWord n k) :
    Fintype.card (w.Labels G) = ∏ c : Fin k, (Fintype.card G)^((w.fiber (some c)).card-1) := by
  change Fintype.card (∀ c : Fin k, w.Nonanchor c → G) = _
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro c _
  rw [Fintype.card_fun,w.nonanchor_card c]

end OccupiedWord
end Dowling
