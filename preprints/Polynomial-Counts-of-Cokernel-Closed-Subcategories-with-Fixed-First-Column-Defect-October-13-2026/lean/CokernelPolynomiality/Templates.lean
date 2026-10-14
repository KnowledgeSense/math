import CokernelPolynomiality.Codes
import Mathlib.Data.Finset.Card

namespace CokernelPolynomiality

 theorem normalized_size_le {i q : ℕ} (c : Code i q) (hc : c.IsNormalized) : q ≤ 2*i := by
  classical
  have hs : (Finset.univ.erase 0 : Finset (Fin (q+1))) ⊆
      Finset.univ.image c.d ∪ Finset.univ.image c.y := by
    intro k hk
    obtain ⟨j,hj⟩ := hc k (Finset.ne_of_mem_erase hk)
    rcases hj with hd | hy
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hd⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hy⟩)
  calc
    q = (Finset.univ.erase (0 : Fin (q+1))).card := by simp
    _ ≤ (Finset.univ.image c.d ∪ Finset.univ.image c.y).card := Finset.card_le_card hs
    _ ≤ (Finset.univ.image c.d).card + (Finset.univ.image c.y).card := Finset.card_union_le _ _
    _ ≤ (Finset.univ : Finset (Fin i)).card + (Finset.univ : Finset (Fin i)).card :=
      Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
    _ = 2*i := by simp; omega

 theorem templateCount_eq_zero_of_lt {i q : ℕ} (hq : 2*i < q) : templateCount i q = 0 := by
  classical
  unfold templateCount
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun c => (Nat.not_le_of_gt hq) (normalized_size_le c.val c.property.2)⟩

/-- Combine the placement and neighborhood cutoff coordinates. -/
def Code.coordinate {i q : ℕ} (c : Code i q) : Fin i ⊕ Fin i → Fin (q+1)
  | .inl j => c.d j
  | .inr j => c.y j

 theorem normalized_coordinate_covers {i q : ℕ} (c : Code i q) (hc : c.IsNormalized)
    (k : Fin q) : ∃ j, c.coordinate j = k.succ := by
  obtain ⟨j,hj⟩ := hc k.succ (Fin.succ_ne_zero k)
  rcases hj with hd | hy
  · exact ⟨Sum.inl j, hd⟩
  · exact ⟨Sum.inr j, hy⟩

/-- At the largest possible template size, every coordinate is positive and
all placement/cutoff coordinates are pairwise distinct. -/
 theorem top_coordinates_bijective {i : ℕ} (c : Code i (2*i)) (hc : c.IsNormalized) :
    Function.Injective c.coordinate ∧ ∀ j, c.coordinate j ≠ 0 := by
  classical
  let g : Fin (2*i) → Fin i ⊕ Fin i := fun k =>
    Classical.choose (normalized_coordinate_covers c hc k)
  have hg : ∀ k, c.coordinate (g k) = k.succ :=
    fun k => Classical.choose_spec (normalized_coordinate_covers c hc k)
  have hgi : Function.Injective g := by
    intro j k hjk
    have hh := congrArg c.coordinate hjk
    rw [hg j, hg k] at hh
    exact Fin.succ_inj.mp hh
  have hgc : Fintype.card (Fin (2*i)) = Fintype.card (Fin i ⊕ Fin i) := by simp; omega
  have hgs : Function.Surjective g := by
    by_contra hs
    have hh := Fintype.card_lt_of_injective_not_surjective g hgi hs
    omega
  constructor
  · intro j k hjk
    obtain ⟨j',rfl⟩ := hgs j
    obtain ⟨k',rfl⟩ := hgs k
    rw [hg j',hg k'] at hjk
    exact congrArg g (Fin.succ_inj.mp hjk)
  · intro j
    obtain ⟨j',rfl⟩ := hgs j
    rw [hg j']
    exact Fin.succ_ne_zero _

end CokernelPolynomiality
