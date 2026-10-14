import SumsetRanges.IntervalSums

open Finset
namespace SumsetRanges

section
variable {α : Type*} [AddCommMonoid α] [DecidableEq α]

theorem restrictedSums_insert_succ (A : Finset α) (x : α) (hx : x∉A) (q : ℕ) :
    restrictedSums (insert x A) (q+1) = restrictedSums A (q+1) ∪
      (restrictedSums A q).image (fun y => x+y) := by
  ext y
  constructor
  · intro hy
    obtain ⟨S,hS,hSc,hSy⟩ := mem_restrictedSums.mp hy
    by_cases hxs : x∈S
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨∑ a∈S.erase x,a,mem_restrictedSums.mpr ⟨S.erase x,?_,?_,rfl⟩,?_⟩
      · intro a ha
        obtain ⟨hax,haS⟩ := Finset.mem_erase.mp ha
        rcases Finset.mem_insert.mp (hS haS) with h | h
        · exact False.elim (hax h)
        · exact h
      · rw [Finset.card_erase_of_mem hxs,hSc]
        omega
      · rw [← hSy,← Finset.add_sum_erase _ _ hxs]
    · apply Finset.mem_union_left
      refine mem_restrictedSums.mpr ⟨S,?_,hSc,hSy⟩
      intro a ha
      rcases Finset.mem_insert.mp (hS ha) with h | h
      · exact False.elim (hxs (h ▸ ha))
      · exact h
  · intro hy
    rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨S,hS,hSc,hSy⟩ := mem_restrictedSums.mp hy
      exact mem_restrictedSums.mpr ⟨S,fun a ha => Finset.mem_insert_of_mem (hS ha),hSc,hSy⟩
    · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨S,hS,hSc,rfl⟩ := mem_restrictedSums.mp hz
      have hxs : x∉S := fun h => hx (hS h)
      refine mem_restrictedSums.mpr ⟨insert x S,Finset.insert_subset_insert x hS,?_,?_⟩
      · rw [Finset.card_insert_of_notMem hxs,hSc]
      · rw [Finset.sum_insert hxs]

end

section
variable {α : Type*} [AddCommMonoid α] [IsCancelAdd α] [DecidableEq α]

theorem restrictedSums_translate (A : Finset α) (x : α) (q : ℕ) :
    restrictedSums (A.image (fun a => x+a)) q =
      (restrictedSums A q).image (fun y => q • x+y) := by
  let e : α ↪ α := ⟨fun a => x+a,fun _ _ h => add_left_cancel h⟩
  have he : A.image (fun a => x+a)=A.map e := by rw [Finset.map_eq_image]; rfl
  rw [he,restrictedSums_map]
  unfold restrictedSums
  rw [Finset.image_image]
  apply Finset.image_congr
  intro S hS
  have hc := (Finset.mem_powersetCard.mp hS).2
  change S.sum (fun a => x + a) = q • x + S.sum id
  rw [Finset.sum_add_distrib,Finset.sum_const,hc]
  rfl

end

@[simp] theorem restrictedSums_range_of_lt (n q : ℕ) (hnq : n<q) :
    restrictedSums (range n) q = ∅ := by
  apply Finset.card_eq_zero.mp
  have h := card_restrictedSums_le (range n) q
  simp only [Finset.card_range,Nat.choose_eq_zero_of_lt hnq] at h
  omega

end SumsetRanges
