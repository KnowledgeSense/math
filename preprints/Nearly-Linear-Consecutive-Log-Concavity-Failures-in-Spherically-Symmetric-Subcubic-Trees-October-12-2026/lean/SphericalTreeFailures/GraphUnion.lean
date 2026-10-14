import SphericalTreeFailures.GraphCounting
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace SphericalTreeFailures
open Finset
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- Two vertex sets with no edges between them. -/
def Separated (a b : Finset V) : Prop := ∀ u ∈ a, ∀ v ∈ b, ¬ G.Adj u v

theorem independent_union {a b : Finset V} (hab : Separated G a b)
    {s t : Finset V} (hs : s ⊆ a) (ht : t ⊆ b) :
    Independent G (s ∪ t) ↔ Independent G s ∧ Independent G t := by
  constructor
  · intro h
    exact ⟨h.mono G subset_union_left, h.mono G subset_union_right⟩
  · rintro ⟨hi, hj⟩ u hu v hv
    rcases mem_union.mp hu with hu | hu <;> rcases mem_union.mp hv with hv | hv
    · exact hi u hu v hv
    · exact hab u (hs hu) v (ht hv)
    · exact fun h => hab v (hs hv) u (ht hu) h.symm
    · exact hj u hu v hv

theorem independentSetsWithin_union {a b : Finset V} (hab : Separated G a b) :
    independentSetsWithin G (a ∪ b) =
      ((independentSetsWithin G a) ×ˢ (independentSetsWithin G b)).image
        (fun p => p.1 ∪ p.2) := by
  classical
  ext t
  simp only [mem_independentSetsWithin, mem_image, mem_product]
  constructor
  · rintro ⟨ht, hi⟩
    refine ⟨(t ∩ a, t ∩ b), ⟨⟨inter_subset_right, hi.mono G inter_subset_left⟩,
      ⟨inter_subset_right, hi.mono G inter_subset_left⟩⟩, ?_⟩
    ext v
    simp only [mem_union, mem_inter]
    constructor
    · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
    · intro hv
      rcases mem_union.mp (ht hv) with ha | hb
      · exact Or.inl ⟨hv, ha⟩
      · exact Or.inr ⟨hv, hb⟩
  · rintro ⟨⟨s, t⟩, ⟨⟨hs, hi⟩, ⟨ht, hj⟩⟩, rfl⟩
    exact ⟨union_subset_union hs ht, (independent_union G hab hs ht).mpr ⟨hi, hj⟩⟩

theorem union_injective_on_independentSets {a b : Finset V} (hd : Disjoint a b) :
    Set.InjOn (fun p : Finset V × Finset V => p.1 ∪ p.2)
      (↑((independentSetsWithin G a) ×ˢ (independentSetsWithin G b)) : Set _) := by
  intro p hp q hq he
  change p.1 ∪ p.2 = q.1 ∪ q.2 at he
  obtain ⟨hp₁, hp₂⟩ := mem_product.mp hp
  obtain ⟨hq₁, hq₂⟩ := mem_product.mp hq
  have hp₁ := ((mem_independentSetsWithin G).mp hp₁).1
  have hp₂ := ((mem_independentSetsWithin G).mp hp₂).1
  have hq₁ := ((mem_independentSetsWithin G).mp hq₁).1
  have hq₂ := ((mem_independentSetsWithin G).mp hq₂).1
  apply Prod.ext
  · ext v
    constructor
    · intro hv
      have hv' : v ∈ q.1 ∪ q.2 := he ▸ mem_union_left _ hv
      rcases mem_union.mp hv' with hv' | hv'
      · exact hv'
      · exact False.elim (disjoint_left.mp hd (hp₁ hv) (hq₂ hv'))
    · intro hv
      have hv' : v ∈ p.1 ∪ p.2 := he.symm ▸ mem_union_left _ hv
      rcases mem_union.mp hv' with hv' | hv'
      · exact hv'
      · exact False.elim (disjoint_left.mp hd (hq₁ hv) (hp₂ hv'))
  · ext v
    constructor
    · intro hv
      have hv' : v ∈ q.1 ∪ q.2 := he ▸ mem_union_right _ hv
      rcases mem_union.mp hv' with hv' | hv'
      · exact False.elim (disjoint_left.mp hd (hq₁ hv') (hp₂ hv))
      · exact hv'
    · intro hv
      have hv' : v ∈ p.1 ∪ p.2 := he.symm ▸ mem_union_right _ hv
      rcases mem_union.mp hv' with hv' | hv'
      · exact False.elim (disjoint_left.mp hd (hp₁ hv') (hq₂ hv))
      · exact hv'

theorem independentSetCount_union {a b : Finset V} (hd : Disjoint a b)
    (hab : Separated G a b) :
    independentSetCount G (a ∪ b) = independentSetCount G a * independentSetCount G b := by
  classical
  unfold independentSetCount
  rw [independentSetsWithin_union G hab,
    card_image_of_injOn (union_injective_on_independentSets G hd), card_product]

theorem independentSetSizeSum_union {a b : Finset V} (hd : Disjoint a b)
    (hab : Separated G a b) :
    independentSetSizeSum G (a ∪ b) =
      independentSetSizeSum G a * independentSetCount G b +
      independentSetCount G a * independentSetSizeSum G b := by
  classical
  unfold independentSetSizeSum independentSetCount
  rw [independentSetsWithin_union G hab,
    sum_image (union_injective_on_independentSets G hd)]
  have he : ∀ p ∈ ((independentSetsWithin G a) ×ˢ (independentSetsWithin G b)),
      (p.1 ∪ p.2).card = p.1.card + p.2.card := by
    intro p hp
    obtain ⟨hpa, hpb⟩ := mem_product.mp hp
    apply card_union_of_disjoint
    exact hd.mono ((mem_independentSetsWithin G).mp hpa).1
      ((mem_independentSetsWithin G).mp hpb).1
  rw [sum_congr rfl he, sum_product]
  simp_rw [sum_add_distrib]
  simp [sum_mul, mul_sum, Nat.mul_comm]

theorem independenceNumber_union {a b : Finset V} (hd : Disjoint a b)
    (hab : Separated G a b) :
    independenceNumber G (a ∪ b) = independenceNumber G a + independenceNumber G b := by
  classical
  apply le_antisymm
  · obtain ⟨t, ht, hi, he⟩ := exists_maximum_independentSet G (a ∪ b)
    have hm : t ∈ independentSetsWithin G (a ∪ b) := (mem_independentSetsWithin G).mpr ⟨ht, hi⟩
    rw [independentSetsWithin_union G hab] at hm
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := mem_image.mp hm
    obtain ⟨hu, hv⟩ := mem_product.mp huv
    obtain ⟨hua, hui⟩ := (mem_independentSetsWithin G).mp hu
    obtain ⟨hvb, hvi⟩ := (mem_independentSetsWithin G).mp hv
    rw [← he, card_union_of_disjoint (hd.mono hua hvb)]
    exact Nat.add_le_add (independent_card_le G a hua hui) (independent_card_le G b hvb hvi)
  · obtain ⟨u, hua, hui, hue⟩ := exists_maximum_independentSet G a
    obtain ⟨v, hvb, hvi, hve⟩ := exists_maximum_independentSet G b
    rw [← hue, ← hve, ← card_union_of_disjoint (hd.mono hua hvb)]
    exact independent_card_le G _ (union_subset_union hua hvb)
      ((independent_union G hab hua hvb).mpr ⟨hui, hvi⟩)

end SphericalTreeFailures
