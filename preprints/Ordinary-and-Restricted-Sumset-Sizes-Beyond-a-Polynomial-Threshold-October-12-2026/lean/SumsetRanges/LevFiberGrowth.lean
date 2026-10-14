import SumsetRanges.LevNormalization

open Finset
namespace SumsetRanges

/-- A positive translate of every point of `T` supplies at least one new point in
    each quotient fiber represented by `U`. -/
theorem card_add_image_le_of_shift {G : Type*} [AddCommGroup G] [DecidableEq G]
    (f : ℤ →+ G) (d : ℤ) (hd : 0 < d) (hfd : f d = 0)
    (T U : Finset ℤ) (hTU : T ⊆ U)
    (hshift : ∀ x ∈ T, x+d ∈ U) :
    T.card + (U.image f).card ≤ U.card := by
  have himage : U.image f ⊆ (U \ T).image f := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    let F := U.filter (fun z => f z = y)
    have hxF : x ∈ F := Finset.mem_filter.mpr ⟨hx, hxy⟩
    have hF : F.Nonempty := ⟨x, hxF⟩
    let m := F.max' hF
    have hmF : m ∈ F := F.max'_mem hF
    obtain ⟨hmU, hmf⟩ := Finset.mem_filter.mp hmF
    have hmT : m ∉ T := by
      intro hmT
      have hmdF : m+d ∈ F := by
        apply Finset.mem_filter.mpr
        exact ⟨hshift m hmT, by rw [map_add, hmf, hfd, add_zero]⟩
      have hle : m+d ≤ m := Finset.le_max' F _ hmdF
      omega
    exact Finset.mem_image.mpr ⟨m, Finset.mem_sdiff.mpr ⟨hmU, hmT⟩, hmf⟩
  have hc : (U.image f).card ≤ (U \ T).card :=
    (Finset.card_le_card himage).trans Finset.card_image_le
  have hdiff := Finset.card_sdiff_add_card_eq_card hTU
  omega

/-- Each quotient class appearing in the next ordinary sumset contributes a new
    integer point when the set contains both ends of a positive kernel shift. -/
theorem ordinarySums_growth_ge_image {G : Type*} [AddCommGroup G] [DecidableEq G]
    (B : Finset ℤ) (f : ℤ →+ G) (d : ℤ) (hd : 0 < d) (hfd : f d = 0)
    (hzero : 0 ∈ B) (hend : d ∈ B) (q : ℕ) :
    (ordinarySums B q).card + (ordinarySums (B.image f) (q+1)).card ≤
      (ordinarySums B (q+1)).card := by
  rw [ordinarySums_image]
  apply card_add_image_le_of_shift f d hd hfd
  · intro x hx
    exact Finset.mem_add.mpr ⟨0, hzero, x, hx, zero_add x⟩
  · intro x hx
    exact Finset.mem_add.mpr ⟨d, hend, x, hx, add_comm d x⟩

/-- Isolating a new fiber sharpens the ordinary shift bound by retaining all of
    its integer points instead of only one representative of each image class. -/
theorem card_add_image_add_fiber_le_of_shift {G : Type*} [AddCommGroup G] [DecidableEq G]
    (f : ℤ →+ G) (d : ℤ) (hd : 0 < d) (hfd : f d = 0)
    (T U V : Finset ℤ) (hTU : T ⊆ U) (hVU : V ⊆ U) (hTV : Disjoint T V)
    (hshift : ∀ x ∈ T, x+d ∈ U) (havoid : ∀ x ∈ T, x+d ∉ V) :
    T.card + (U.image f).card + V.card ≤ U.card + (V.image f).card := by
  have hTUV : T ⊆ U \ V := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hTU hx, fun hv => Finset.disjoint_left.mp hTV hx hv⟩
  have hg := card_add_image_le_of_shift f d hd hfd T (U \ V) hTUV
    (fun x hx => Finset.mem_sdiff.mpr ⟨hshift x hx, havoid x hx⟩)
  have himage : U.image f ⊆ (U \ V).image f ∪ V.image f := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    by_cases hxV : x ∈ V
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hxV, rfl⟩)
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxV⟩, rfl⟩)
  have hc := (Finset.card_le_card himage).trans (Finset.card_union_le _ _)
  have he := Finset.card_sdiff_add_card_eq_card hVU
  omega

end SumsetRanges
