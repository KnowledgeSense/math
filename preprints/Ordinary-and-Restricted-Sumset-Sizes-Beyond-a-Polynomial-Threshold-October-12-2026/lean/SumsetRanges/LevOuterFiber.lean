import SumsetRanges.LevCosets

open Finset
open scoped Pointwise Classical
namespace SumsetRanges

/-- A quotient fiber absent from the preceding sumset inherits the sum of the
    lower bounds of its nonzero input fibers. -/
theorem ordinarySums_outer_fiber_lower {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset ℤ) (f : ℤ →+ G) (e : ℤ) (hfe : f e = 0)
    (hf : Set.InjOn f (A.erase e)) (H : AddSubgroup G) [DecidableEq (G ⧸ H)]
    (K : Finset G)
    (hK : (K : Set G) = H) (n : ℕ) (q : G ⧸ H)
    (hq : q ∈ (ordinarySums A (n+1)).image ((QuotientAddGroup.mk' H).comp f))
    (hnew : q ∉ (ordinarySums A n).image ((QuotientAddGroup.mk' H).comp f)) :
    (n+1)*(A.image f).card + (n+1)*K.card + 1 ≤
      ((ordinarySums A (n+1)).filter
        (fun x => ((QuotientAddGroup.mk' H).comp f) x = q)).card +
      (n+1)*(A.image f+K).card + (n+1) := by
  let π := QuotientAddGroup.mk' H
  let g := π.comp f
  let S := A.image f
  obtain ⟨x, hx, hxq⟩ := Finset.mem_image.mp hq
  obtain ⟨v, hv, hvx⟩ := (mem_ordinarySums A (n+1) x).mp hx
  have hqsum : (∑ i, g (v i)) = q := by
    rw [← map_sum, hvx]
    exact hxq
  have hnonzero : ∀ i, g (v i) ≠ 0 :=
    sum_representative_nonzero_of_new_fiber A g n v hv (by rw [hqsum]; exact hnew)
  have hge : g e = 0 := by change π (f e) = 0; rw [hfe, map_zero]
  have hpoint (i : Fin (n+1)) :
      S.card + K.card ≤ (S+K).card + (A.filter (fun a => g a = g (v i))).card := by
    have hinj : Set.InjOn f (A.filter (fun a => g a = g (v i))) := by
      apply hf.mono
      intro a ha
      obtain ⟨haA, hag⟩ := Finset.mem_filter.mp ha
      apply Finset.mem_erase.mpr
      refine ⟨?_, haA⟩
      intro hae
      apply hnonzero i
      rw [← hag, hae, hge]
    have hc : (A.filter (fun a => g a = g (v i))).card =
        (S.filter (fun a => π a = π (f (v i)))).card := by
      rw [← image_filter_comp_eq A f π]
      exact (Finset.card_image_iff.mpr hinj).symm
    rw [hc]
    exact card_fiber_lower H K S hK (Finset.mem_image.mpr ⟨v i, hv i, rfl⟩)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at hsum
  have hc := integer_sum_fiber_card_lower A g (n+1) v hv
  rw [hqsum] at hc
  change (n+1)*S.card + (n+1)*K.card + 1 ≤
    ((ordinarySums A (n+1)).filter (fun x => g x = q)).card +
      (n+1)*(S+K).card + (n+1)
  omega

end SumsetRanges
