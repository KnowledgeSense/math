import Paving.LowFlatMobiusSum

namespace Paving
attribute [local instance] Classical.propDecidable
open Finset MatroidInverseZ
variable {α : Type*} [Fintype α] {M : Matroid α}

/-- The non-Boolean proper flats in the upper interval are precisely actual hyperplanes. -/
theorem IsPaving.hyperplane_mobius_sum (hM : IsPaving M) (d : ℕ) (hr : rank M=d+2)
    (F : MatroidInverseZ.Flat M) (hF : F.1.ncard≤d) :
    (∑ G ∈ (Ico F ⊤).filter (fun G => ¬G.1.ncard≤d), IncidenceAlgebra.mu ℤ F G) =
      ∑ H ∈ (hyperplanes M).filter (fun H => F.1 ⊆ H),
        (-1 : ℤ)^(d-F.1.ncard+1) * (H.ncard-F.1.ncard-1).choose (d-F.1.ncard) := by
  apply sum_bij (fun G _ => G.1)
  · intro G hG
    obtain ⟨hG,hcard⟩ := mem_filter.mp hG
    have hne : G.1 ≠ M.E := fun he => (mem_Ico.mp hG).2.ne (Subtype.ext he)
    have hh := hM.proper_flat_cases G.2 hne
    have hH : IsHyperplane M G.1 := by
      rcases hh with hh | hh
      · exfalso
        omega
      · exact hh
    exact mem_filter.mpr ⟨(mem_hyperplanes M G.1).mpr hH, (mem_Ico.mp hG).1⟩
  · intro G _ H _ he
    exact Subtype.ext he
  · intro H hH
    obtain ⟨hH,hFH⟩ := mem_filter.mp hH
    have hh := (mem_hyperplanes M H).mp hH
    have hc := hyperplane_card_lower hh
    refine ⟨⟨H,hh.1⟩, mem_filter.mpr ⟨mem_Ico.mpr ⟨hFH, ?_⟩, by change ¬H.ncard≤d; omega⟩,rfl⟩
    exact lt_of_le_of_ne le_top (fun he => hyperplane_ne_ground hh (congrArg Subtype.val he))
  · intro G hG
    obtain ⟨hG,hcard⟩ := mem_filter.mp hG
    have hne : G.1 ≠ M.E := fun he => (mem_Ico.mp hG).2.ne (Subtype.ext he)
    have hh := hM.proper_flat_cases G.2 hne
    have hH : IsHyperplane M G.1 := by
      rcases hh with hh | hh
      · exfalso
        omega
      · exact hh
    exact hyperplane_upper_mu hM d hr G.1 hH F (mem_Ico.mp hG).1
      (fun he => by rw [← he] at hcard; omega)

/-- An exact Möbius recurrence using the actual low flats and actual hyperplanes. -/
theorem IsPaving.upper_mu_recurrence (hM : IsPaving M) (d : ℕ) (hr : rank M=d+2)
    (F : MatroidInverseZ.Flat M) (hF : F.1.ncard≤d) :
    IncidenceAlgebra.mu ℤ F ⊤ =
      (-1 : ℤ)^(d+2-F.1.ncard) *
        ((∑ H ∈ (hyperplanes M).filter (fun H => F.1 ⊆ H),
          ((H.ncard-F.1.ncard-1).choose (d-F.1.ncard):ℤ)) -
        ((M.E.ncard-F.1.ncard-1).choose (d-F.1.ncard):ℤ)) := by
  have hne : F ≠ ⊤ := by
    intro he
    have hg := rank_le_ground_card M
    have hc : F.1.ncard=M.E.ncard := congrArg (fun G : MatroidInverseZ.Flat M => G.1.ncard) he
    omega
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hne]
  rw [← sum_filter_add_sum_filter_not (Ico F ⊤) (fun G => G.1.ncard≤d)]
  rw [hM.low_flat_mobius_sum_closed d hr F hF, hM.hyperplane_mobius_sum d hr F hF,
    ← mul_sum, show d+2-F.1.ncard=(d-F.1.ncard)+2 by omega]
  simp only [pow_succ]
  ring

end Paving
