import Paving.MobiusCoefficientSum

namespace Paving
attribute [local instance] Classical.propDecidable
open Finset MatroidInverseZ Polynomial
variable {α : Type*} [Fintype α] {M : Matroid α}

theorem hyperplane_upper_Ico (H : Set α) (hH : IsHyperplane M H) :
    Ico (⟨H,hH.1⟩ : MatroidInverseZ.Flat M) ⊤ = {⟨H,hH.1⟩} := by
  ext F
  simp only [mem_Ico,mem_singleton]
  constructor
  · rintro ⟨hle,hlt⟩
    by_contra hne
    have h1 := (actualFlatRank_strictMono M) (lt_of_le_of_ne hle (Ne.symm hne))
    have h2 := (actualFlatRank_strictMono M) hlt
    rw [actualFlatRank_top] at h2
    have hh := hH.2
    change subsetRank M H < MatroidInverseZ.flatRank M F at h1
    omega
  · rintro rfl
    exact ⟨le_rfl, lt_of_le_of_ne le_top (fun he => hyperplane_ne_ground hH (congrArg Subtype.val he))⟩

theorem hyperplane_upper_mu_one (H : Set α) (hH : IsHyperplane M H) :
    IncidenceAlgebra.mu ℤ (⟨H,hH.1⟩ : MatroidInverseZ.Flat M) ⊤ = -1 := by
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne
    (fun he => hyperplane_ne_ground hH (congrArg Subtype.val he)), hyperplane_upper_Ico H hH,
    sum_singleton, IncidenceAlgebra.mu_self]

/-- The even central coefficient receives exactly the low-flat Möbius mass
and the uniform inverse-Q contributions from actual hyperplanes. -/
theorem IsPaving.flatSummand_center (hM : IsPaving M) (m : ℕ) (hm : 2≤m)
    (hr : rank M=2*m) (F : MatroidInverseZ.Flat M) :
    (flatSummand M F).coeff m =
      (if MatroidInverseZ.flatRank M F=m then (-1:ℤ)^m*IncidenceAlgebra.mu ℤ F ⊤ else 0) +
      (if IsHyperplane M F.1 then (uniformQ (α:=F.1) (2*m-2)).coeff (m-1) else 0) := by
  by_cases htop : F = ⊤
  · subst F
    have hnh : ¬IsHyperplane M (⊤ : MatroidInverseZ.Flat M).1 := by
      intro h
      exact hyperplane_ne_ground h rfl
    rw [actualFlatRank_top, hr, ite_eq_right (by omega : 2*m≠m), ite_eq_right hnh, add_zero]
    rw [flatSummand, actualFlatRank_top, Nat.sub_self, pow_zero, IncidenceAlgebra.mu_self,
      mul_one, map_one, one_mul]
    simp only [pow_zero, one_mul]
    exact inverseKL_high_coeff (MatroidInverseZ.flatRank M) (actualFlatRank_strictMono M).monotone
      ⊥ ⊤ bot_le (by
        intro he
        have h := congrArg (MatroidInverseZ.flatRank M) he
        rw [actualFlatRank_bot,actualFlatRank_top,hr] at h
        omega) m
      (by rw [actualFlatRank_bot,actualFlatRank_top,hr]; omega)
  · have hproper : F.1 ≠ M.E := fun he => htop (Subtype.ext he)
    rcases hM.proper_flat_cases F.2 hproper with hlo | hH
    · have hc : MatroidInverseZ.flatRank M F=F.1.ncard := congrArg ENat.toNat hlo.1.eRk_eq_encard
      have hnh : ¬IsHyperplane M F.1 := by
        intro hh
        have hh' := hh.2
        change subsetRank M F.1=F.1.ncard at hc
        omega
      rw [ite_eq_right hnh,add_zero,flatSummand,actual_independentFlat_inverseKL F.1 hlo.1 F.2,
        mul_one,coeff_C_mul,coeff_X_pow]
      by_cases he : MatroidInverseZ.flatRank M F=m
      · rw [ite_eq_left he,he,hr,show 2*m-m=m by omega,ite_eq_left rfl,mul_one]
      · rw [ite_eq_right he,ite_eq_right (by omega : ¬m=rank M-MatroidInverseZ.flatRank M F),mul_zero]
    · have hf : MatroidInverseZ.flatRank M F+1=2*m := by exact hH.2.trans hr
      have hmu := hyperplane_upper_mu_one F.1 hH
      change IncidenceAlgebra.mu ℤ F ⊤ = -1 at hmu
      rw [ite_eq_right (by omega : MatroidInverseZ.flatRank M F≠m),zero_add,ite_eq_left hH,
        flatSummand,hmu,show rank M-MatroidInverseZ.flatRank M F=1 by omega]
      simp only [pow_one,neg_mul_neg,mul_one,map_one,one_mul]
      have hx := coeff_X_mul (inverseKL (MatroidInverseZ.flatRank M) ⊥ F) (m-1)
      rw [show m-1+1=m by omega] at hx
      rw [hx,hyperplane_inverseKL hM (2*m-2) (by omega) F.1 hH]

theorem sum_hyperplane_flats (M : Matroid α) (w : Set α → ℤ) :
    (∑ F : MatroidInverseZ.Flat M, if IsHyperplane M F.1 then w F.1 else 0) =
      ∑ H ∈ hyperplanes M, w H := by
  rw [← sum_filter]
  apply sum_bij (fun F _ => F.1)
  · intro F hF
    exact (mem_hyperplanes M F.1).mpr (mem_filter.mp hF).2
  · intro F _ G _ he
    exact Subtype.ext he
  · intro H hH
    have hh := (mem_hyperplanes M H).mp hH
    exact ⟨⟨H,hh.1⟩, mem_filter.mpr ⟨mem_univ _,hh⟩,rfl⟩
  · intro F _
    rfl

theorem IsPaving.actual_inverseZ_center_split (hM : IsPaving M) (m : ℕ) (hm : 2≤m)
    (hr : rank M=2*m) :
    (matroidInverseZ M).coeff m =
      uniformEntry (2*m) M.E.ncard m - ∑ H ∈ hyperplanes M, uniformEntry (2*m) H.ncard m +
      ∑ H ∈ hyperplanes M, (uniformQ (α:=H) (2*m-2)).coeff (m-1) := by
  rw [actual_inverseZ_sum,finsetSum_coeff]
  simp_rw [hM.flatSummand_center m hm hr]
  rw [sum_add_distrib,sum_hyperplane_flats M (fun H => (uniformQ (α:=H) (2*m-2)).coeff (m-1))]
  congr 1
  rw [← sum_filter]
  have h := hM.signed_mobius_rank_sum (2*m-2) (by omega) m (by omega)
  rw [hr,show 2*m-m=m by omega] at h
  exact h

end Paving
