import Paving.RankOneInterval
import Paving.CentralDecomposition
import Paving.PointedPacking
import Paving.Support

namespace Paving
attribute [local instance] Classical.propDecidable
open MatroidInverseZ Polynomial Finset
variable {α : Type*} [Fintype α] {M : Matroid α}

theorem rank_one_polynomial (M : Matroid α) (hr : rank M=1) :
    matroidInverseZ M=1+X := by
  change inverseZ (MatroidInverseZ.flatRank M) ⊥ ⊤=1+X
  have hd : MatroidInverseZ.flatRank M ⊤=MatroidInverseZ.flatRank M ⊥+1 := by simp [hr]
  rw [inverseZ_rank_one_split _ (actualFlatRank_strictMono M) _ _ bot_le hd,
    inverseKL_rank_one _ (actualFlatRank_strictMono M) _ _ bot_le hd]

theorem rank_two_flat_cases (M : Matroid α) (hr : rank M=2) (F : MatroidInverseZ.Flat M) :
    F=⊥ ∨ IsHyperplane M F.val ∨ F=⊤ := by
  by_cases hb : F=⊥
  · exact Or.inl hb
  by_cases ht : F=⊤
  · exact Or.inr (Or.inr ht)
  have h1 := actualFlatRank_strictMono M (bot_lt_iff_ne_bot.mpr hb)
  have h2 := actualFlatRank_strictMono M (lt_top_iff_ne_top.mpr ht)
  rw [actualFlatRank_bot] at h1
  rw [actualFlatRank_top,hr] at h2
  exact Or.inr (Or.inl ⟨F.property,by change MatroidInverseZ.flatRank M F+1=rank M; omega⟩)

theorem rank_two_hyperplane_bottom_mu (M : Matroid α) (hr : rank M=2)
    (H : Set α) (hH : IsHyperplane M H) :
    IncidenceAlgebra.mu ℤ (⊥ : MatroidInverseZ.Flat M) ⟨H,hH.1⟩ = -1 := by
  have hd : MatroidInverseZ.flatRank M ⟨H,hH.1⟩=MatroidInverseZ.flatRank M ⊥+1 := by
    rw [actualFlatRank_bot]
    have hh := hH.2
    change subsetRank M H=0+1
    omega
  have hn : (⊥ : MatroidInverseZ.Flat M)≠⟨H,hH.1⟩ := by
    intro he
    rw [← he] at hd
    omega
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hn,
    rank_one_Ico _ (actualFlatRank_strictMono M) _ _ bot_le hd,
    sum_singleton,IncidenceAlgebra.mu_self]

theorem rank_two_bottom_top_mu (M : Matroid α) (hr : rank M=2) :
    IncidenceAlgebra.mu ℤ (⊥ : MatroidInverseZ.Flat M) ⊤=((hyperplanes M).card:ℤ)-1 := by
  have hn : (⊥ : MatroidInverseZ.Flat M)≠⊤ := by
    intro he
    have hh := congrArg (MatroidInverseZ.flatRank M) he
    simp [hr] at hh
  let S := univ.filter (fun F : MatroidInverseZ.Flat M => IsHyperplane M F.val)
  have hnb : (⊥ : MatroidInverseZ.Flat M)∉S := by
    intro hb
    have hh := (mem_filter.mp hb).2.2
    change MatroidInverseZ.flatRank M ⊥+1=rank M at hh
    simp [hr] at hh
  have he : Ico (⊥ : MatroidInverseZ.Flat M) ⊤=insert ⊥ S := by
    ext F
    simp only [mem_Ico,bot_le,true_and,mem_insert,S,mem_filter,mem_univ,true_and]
    constructor
    · intro hF
      rcases rank_two_flat_cases M hr F with h|h|h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hF.ne h)
    · rintro (rfl|hF)
      · exact lt_of_le_of_ne bot_le hn
      · exact lt_of_le_of_ne le_top (fun hh => hyperplane_ne_ground hF (congrArg Subtype.val hh))
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hn,he,sum_insert hnb,IncidenceAlgebra.mu_self]
  have hs : (∑F∈S,IncidenceAlgebra.mu ℤ (⊥ : MatroidInverseZ.Flat M) F) = -(hyperplanes M).card := by
    have hx (F : MatroidInverseZ.Flat M) (hF : F∈S) :
        IncidenceAlgebra.mu ℤ (⊥ : MatroidInverseZ.Flat M) F=-1 :=
      rank_two_hyperplane_bottom_mu M hr F.val (mem_filter.mp hF).2
    rw [sum_congr rfl hx]
    have hc : S.card=(hyperplanes M).card := by
      have hh := sum_hyperplane_flats M (fun _ => 1)
      simpa [S,← sum_filter] using hh
    simp [hc]
  rw [hs]
  ring

theorem IsPaving.rank_two_hyperplanes_card (hM : IsPaving M) (hr : rank M=2) :
    2 ≤ (hyperplanes M).card := by
  have hn := rank_le_ground_card M
  have hs := hM.pointed_hyperplane_packing (by omega) ∅ (Set.empty_subset _) (by simp)
  simp only [hr,Set.ncard_empty,Nat.sub_zero,Set.empty_subset,ite_true,Nat.reduceSub,Nat.choose_one_right] at hs
  by_contra hc
  have hc1 : (hyperplanes M).card≤1 := by omega
  by_cases he : hyperplanes M=∅
  · rw [he,sum_empty] at hs
    omega
  · obtain ⟨H,hH⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hsingle : hyperplanes M={H} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      exact ⟨hH,fun K hK => Finset.card_le_one.mp hc1 K hK H hH⟩
    rw [hsingle,sum_singleton] at hs
    have hlt := hyperplane_card_lt ((mem_hyperplanes M H).mp hH)
    omega

theorem rank_two_summand_coeff (M : Matroid α) (hr : rank M=2)
    (F : MatroidInverseZ.Flat M) (j : ℕ) (hj : 1 ≤ j) :
    (flatSummand M F).coeff j =
      if F=⊥ then (if j=2 then ((hyperplanes M).card:ℤ)-1 else 0)
      else if IsHyperplane M F.val then (if j=1 then 1 else 0) else 0 := by
  by_cases hb : F=⊥
  · subst F
    rw [flatSummand,actualFlatRank_bot,hr,Nat.sub_zero,rank_two_bottom_top_mu M hr,inverseKL_self]
    simp only [neg_one_sq,one_mul,mul_one,coeff_C_mul,coeff_X_pow,ite_true]
    split_ifs <;> simp_all
  · rw [ite_eq_right hb]
    rcases rank_two_flat_cases M hr F with h|h|h
    · exact False.elim (hb h)
    · have hf : MatroidInverseZ.flatRank M F=1 := by have hh := h.2; change subsetRank M F.val=1; omega
      have hq := inverseKL_rank_one (MatroidInverseZ.flatRank M) (actualFlatRank_strictMono M)
        ⊥ F bot_le (by simp [hf])
      have hmu := hyperplane_upper_mu_one F.val h
      change IncidenceAlgebra.mu ℤ F ⊤=-1 at hmu
      rw [ite_eq_left h,flatSummand,hf,hr,hmu,hq]
      simp [coeff_X,eq_comm]
    · subst F
      have hnH : ¬IsHyperplane M (⊤ : MatroidInverseZ.Flat M).val := by
        intro hh; exact hyperplane_ne_ground hh rfl
      rw [ite_eq_right hnH,flatSummand,actualFlatRank_top,Nat.sub_self]
      simp only [pow_zero,IncidenceAlgebra.mu_self,mul_one,map_one,one_mul]
      apply inverseKL_high_coeff _ (actualFlatRank_strictMono M).monotone _ _ bot_le
      · exact Ne.symm hb
      · rw [actualFlatRank_bot,actualFlatRank_top,hr]; omega

theorem rank_two_coeff_one (M : Matroid α) (hr : rank M=2) :
    (matroidInverseZ M).coeff 1=(hyperplanes M).card := by
  rw [actual_inverseZ_sum,finsetSum_coeff]
  have he (F : MatroidInverseZ.Flat M) : (flatSummand M F).coeff 1=
      if IsHyperplane M F.val then 1 else 0 := by
    rw [rank_two_summand_coeff M hr F 1 le_rfl]
    by_cases hb : F=⊥
    · subst F
      have hn : ¬IsHyperplane M (⊥ : MatroidInverseZ.Flat M).val := by
        intro hh
        have h := hh.2
        change MatroidInverseZ.flatRank M ⊥+1=rank M at h
        simp [hr] at h
      simp [hn]
    · simp [hb]
  simp_rw [he]
  rw [sum_hyperplane_flats M (fun _ => (1:ℤ))]
  simp

theorem rank_two_coeff_two (M : Matroid α) (hr : rank M=2) :
    (matroidInverseZ M).coeff 2=((hyperplanes M).card:ℤ)-1 := by
  rw [actual_inverseZ_sum,finsetSum_coeff]
  simp_rw [rank_two_summand_coeff M hr _ 2 (by omega)]
  simp

theorem rank_two_coeff_zero (M : Matroid α) (hr : rank M=2) :
    (matroidInverseZ M).coeff 0=((hyperplanes M).card:ℤ)-1 := by
  rw [actual_inverseZ_coeff_symm M 0 (by omega),hr,Nat.sub_zero,rank_two_coeff_two M hr]

theorem rank_two_polynomial (M : Matroid α) (hr : rank M=2) :
    matroidInverseZ M=C (((hyperplanes M).card:ℤ)-1)+C ((hyperplanes M).card:ℤ)*X+
      C (((hyperplanes M).card:ℤ)-1)*X^2 := by
  ext i
  by_cases hi : i≤2
  · interval_cases i
    · simp only [rank_two_coeff_zero M hr,coeff_add,coeff_C_mul,coeff_C,coeff_X,coeff_X_pow]
      norm_num
    · simp only [rank_two_coeff_one M hr,coeff_add,coeff_C_mul,coeff_C,coeff_X,coeff_X_pow]
      norm_num
    · simp only [rank_two_coeff_two M hr,coeff_add,coeff_C_mul,coeff_C,coeff_X,coeff_X_pow]
      norm_num
  · have hz := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (actual_inverseZ_degree_le M) (by omega : rank M < i))
    rw [hz]
    simp only [coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C,ite_eq_right (show i≠0 by omega),ite_eq_right (show 1≠i by omega),ite_eq_right (show i≠2 by omega),mul_zero,add_zero]

theorem low_rank_positive (hM : IsPaving M) (hr : 1 ≤ rank M) (hr2 : rank M≤2)
    (i : ℕ) (hi : i≤rank M) : 0 < (matroidInverseZ M).coeff i := by
  have cases : rank M=1 ∨ rank M=2 := by omega
  rcases cases with h|h
  · rw [rank_one_polynomial M h]
    have : i≤1 := by omega
    interval_cases i <;> simp [coeff_one]
  · have hc := hM.rank_two_hyperplanes_card h
    have hcZ : (2:ℤ) ≤ (hyperplanes M).card := by exact_mod_cast hc
    have : i≤2 := by omega
    interval_cases i
    · rw [rank_two_coeff_zero M h]; omega
    · rw [rank_two_coeff_one M h]; omega
    · rw [rank_two_coeff_two M h]; omega

theorem low_rank_strict (hM : IsPaving M) (hr : 1 ≤ rank M) (hr2 : rank M≤2)
    (i : ℕ) (hi : 1 ≤ i) (hir : i < rank M) :
    (matroidInverseZ M).coeff (i-1)*(matroidInverseZ M).coeff (i+1)<(matroidInverseZ M).coeff i^2 := by
  have h : rank M=2 := by omega
  have he : i=1 := by omega
  subst i
  rw [show 1-1=0 from rfl,show 1+1=2 from rfl,rank_two_coeff_zero M h,
    rank_two_coeff_two M h,rank_two_coeff_one M h]
  have hc := hM.rank_two_hyperplanes_card h
  have hcZ : (2:ℤ) ≤ (hyperplanes M).card := by exact_mod_cast hc
  nlinarith

end Paving
