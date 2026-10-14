import HonestEmbeddingDimension.CoordinateChanges
import Mathlib.Data.ENat.SuccOrder

namespace HonestEmbeddingDimension

/-- Substitution of zero-constant coordinates preserves the outer constant coefficient. -/
theorem constantCoeff_formal_subst {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (hf0 : ∀ i, (f i).constantCoeff=0) (p : MvPowerSeries (Fin d) ℂ) :
    (MvPowerSeries.subst f p).constantCoeff=p.constantCoeff := by
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero hf0
  have hz : (p-MvPowerSeries.C p.constantCoeff).constantCoeff=0 := by simp
  have h := MvPowerSeries.constantCoeff_subst_eq_zero hs hf0 hz
  apply sub_eq_zero.mp
  simpa [MvPowerSeries.subst_sub hs, MvPowerSeries.subst_C] using h

/-- A positive minimal value occurs as the order of an actual coordinate. -/
theorem exists_coordinate_of_minimal_value {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (hf0 : ∀ i, (f i).constantCoeff=0) (m : ℕ) (hm : 0 < m)
    (hmem : m ∈ formalValues f)
    (hmin : ∀ n ∈ formalValues f, 0 < n → m ≤ n) :
    ∃ i, (f i).order=m := by
  classical
  have hcoords : ∀ i, (m : ℕ∞) ≤ (f i).order := by
    intro i
    by_cases hz : f i=0
    · simp [hz]
    · have he := PowerSeries.coe_toNat_order hz
      have hn : 0 < (f i).order.toNat := by
        have hp := PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (hf0 i)
        rw [← he] at hp
        exact_mod_cast hp
      have hv : (f i).order.toNat ∈ formalValues f := by
        rw [formalValues_eq_polynomialValues f hf0]
        exact ⟨MvPolynomial.X i, by simpa using he.symm⟩
      rw [← he]
      exact_mod_cast hmin _ hv hn
  by_contra hn
  have hne : ∀ i, (f i).order ≠ (m : ℕ∞) := by simpa using hn
  have hl : ((m+1 : ℕ) : ℕ∞) ≤ ⨅ i, (f i).order := by
    apply le_iInf
    intro i
    rw [Nat.cast_add, Nat.cast_one, ENat.natCast_add_one_le_iff]
    exact lt_of_le_of_ne (hcoords i) (hne i).symm
  obtain ⟨p,hp⟩ := hmem
  have hp0 : p.constantCoeff=0 := by
    rw [← constantCoeff_formal_subst f hf0 p]
    change PowerSeries.constantCoeff (MvPowerSeries.subst f p)=0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    exact PowerSeries.coeff_of_lt_order 0 (by rw [hp]; exact_mod_cast hm)
  have hp1 := MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hp0
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero hf0
  have hb := MvPowerSeries.le_order_subst hs p
  simp only [← PowerSeries.order_eq_order] at hb
  have hmul : (⨅ i, (f i).order) ≤ (⨅ i, (f i).order)*p.order :=
    le_mul_of_one_le_right' hp1
  have hh := hl.trans (hmul.trans hb)
  change ((m+1 : ℕ) : ℕ∞) ≤ PowerSeries.order (MvPowerSeries.subst f p) at hh
  rw [hp] at hh
  have hbad : m+1 ≤ m := by exact_mod_cast hh
  omega

/-- Normalize the minimum coordinate, allowing an arbitrary original leading coefficient. -/
theorem normalize_minimum_coordinate {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (hf0 : ∀ i, (f i).constantCoeff=0) (m : ℕ) (hm : 0 < m)
    (hmem : m ∈ formalValues f)
    (hmin : ∀ n ∈ formalValues f, 0 < n → m ≤ n) :
    ∃ (i : Fin d) (g : Fin d → PowerSeries ℂ), g i=PowerSeries.X^m ∧
      (∀ j, (g j).constantCoeff=0) ∧ formalValues g=formalValues f := by
  classical
  obtain ⟨i,hi⟩ := exists_coordinate_of_minimal_value f hf0 m hm hmem hmin
  let c := PowerSeries.coeff m (f i)
  have hc : c ≠ 0 := (PowerSeries.order_eq_nat.mp hi).1
  let g := Function.update f i (c⁻¹ • f i)
  have hg0 : ∀ j, (g j).constantCoeff=0 := by
    intro j
    by_cases hj : j=i
    · subst j; simp [g, hf0]
    · simp [g, Function.update_of_ne hj, hf0]
  have hglead : PowerSeries.coeff m (g i)=1 := by
    simp [g, c, hc]
  have hgi : (g i).order=m := by
    apply PowerSeries.order_eq_nat.mpr
    refine ⟨by rw [hglead]; exact one_ne_zero, ?_⟩
    intro n hn
    have hz := (PowerSeries.order_eq_nat.mp hi).2 n hn
    simp [g, hz]
  have hvalues : formalValues g=formalValues f := by
    rw [formalValues_eq_polynomialValues _ hg0, formalValues_eq_polynomialValues _ hf0]
    exact polynomialValues_eq_of_coordinateAlgebra_eq g f
      (coordinateAlgebra_update_scale f i c⁻¹ (inv_ne_zero hc))
  obtain ⟨k,hki,hk0,hkv,_⟩ := normalize_formal_coordinate g hg0 i m hm hgi hglead
  exact ⟨i,k,hki,hk0,hkv.trans hvalues⟩

end HonestEmbeddingDimension
