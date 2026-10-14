import MainTheorems.PreorderGamma.CloneCounts
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Data.Sym.NatCard
import Mathlib.Data.Nat.Choose.Sum

namespace ResearchMain.PreorderGamma

open scoped BigOperators Classical

abbrev MarginVectors (T : Type*) [Fintype T] (t : ℕ) :=
  {s : T → ℕ // ∑ b, s b = t}

instance marginVectorsFinite (T : Type*) [Fintype T] (t : ℕ) :
    Finite (MarginVectors T t) :=
  Finite.of_equiv (Sym T t) (Sym.equivNatSumOfFintype T t)

noncomputable instance marginVectorsFintype (T : Type*) [Fintype T] (t : ℕ) :
    Fintype (MarginVectors T t) := Fintype.ofFinite _

noncomputable def marginFinsuppEquiv (T : Type*) [Fintype T] (t : ℕ) :
    (Finset.finsuppAntidiag (Finset.univ : Finset T) t) ≃ MarginVectors T t := by
  classical
  refine
    { toFun := fun f => ⟨f.val, (Finset.mem_finsuppAntidiag.mp f.property).1⟩
      invFun := fun s => ⟨Finsupp.equivFunOnFinite.symm s.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact Finset.mem_finsuppAntidiag.mpr ⟨s.property, Finset.subset_univ _⟩
  · intro f
    apply Subtype.ext
    exact Finsupp.equivFunOnFinite.symm_apply_apply f.val
  · intro s
    rfl

theorem powerSeries_coeff_product {T : Type*} [Fintype T]
    (f : T → PowerSeries ℚ) (t : ℕ) :
    PowerSeries.coeff t (∏ b, f b) =
      ∑ s : MarginVectors T t, ∏ b, PowerSeries.coeff (s.val b) (f b) := by
  classical
  rw [PowerSeries.coeff_prod]
  rw [← Finset.sum_coe_sort]
  apply Fintype.sum_equiv (marginFinsuppEquiv T t)
  intro s
  rfl

noncomputable def multichooseSeries (a : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun s => (Nat.multichoose s a : ℚ)

@[simp] theorem multichooseSeries_coeff (a s : ℕ) :
    PowerSeries.coeff s (multichooseSeries a) = (Nat.multichoose s a : ℚ) :=
  PowerSeries.coeff_mk _ _

theorem multichooseSeries_zero :
    multichooseSeries 0 = (PowerSeries.invOneSubPow ℚ 1).val := by
  ext s
  simp [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]

theorem multichooseSeries_succ (a : ℕ) :
    multichooseSeries (a + 1) =
      PowerSeries.X * (PowerSeries.invOneSubPow ℚ (a + 2)).val := by
  ext s
  rw [multichooseSeries_coeff, ← pow_one (PowerSeries.X : PowerSeries ℚ),
    PowerSeries.coeff_X_pow_mul', PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
  cases s with
  | zero => simp
  | succ s =>
    simp only [Nat.le_add_left, ite_eq_left, Nat.add_sub_cancel,
      PowerSeries.coeff_mk, Nat.multichoose_eq]
    congr 1
    congr 1
    omega

theorem multichooseSeries_eq (a : ℕ) :
    multichooseSeries a = (PowerSeries.X : PowerSeries ℚ) ^ (if 0 < a then 1 else 0) *
      (PowerSeries.invOneSubPow ℚ (a + 1)).val := by
  cases a with
  | zero => simp [multichooseSeries_zero]
  | succ a => simpa using multichooseSeries_succ a

theorem sum_multichooseSeries (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), multichooseSeries j) =
      (PowerSeries.invOneSubPow ℚ (N + 1)).val := by
  ext s
  simp only [map_sum, multichooseSeries_coeff,
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, PowerSeries.coeff_mk]
  rw [← Nat.cast_sum, Nat.sum_range_multichoose]
  exact_mod_cast (Nat.choose_symm_add (a := N) (b := s)).symm

theorem product_invOneSubPow {T : Type*} (A : Finset T) (d : T → ℕ) :
    (∏ b ∈ A, (PowerSeries.invOneSubPow ℚ (d b)).val) =
      (PowerSeries.invOneSubPow ℚ (∑ b ∈ A, d b)).val := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [PowerSeries.invOneSubPow_zero]
  | @insert b A hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb, ih,
      PowerSeries.invOneSubPow_add, Units.val_mul]

theorem product_multichooseSeries {T : Type*} [Fintype T] (a : T → ℕ) :
    (∏ b, multichooseSeries (a b)) =
      (PowerSeries.X : PowerSeries ℚ) ^ (demandSupport a).card *
        (PowerSeries.invOneSubPow ℚ ((∑ b, a b) + Fintype.card T)).val := by
  classical
  simp_rw [multichooseSeries_eq]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, product_invOneSubPow]
  congr 1
  · rw [demandSupport, Finset.card_filter]
  · simp [Finset.sum_add_distrib]

theorem multichoose_margin_sum {T : Type*} [Fintype T] (a : T → ℕ) (t : ℕ) :
    (∑ s : MarginVectors T t, ∏ b, (Nat.multichoose (s.val b) (a b) : ℚ)) =
      PowerSeries.coeff t (∏ b, multichooseSeries (a b)) := by
  rw [powerSeries_coeff_product]
  simp

end ResearchMain.PreorderGamma
