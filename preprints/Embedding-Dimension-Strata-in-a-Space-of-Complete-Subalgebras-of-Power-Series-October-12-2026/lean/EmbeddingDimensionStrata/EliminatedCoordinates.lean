import EmbeddingDimensionStrata.WeightControl

/-! # The five solved normal-form coordinates -/
set_option maxRecDepth 4096
noncomputable section
namespace EmbeddingDimensionStrata

/-- z37, z38, w49, z39, z49, in the triangular elimination order. -/
def eliminatedCoordinate (i : Fin 5) : NormalCoordinate :=
  match i.val with
  | 0 => ⟨(2,37),by decide⟩
  | 1 => ⟨(2,38),by decide⟩
  | 2 => ⟨(3,49),by decide⟩
  | 3 => ⟨(2,39),by decide⟩
  | _ => ⟨(2,49),by decide⟩

theorem eliminatedCoordinate_injective : Function.Injective eliminatedCoordinate := by decide

theorem eliminatedCoordinate_weight (i : Fin 5) :
    coordinateWeight (eliminatedCoordinate i) = equationWeight i := by
  have h : ∀ i : Fin 5, coordinateWeight (eliminatedCoordinate i) = equationWeight i := by decide
  exact h i

def eliminatedCoordinates : Finset NormalCoordinate := Finset.univ.image eliminatedCoordinate

abbrev FreeCoordinate := {j : NormalCoordinate // j ∉ eliminatedCoordinates}

theorem freeCoordinate_card : Fintype.card FreeCoordinate = 57 := by decide

/-- At a coordinate unit point, the actual normal form differs from its leading
monomial by just the indicated single monomial. -/
theorem normalSeries_unitPoint (j : NormalCoordinate) (i : Fin 5) :
    normalSeries (coordinateUnitPoint j) i =
      (PowerSeries.X : PowerSeries ℤ) ^ generatorValue i +
        if i = j.val.1 then PowerSeries.X ^ j.val.2.val else 0 := by
  classical
  by_cases hij : i = j.val.1
  · rw [ite_eq_left hij]
    subst i
    ext n
    rw [map_add, PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow, coeff_normalSeries]
    by_cases hn : n = generatorValue j.val.1
    · rw [ite_eq_left hn, ite_eq_left hn, ite_eq_right (by
        have hh := j.property.1
        omega : n ≠ j.val.2.val), add_zero]
    · rw [ite_eq_right hn, ite_eq_right hn, zero_add]
      by_cases ht : n < 60 ∧ generatorValue j.val.1 < n ∧ n ∉ valuesBelowConductor
      · rw [dite_eq_left ht]
        have heq : (⟨(j.val.1,⟨n,ht.1⟩),ht.2⟩ : NormalCoordinate) = j ↔ n = j.val.2.val := by
          constructor
          · intro h
            exact congrArg (fun k : NormalCoordinate => k.val.2.val) h
          · intro h
            apply Subtype.ext
            apply Prod.ext
            · rfl
            · exact Fin.ext h
        simp only [coordinateUnitPoint, heq]
      · rw [dite_eq_right ht, ite_eq_right (by
          intro hh
          subst n
          exact ht ⟨j.val.2.isLt,j.property⟩)]
  · rw [ite_eq_right hij, add_zero]
    ext n
    rw [coeff_normalSeries, PowerSeries.coeff_X_pow]
    by_cases hn : n = generatorValue i
    · rw [ite_eq_left hn, ite_eq_left hn]
    · rw [ite_eq_right hn, ite_eq_right hn]
      split_ifs with ht
      · apply ite_eq_right
        intro hh
        exact hij (congrArg (fun k : NormalCoordinate => k.val.1) hh)
      · rfl

/-- A series supported entirely at gaps is unchanged by reduction. -/
theorem reduceSeries_eq_self_of_gap_support {A : Type*} [CommRing A]
    (p : NormalCoordinate → A) (f : PowerSeries A)
    (hf : ∀ n ∈ valuesBelowConductor, PowerSeries.coeff n f = 0) (N : ℕ) :
    reduceSeries p N f = f := by
  induction N with
  | zero => rfl
  | succ n ih =>
    rw [reduceSeries_succ, ih]
    split_ifs with hn
    · rw [hf n hn, zero_smul, sub_zero]
    · rfl

/-- At a Z-coordinate unit point the first binomial is exactly a negative
gap monomial. -/
theorem relationF_unit_Z (j : NormalCoordinate) (hj : j.val.1 = 2) :
    relationF (coordinateUnitPoint j) = -(PowerSeries.X : PowerSeries ℤ) ^ (10+j.val.2.val) := by
  simp only [relationF, normalSeries_unitPoint, hj]
  norm_num [generatorValue]
  rw [pow_add]
  ring

/-- At a W-coordinate unit point the first binomial is zero. -/
theorem relationF_unit_W (j : NormalCoordinate) (hj : j.val.1 = 3) :
    relationF (coordinateUnitPoint j) = 0 := by
  simp only [relationF, normalSeries_unitPoint, hj]
  norm_num [generatorValue]
  ring

theorem relationG_unit_W (j : NormalCoordinate) (hj : j.val.1 = 3) :
    relationG (coordinateUnitPoint j) = -(PowerSeries.X : PowerSeries ℤ) ^ (10+j.val.2.val) := by
  simp only [relationG, normalSeries_unitPoint, hj]
  norm_num [generatorValue]
  rw [pow_add]
  ring

theorem reduceSeries_neg_gap_monomial {A : Type*} [CommRing A]
    (p : NormalCoordinate → A) (n : ℕ) (hn : n ∉ valuesBelowConductor) (N : ℕ) :
    reduceSeries p N (-(PowerSeries.X : PowerSeries A)^n) = -PowerSeries.X^n := by
  apply reduceSeries_eq_self_of_gap_support
  intro k hk
  rw [map_neg, PowerSeries.coeff_X_pow, ite_eq_right (by
    intro heq
    exact hn (heq ▸ hk)), neg_zero]

/-- The exact coefficient of each solved coordinate in its defining equation
is -1, checked through the actual normal-form specialization. -/
theorem definingPolynomial_linear_coefficient (i : Fin 5) :
    (definingPolynomial i).coeff (Finsupp.single (eliminatedCoordinate i) 1) = -1 := by
  have hweight : (definingPolynomial i).IsWeightedHomogeneous coordinateWeight
      (coordinateWeight (eliminatedCoordinate i)) := by
    rw [eliminatedCoordinate_weight]
    exact definingPolynomial_weighted i
  rw [← weighted_linear_coefficient (eliminatedCoordinate i) hweight]
  have hEval : MvPolynomial.eval (coordinateUnitPoint (eliminatedCoordinate i))
      (definingPolynomial i) = definingEquation (coordinateUnitPoint (eliminatedCoordinate i)) i :=
    eval_definingPolynomial _ i
  rw [hEval]
  fin_cases i
  · change PowerSeries.coeff 47 (reduceSeries _ 60 (relationF _)) = -1
    rw [relationF_unit_Z _ (by rfl)]
    change PowerSeries.coeff 47 (reduceSeries _ 60 (-(PowerSeries.X : PowerSeries ℤ)^47)) = -1
    rw [reduceSeries_neg_gap_monomial _ 47 (by decide), map_neg, PowerSeries.coeff_X_pow]
    norm_num
  · change PowerSeries.coeff 48 (reduceSeries _ 60 (relationF _)) = -1
    rw [relationF_unit_Z _ (by rfl)]
    change PowerSeries.coeff 48 (reduceSeries _ 60 (-(PowerSeries.X : PowerSeries ℤ)^48)) = -1
    rw [reduceSeries_neg_gap_monomial _ 48 (by decide), map_neg, PowerSeries.coeff_X_pow]
    norm_num
  · change PowerSeries.coeff 59 (reduceSeries _ 60 (relationG _)) = -1
    rw [relationG_unit_W _ (by rfl)]
    change PowerSeries.coeff 59 (reduceSeries _ 60 (-(PowerSeries.X : PowerSeries ℤ)^59)) = -1
    rw [reduceSeries_neg_gap_monomial _ 59 (by decide), map_neg, PowerSeries.coeff_X_pow]
    norm_num
  · change PowerSeries.coeff 49 (reduceSeries _ 60 (relationF _)) = -1
    rw [relationF_unit_Z _ (by rfl)]
    change PowerSeries.coeff 49 (reduceSeries _ 60 (-(PowerSeries.X : PowerSeries ℤ)^49)) = -1
    rw [reduceSeries_neg_gap_monomial _ 49 (by decide), map_neg, PowerSeries.coeff_X_pow]
    norm_num
  · change PowerSeries.coeff 59 (reduceSeries _ 60 (relationF _)) = -1
    rw [relationF_unit_Z _ (by rfl)]
    change PowerSeries.coeff 59 (reduceSeries _ 60 (-(PowerSeries.X : PowerSeries ℤ)^59)) = -1
    rw [reduceSeries_neg_gap_monomial _ 59 (by decide), map_neg, PowerSeries.coeff_X_pow]
    norm_num

end EmbeddingDimensionStrata
