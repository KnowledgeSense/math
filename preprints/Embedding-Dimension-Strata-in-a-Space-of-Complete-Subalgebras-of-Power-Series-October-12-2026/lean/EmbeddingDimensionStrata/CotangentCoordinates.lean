import EmbeddingDimensionStrata.AffineParameters

/-! # The three actual reduced relation coefficients A, B, C -/
set_option maxRecDepth 4096
noncomputable section
namespace EmbeddingDimensionStrata

section Ring
variable {A : Type*} [CommRing A]

/-- The linear relation coefficients in the order A, B, C. -/
def relationCoordinate (p : NormalCoordinate → A) (i : Fin 3) : A :=
  match i.val with
  | 0 => PowerSeries.coeff 46 (reduceSeries p 46 (relationF p))
  | 1 => PowerSeries.coeff 58 (reduceSeries p 58 (relationG p))
  | _ => PowerSeries.coeff 58 (reduceSeries p 58 (relationF p))

def relationCoordinatePolynomial (i : Fin 3) : CoordinatePolynomial := relationCoordinate universalPoint i

/-- The three free normal-form coefficients replaced by A, B, C. -/
def coordinatePivot (i : Fin 3) : NormalCoordinate :=
  match i.val with
  | 0 => ⟨(2,36),by decide⟩
  | 1 => ⟨(3,48),by decide⟩
  | _ => ⟨(2,48),by decide⟩

theorem relationCoordinate_weighted (i : Fin 3) :
    (relationCoordinatePolynomial i).IsWeightedHomogeneous coordinateWeight
      (coordinateWeight (coordinatePivot i)) := by
  fin_cases i
  · exact reduceSeries_weighted _ 44 relationF_weighted 46 46
  · exact reduceSeries_weighted _ 56 relationG_weighted 58 58
  · exact reduceSeries_weighted _ 44 relationF_weighted 58 58

theorem eval_relationCoordinatePolynomial (p : NormalCoordinate → A) (i : Fin 3) :
    MvPolynomial.eval₂ (Int.castRingHom A) p (relationCoordinatePolynomial i) = relationCoordinate p i := by
  let φ := MvPolynomial.eval₂Hom (Int.castRingHom A) p
  have hp : (fun j => φ (universalPoint j)) = p := by
    funext j
    exact MvPolynomial.eval₂_X _ _ j
  have hF (N : ℕ) := map_reduceSeries φ universalPoint (relationF universalPoint) N
  have hG (N : ℕ) := map_reduceSeries φ universalPoint (relationG universalPoint) N
  simp only [map_relationF, hp] at hF
  simp only [map_relationG, hp] at hG
  fin_cases i
  · exact congrArg (PowerSeries.coeff 46) (hF 46)
  · exact congrArg (PowerSeries.coeff 58) (hG 58)
  · exact congrArg (PowerSeries.coeff 58) (hF 58)

/-- Reduction before the pivot leaves a monomial of that pivot order alone. -/
theorem reduceSeries_neg_monomial_at (p : NormalCoordinate → A) (n : ℕ) :
    reduceSeries p n (-(PowerSeries.X : PowerSeries A)^n) = -PowerSeries.X^n := by
  apply reduceSeries_eq_self_of_low_zero
  intro k hk
  rw [map_neg, PowerSeries.coeff_X_pow, ite_eq_right (by omega : k ≠ n), neg_zero]

end Ring

theorem relationCoordinate_linear_coefficient (i : Fin 3) :
    (relationCoordinatePolynomial i).coeff (Finsupp.single (coordinatePivot i) 1) = -1 := by
  rw [← weighted_linear_coefficient _ (relationCoordinate_weighted i)]
  have hev : MvPolynomial.eval (coordinateUnitPoint (coordinatePivot i)) (relationCoordinatePolynomial i) =
      relationCoordinate (coordinateUnitPoint (coordinatePivot i)) i := eval_relationCoordinatePolynomial _ i
  rw [hev]
  fin_cases i
  · change PowerSeries.coeff 46 (reduceSeries _ 46 (relationF _)) = -1
    rw [relationF_unit_Z _ (by rfl)]
    change PowerSeries.coeff 46 (reduceSeries _ 46 (-(PowerSeries.X : PowerSeries ℤ)^46)) = -1
    rw [reduceSeries_neg_monomial_at, map_neg, PowerSeries.coeff_X_pow]
    norm_num
  · change PowerSeries.coeff 58 (reduceSeries _ 58 (relationG _)) = -1
    rw [relationG_unit_W _ (by rfl)]
    change PowerSeries.coeff 58 (reduceSeries _ 58 (-(PowerSeries.X : PowerSeries ℤ)^58)) = -1
    rw [reduceSeries_neg_monomial_at, map_neg, PowerSeries.coeff_X_pow]
    norm_num
  · change PowerSeries.coeff 58 (reduceSeries _ 58 (relationF _)) = -1
    rw [relationF_unit_Z _ (by rfl)]
    change PowerSeries.coeff 58 (reduceSeries _ 58 (-(PowerSeries.X : PowerSeries ℤ)^58)) = -1
    rw [reduceSeries_neg_monomial_at, map_neg, PowerSeries.coeff_X_pow]
    norm_num

theorem coordinateA_W_linear_coefficient :
    (relationCoordinatePolynomial 0).coeff (Finsupp.single (coordinatePivot 1) 1) = 0 := by
  have hh : (relationCoordinatePolynomial 0).IsWeightedHomogeneous coordinateWeight
      (coordinateWeight (coordinatePivot 1)) := relationCoordinate_weighted 0
  rw [← weighted_linear_coefficient _ hh]
  have hev : MvPolynomial.eval (coordinateUnitPoint (coordinatePivot 1)) (relationCoordinatePolynomial 0) =
      relationCoordinate (coordinateUnitPoint (coordinatePivot 1)) 0 := eval_relationCoordinatePolynomial _ 0
  rw [hev]
  change PowerSeries.coeff 46 (reduceSeries _ 46 (relationF _)) = 0
  rw [relationF_unit_W _ (by rfl), map_zero, map_zero]

end EmbeddingDimensionStrata
