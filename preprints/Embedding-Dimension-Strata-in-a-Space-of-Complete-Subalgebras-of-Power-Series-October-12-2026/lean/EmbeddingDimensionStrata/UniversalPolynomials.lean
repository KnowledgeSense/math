import EmbeddingDimensionStrata.Relations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! # Universal polynomial equations and their positive weight grading -/
set_option maxRecDepth 4096
noncomputable section
namespace EmbeddingDimensionStrata

/-- All coefficients are defined integrally, before specializing to ℂ. -/
abbrev CoordinatePolynomial := MvPolynomial NormalCoordinate ℤ

def coordinateWeight (j : NormalCoordinate) : ℤ :=
  (j.val.2.val : ℤ) - generatorValue j.val.1

theorem coordinateWeight_pos (j : NormalCoordinate) : 0 < coordinateWeight j := by
  have hj := j.property.1
  dsimp [coordinateWeight]
  omega

/-- The universal generator coefficients are the coordinate indeterminates. -/
def universalPoint : NormalCoordinate → CoordinatePolynomial := MvPolynomial.X

/-- Coefficients of an order-ν series have weight n-ν, including the zero
coefficients in degrees below ν. -/
def IsWeightedSeries (f : PowerSeries CoordinatePolynomial) (ν : ℤ) : Prop :=
  ∀ n, (PowerSeries.coeff n f).IsWeightedHomogeneous coordinateWeight ((n : ℤ)-ν)

theorem normalSeries_weighted (i : Fin 5) :
    IsWeightedSeries (normalSeries universalPoint i) (generatorValue i) := by
  intro n
  rw [coeff_normalSeries]
  split_ifs with hn hh
  · subst n
    simp only [sub_self]
    exact MvPolynomial.isWeightedHomogeneous_one ℤ coordinateWeight
  · exact MvPolynomial.isWeightedHomogeneous_X ℤ coordinateWeight
      ⟨(i,⟨n,hh.1⟩),hh.2⟩
  · exact MvPolynomial.isWeightedHomogeneous_zero ℤ coordinateWeight _

theorem IsWeightedSeries.one : IsWeightedSeries (1 : PowerSeries CoordinatePolynomial) 0 := by
  intro n
  by_cases hn : n = 0
  · subst n
    simpa using MvPolynomial.isWeightedHomogeneous_one ℤ coordinateWeight
  · rw [PowerSeries.coeff_one, ite_eq_right hn]
    exact MvPolynomial.isWeightedHomogeneous_zero ℤ coordinateWeight _

theorem IsWeightedSeries.mul {f g : PowerSeries CoordinatePolynomial} {ν μ : ℤ}
    (hf : IsWeightedSeries f ν) (hg : IsWeightedSeries g μ) :
    IsWeightedSeries (f*g) (ν+μ) := by
  intro n
  rw [PowerSeries.coeff_mul]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro ab hab
  have heq := Finset.mem_antidiagonal.mp hab
  convert (hf ab.1).mul (hg ab.2) using 1
  omega

theorem IsWeightedSeries.pow {f : PowerSeries CoordinatePolynomial} {ν : ℤ}
    (hf : IsWeightedSeries f ν) (n : ℕ) : IsWeightedSeries (f^n) (ν*n) := by
  induction n with
  | zero => simpa using IsWeightedSeries.one
  | succ n ih =>
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one, mul_add, mul_one] using ih.mul hf

theorem IsWeightedSeries.sub {f g : PowerSeries CoordinatePolynomial} {ν : ℤ}
    (hf : IsWeightedSeries f ν) (hg : IsWeightedSeries g ν) : IsWeightedSeries (f-g) ν := by
  intro n
  rw [map_sub]
  exact (hf n).sub (hg n)

theorem seriesMonomial_weighted (a : Exponent) :
    IsWeightedSeries (seriesMonomial universalPoint a) (monomialWeight a) := by
  have hh := ((((normalSeries_weighted 0).pow a.1).mul
      ((normalSeries_weighted 1).pow a.2.1)).mul
      ((normalSeries_weighted 2).pow a.2.2.1)).mul
      ((normalSeries_weighted 3).pow a.2.2.2.1) |>.mul
      ((normalSeries_weighted 4).pow a.2.2.2.2)
  simpa [seriesMonomial, monomialWeight, generatorValue] using hh

theorem basisSeries_weighted (n : ℕ) (hn : n ∈ valuesBelowConductor) :
    IsWeightedSeries (basisSeries universalPoint n) n := by
  simpa only [basisSeries, basisExponent_weight n hn] using
    seriesMonomial_weighted (basisExponent n)

/-- Every subtraction in the division algorithm preserves the grading. -/
theorem reduceSeries_weighted (f : PowerSeries CoordinatePolynomial) (ν : ℤ)
    (hf : IsWeightedSeries f ν) (N : ℕ) :
    IsWeightedSeries (reduceSeries universalPoint N f) ν := by
  induction N with
  | zero => exact hf
  | succ n ih =>
    intro i
    rw [reduceSeries_succ]
    split_ifs with hn
    · rw [map_sub, map_smul, smul_eq_mul]
      apply (ih i).sub
      convert (ih n).mul (basisSeries_weighted n hn i) using 1
      omega
    · exact ih i

theorem relationF_weighted : IsWeightedSeries (relationF universalPoint) 44 :=
  ((normalSeries_weighted 1).pow 4).sub
    ((normalSeries_weighted 0).mul (normalSeries_weighted 2))

theorem relationG_weighted : IsWeightedSeries (relationG universalPoint) 56 :=
  (((normalSeries_weighted 1).pow 2).mul (normalSeries_weighted 2)).sub
    ((normalSeries_weighted 0).mul (normalSeries_weighted 3))

/-- The five actual defining polynomials. -/
def definingPolynomial (i : Fin 5) : CoordinatePolynomial := definingEquation universalPoint i

def equationWeight (i : Fin 5) : ℤ :=
  match i.val with | 0 => 3 | 1 => 4 | 2 => 3 | 3 => 5 | _ => 15

theorem definingPolynomial_weighted (i : Fin 5) :
    (definingPolynomial i).IsWeightedHomogeneous coordinateWeight (equationWeight i) := by
  have hF := reduceSeries_weighted _ 44 relationF_weighted 60
  have hG := reduceSeries_weighted _ 56 relationG_weighted 60
  fin_cases i
  · exact hF 47
  · exact hF 48
  · exact hG 59
  · exact hF 49
  · exact hF 59

section Specialization
variable {A B : Type*} [CommRing A] [CommRing B]

theorem map_normalSeries (φ : A →+* B) (p : NormalCoordinate → A) (i : Fin 5) :
    PowerSeries.map φ (normalSeries p i) = normalSeries (fun j => φ (p j)) i := by
  ext n
  simp only [PowerSeries.coeff_map, coeff_normalSeries]
  split_ifs <;> simp only [map_one, map_zero]

theorem map_basisSeries (φ : A →+* B) (p : NormalCoordinate → A) (n : ℕ) :
    PowerSeries.map φ (basisSeries p n) = basisSeries (fun j => φ (p j)) n := by
  simp only [basisSeries, seriesMonomial, map_mul, map_pow, map_normalSeries]

theorem map_smul_series (φ : A →+* B) (a : A) (f : PowerSeries A) :
    PowerSeries.map φ (a • f) = φ a • PowerSeries.map φ f := by
  ext n
  simp only [PowerSeries.coeff_map, map_smul, smul_eq_mul, map_mul]

/-- The entire elimination, not just selected expanded coefficients, commutes
with coefficient specialization. -/
theorem map_reduceSeries (φ : A →+* B) (p : NormalCoordinate → A)
    (f : PowerSeries A) (N : ℕ) :
    PowerSeries.map φ (reduceSeries p N f) =
      reduceSeries (fun j => φ (p j)) N (PowerSeries.map φ f) := by
  induction N with
  | zero => rfl
  | succ n ih =>
    rw [reduceSeries_succ, reduceSeries_succ]
    split_ifs <;> simp only [map_sub, map_smul_series, map_basisSeries, ih,
      ← PowerSeries.coeff_map]

theorem map_relationF (φ : A →+* B) (p : NormalCoordinate → A) :
    PowerSeries.map φ (relationF p) = relationF (fun j => φ (p j)) := by
  simp only [relationF, map_sub, map_pow, map_mul, map_normalSeries]

theorem map_relationG (φ : A →+* B) (p : NormalCoordinate → A) :
    PowerSeries.map φ (relationG p) = relationG (fun j => φ (p j)) := by
  simp only [relationG, map_sub, map_pow, map_mul, map_normalSeries]

theorem map_definingEquation (φ : A →+* B) (p : NormalCoordinate → A) (i : Fin 5) :
    φ (definingEquation p i) = definingEquation (fun j => φ (p j)) i := by
  have hF := map_reduceSeries φ p (relationF p) 60
  have hG := map_reduceSeries φ p (relationG p) 60
  rw [map_relationF] at hF
  rw [map_relationG] at hG
  fin_cases i
  · exact (congrArg (PowerSeries.coeff 47) hF)
  · exact (congrArg (PowerSeries.coeff 48) hF)
  · exact (congrArg (PowerSeries.coeff 59) hG)
  · exact (congrArg (PowerSeries.coeff 49) hF)
  · exact (congrArg (PowerSeries.coeff 59) hF)

/-- Evaluation of the universal polynomial is exactly the defining coefficient
of the actual specialized normal forms. -/
theorem eval_definingPolynomial (p : NormalCoordinate → A) (i : Fin 5) :
    MvPolynomial.eval₂ (Int.castRingHom A) p (definingPolynomial i) = definingEquation p i := by
  have h := map_definingEquation (MvPolynomial.eval₂Hom (Int.castRingHom A) p) universalPoint i
  have hp : (fun j => MvPolynomial.eval₂Hom (Int.castRingHom A) p (universalPoint j)) = p := by
    funext j
    exact MvPolynomial.eval₂_X _ _ j
  rw [hp] at h
  exact h

end Specialization
end EmbeddingDimensionStrata
