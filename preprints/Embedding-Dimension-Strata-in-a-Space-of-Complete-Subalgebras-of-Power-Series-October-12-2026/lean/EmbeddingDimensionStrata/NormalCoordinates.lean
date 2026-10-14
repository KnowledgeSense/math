import EmbeddingDimensionStrata.NormalGenerators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.MvPolynomial.Basic

/-! # The 62 genuine normal-form coefficients -/
noncomputable section
namespace EmbeddingDimensionStrata

/-- Coordinates are precisely the gaps above the five minimal values. -/
abbrev NormalCoordinate :=
  {p : Fin 5 × Fin 60 // generatorValue p.1 < p.2.val ∧ p.2.val ∉ valuesBelowConductor}

/-- There are 62 coefficients in the actual normal forms. -/
theorem normalCoordinate_card : Fintype.card NormalCoordinate = 62 := by decide

/-- The universal normal-form series attached to arbitrary coefficient values.
The construction works over any commutative ring, hence also over a polynomial ring. -/
def normalSeries {A : Type*} [CommRing A] (p : NormalCoordinate → A) (i : Fin 5) :
    PowerSeries A :=
  PowerSeries.mk fun n =>
    if n = generatorValue i then 1 else
    if h : n < 60 ∧ generatorValue i < n ∧ n ∉ valuesBelowConductor then
      p ⟨(i, ⟨n, h.1⟩), h.2⟩ else 0

theorem coeff_normalSeries {A : Type*} [CommRing A] (p : NormalCoordinate → A)
    (i : Fin 5) (n : ℕ) :
    PowerSeries.coeff n (normalSeries p i) =
      if n = generatorValue i then 1 else
      if h : n < 60 ∧ generatorValue i < n ∧ n ∉ valuesBelowConductor then
        p ⟨(i, ⟨n, h.1⟩), h.2⟩ else 0 := by
  rw [normalSeries, PowerSeries.coeff_mk]

theorem coeff_normalSeries_coordinate {A : Type*} [CommRing A]
    (p : NormalCoordinate → A) (j : NormalCoordinate) :
    PowerSeries.coeff j.val.2.val (normalSeries p j.val.1) = p j := by
  rw [coeff_normalSeries, ite_eq_right (by omega : j.val.2.val ≠ generatorValue j.val.1)]
  rw [dite_eq_left ⟨j.val.2.isLt, j.property⟩]

theorem normalSeries_normal {K : Type*} [Field K]
    (p : NormalCoordinate → K) (i : Fin 5) :
    IsNormalForm (generatorValue i) (normalSeries p i) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [coeff_normalSeries, ite_eq_left rfl]
  · intro n hn
    rw [coeff_normalSeries, ite_eq_right (by omega : n ≠ generatorValue i)]
    rw [dite_eq_right (by omega : ¬ (n < 60 ∧ generatorValue i < n ∧ n ∉ valuesBelowConductor))]
  · intro n hn hng
    rw [coeff_normalSeries, ite_eq_right (by omega : n ≠ generatorValue i)]
    apply dite_eq_right
    rintro ⟨hn60, _, hnot⟩
    rcases hng with hg | hh
    · exact hnot ((gamma_below_conductor hn60).mp hg)
    · omega

variable {K : Type*} [Field K] [TopologicalSpace K]
open scoped PowerSeries.WithPiTopology

/-- The coefficient map on actual complete embedded subalgebras. -/
def normalCoordinates (S : CompleteGammaSubalgebra (K := K)) : NormalCoordinate → K :=
  fun j => PowerSeries.coeff j.val.2.val (normalGenerator S j.val.1)

/-- Reconstructing the entire infinite series from its 62 coefficient coordinates
recovers the actual canonical generators, not only their first 60 coefficients. -/
theorem normalSeries_normalCoordinates (S : CompleteGammaSubalgebra (K := K))
    (i : Fin 5) : normalSeries (normalCoordinates S) i = normalGenerator S i := by
  ext n
  rw [coeff_normalSeries]
  have hnorm := normalGenerator_normal S i
  split_ifs with heq htail
  · rw [heq]
    exact hnorm.1.symm
  · rfl
  · by_cases hn : n < generatorValue i
    · exact (hnorm.2.1 n hn).symm
    · have hgt : generatorValue i < n := by omega
      apply (hnorm.2.2 n hgt ?_).symm
      by_cases h60 : n < 60
      · exact Or.inl ((gamma_below_conductor h60).mpr (by
          by_contra hnot
          exact htail ⟨h60, hgt, hnot⟩))
      · exact Or.inr (by omega)

/-- The coefficient parametrization is injective on genuine complete subalgebras. -/
theorem normalCoordinates_injective [DiscreteTopology K] :
    Function.Injective (normalCoordinates (K := K)) := by
  intro S T h
  apply normalGenerator_injective
  funext i
  rw [← normalSeries_normalCoordinates S i, ← normalSeries_normalCoordinates T i, h]

end EmbeddingDimensionStrata
