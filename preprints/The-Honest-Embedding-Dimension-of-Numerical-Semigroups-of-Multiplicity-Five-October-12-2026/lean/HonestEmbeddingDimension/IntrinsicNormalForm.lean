import HonestEmbeddingDimension.ThreeCoordinateNormalForm
import HonestEmbeddingDimension.ClassificationArithmetic
import HonestEmbeddingDimension.TripleJets

namespace HonestEmbeddingDimension

theorem formal_characteristic_normal_form {S : NumericalSemigroup} {a b d : ℕ}
    (hm : HasMultiplicity S 5) (ha0 : 0 < a) (hb0 : 0 < b) (hcop : Nat.Coprime 5 a)
    (hav : a ∈ S.monoid) (hbv : b ∈ S.monoid) (ha : ¬5 ∣ a)
    (hmina : ∀ n ∈ S.monoid, ¬5 ∣ n → a ≤ n)
    (hb : b ∉ generatedPair 5 a)
    (hminb : ∀ n ∈ S.monoid, n ∉ generatedPair 5 a → b ≤ n)
    (hreal : FormallyRealizes S d) :
    ∃ (g : Fin d → PowerSeries ℂ) (i j k : Fin d),
      (∀ l, (g l).constantCoeff = 0) ∧ formalValues g = (S.monoid : Set ℕ) ∧
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ g i=PowerSeries.X^5 ∧ (g j).order=a ∧ (g k).order=b := by
  obtain ⟨f,hf0,hfS⟩ := hreal
  have hmem (n : ℕ) : n ∈ formalValues f ↔ n ∈ S.monoid := by rw [hfS]; rfl
  obtain ⟨g,i,j,k,hg0,hgv,hij,hik,hjk,hgi,hgj,hgk⟩ :=
    formal_three_coordinate_normal_form f hf0 5 a b (by omega) ha0 hb0 hcop
      ((hmem 5).mpr hm.2.1) (by intro n hn; exact hm.2.2 n ((hmem n).mp hn))
      ((hmem a).mpr hav) ha (by intro n hn; exact hmina n ((hmem n).mp hn))
      ((hmem b).mpr hbv) hb (by intro n hn; exact hminb n ((hmem n).mp hn))
  exact ⟨g,i,j,k,hg0,hgv.trans hfS,hij,hik,hjk,hgi,hgj,hgk⟩

theorem analytic_characteristic_dimension_ge_three {S : NumericalSemigroup} {a b d : ℕ}
    (hm : HasMultiplicity S 5) (ha0 : 0 < a) (hb0 : 0 < b) (hcop : Nat.Coprime 5 a)
    (hav : a ∈ S.monoid) (hbv : b ∈ S.monoid) (ha : ¬5 ∣ a)
    (hmina : ∀ n ∈ S.monoid, ¬5 ∣ n → a ≤ n)
    (hb : b ∉ generatedPair 5 a)
    (hminb : ∀ n ∈ S.monoid, n ∉ generatedPair 5 a → b ≤ n)
    (hreal : AnalyticallyRealizes S d) : 3 ≤ d := by
  obtain ⟨_,i,j,k,_,_,hij,hik,hjk,_⟩ :=
    formal_characteristic_normal_form hm ha0 hb0 hcop hav hbv ha hmina hb hminb hreal.formal
  exact three_le_of_distinct_coordinates i j k hij hik hjk

/-- Every genuine analytic three-dimensional realization admits the source's formal normal form. -/
theorem analytic_characteristic_triple {S : NumericalSemigroup} {a b : ℕ}
    (hm : HasMultiplicity S 5) (ha0 : 0 < a) (hb0 : 0 < b) (hcop : Nat.Coprime 5 a)
    (hav : a ∈ S.monoid) (hbv : b ∈ S.monoid) (ha : ¬5 ∣ a)
    (hmina : ∀ n ∈ S.monoid, ¬5 ∣ n → a ≤ n)
    (hb : b ∉ generatedPair 5 a)
    (hminb : ∀ n ∈ S.monoid, n ∉ generatedPair 5 a → b ≤ n)
    (hreal : AnalyticallyRealizes S 3) :
    ∃ Y Z : PowerSeries ℂ, Y.order=a ∧ Z.order=b ∧
      formalValues (tripleCoordinates 5 Y Z) = (S.monoid : Set ℕ) := by
  obtain ⟨g,i,j,k,hg0,hgv,hij,hik,hjk,hgi,hgj,hgk⟩ :=
    formal_characteristic_normal_form hm ha0 hb0 hcop hav hbv ha hmina hb hminb hreal.formal
  refine ⟨g j,g k,hgj,hgk,?_⟩
  have hperm := formalValues_reorder_three g hg0 i j k hij hik hjk
  have he : (![g i,g j,g k] : Fin 3 → PowerSeries ℂ) = tripleCoordinates 5 (g j) (g k) := by
    funext l
    fin_cases l <;> simp [tripleCoordinates,hgi]
  rw [he] at hperm
  exact hperm.trans hgv

end HonestEmbeddingDimension
