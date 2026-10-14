import SumsetRanges.RestrictedMain
import SumsetRanges.OrdinaryMain

open Finset
open scoped Pointwise
namespace OriginalStatementTests

/-- The fixed-release restricted main theorem, with definitions expanded. -/
theorem restricted_complete : ∀ h k : ℕ, 2 ≤ h → (2*h)^80 ≤ k →
    {t : ℕ | ∃ A : Finset ℤ, A.card = k ∧
      ((A.powersetCard h).image (fun S => ∑ a ∈ S, a)).card = t} =
      Set.Icc (h*(k-h)+1) (k.choose h) ∧
    ∀ t ∈ Set.Icc (h*(k-h)+1) (k.choose h), ∃ A : Finset ℤ,
      A.card = k ∧
      (∀ a ∈ A, 0 ≤ a ∧ a ≤
        (k^(4*h^2*(4*h^2+2*h+2) + Nat.clog 2
          ((4*h^2+2*h+2)*(4*h*(2*h+2)^(4*h^2)+2*h+1)*
            (h*(4*h*(2*h+2)^(4*h^2)+2*h+1)+1)^((4*h^2+2*h+2)-1))) : ℕ)) ∧
      ((A.powersetCard h).image (fun S => ∑ a ∈ S, a)).card = t := by
  exact SumsetRanges.restricted_main

/-- Independent tuple-sum presentation of the ordinary sumset. -/
def tupleSums (A : Finset ℤ) (h : ℕ) : Finset ℤ :=
  ((Finset.pi Finset.univ (fun _ : Fin h => A)).image
    (fun v => ∑ i : Fin h, v i (Finset.mem_univ i)))

theorem tupleSums_eq (A : Finset ℤ) (h : ℕ) :
    tupleSums A h = SumsetRanges.ordinarySums A h := by
  classical
  ext x
  simp only [tupleSums, Finset.mem_image, SumsetRanges.mem_ordinarySums]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨fun i => v i (Finset.mem_univ i), ?_, rfl⟩
    intro i
    exact Finset.mem_pi.mp hv i (Finset.mem_univ i)
  · rintro ⟨v, hv, rfl⟩
    exact ⟨fun i _ => v i, Finset.mem_pi.mpr (fun i _ => hv i), rfl⟩

/-- The fixed-release ordinary main theorem, including every excluded interval. -/
theorem ordinary_complete : ∀ h k : ℕ, 2 ≤ h → (2*h)^80 ≤ k →
    {t : ℕ | ∃ A : Finset ℤ, A.card = k ∧ (tupleSums A h).card = t} =
      Set.Icc (h*k-h+1) ((h+k-1).choose h) \
        ((Finset.range (min h k-2)).biUnion (fun l =>
          Finset.Icc (h*k-h+1+l*h+1) (h*k-h+1+l*h+(h-2-l))) : Set ℕ) ∧
    ∀ t ∈ Set.Icc (h*k-h+1) ((h+k-1).choose h) \
        ((Finset.range (min h k-2)).biUnion (fun l =>
          Finset.Icc (h*k-h+1+l*h+1) (h*k-h+1+l*h+(h-2-l))) : Set ℕ),
      ∃ A : Finset ℤ, A.card = k ∧
        (∀ a ∈ A, 0 ≤ a ∧ a ≤ (k^((h^2+2)*(h^2+2*h+2)) : ℕ)) ∧
        (tupleSums A h).card = t := by
  simpa only [tupleSums_eq, SumsetRanges.OrdinaryMainStatement, SumsetRanges.ordinaryRange,
    SumsetRanges.ordinaryMinimum, SumsetRanges.excludedValues, SumsetRanges.ordinaryExponent]
    using SumsetRanges.ordinary_main

/-- The full normalized Lev input is a proved consequence with no growth premise. -/
theorem lev_complete (B : Finset ℤ) (d j : ℕ) (hcard : 2 ≤ B.card)
    (hzero : 0 ∈ B) (hend : (d : ℤ) ∈ B)
    (hbound : ∀ b ∈ B, 0 ≤ b ∧ b ≤ d) (hgcd : B.gcd id = 1) (hj : 2 ≤ j) :
    (tupleSums B (j-1)).card + min d (j*(B.card-2)+1) ≤ (tupleSums B j).card := by
  simpa only [tupleSums_eq] using SumsetRanges.lev_growth B d j hcard hzero hend hbound hgcd hj

#print axioms restricted_complete
#print axioms ordinary_complete
#print axioms tupleSums_eq
#print axioms lev_complete
end OriginalStatementTests
