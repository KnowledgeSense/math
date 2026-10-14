import SumsetRanges.ExtendedMoments

open Finset
namespace SumsetRanges

def reindexCoordinates {ι κ : Type*} (e : ι ≃ κ) : (ι → ℤ) →+ (κ → ℤ) where
  toFun v := v ∘ e.symm
  map_zero' := rfl
  map_add' _ _ := rfl

theorem reindexCoordinates_injective {ι κ : Type*} (e : ι ≃ κ) :
    Function.Injective (reindexCoordinates e) := by
  intro v w he
  funext i
  have h := congrFun he (e i)
  simpa [reindexCoordinates] using h

theorem finite_bounded_integer_model {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M h Q : ℕ) (A : Finset (ι → ℤ)) (hD : 1≤Fintype.card ι) (hh : 1≤h) (hQ : h*M<Q)
    (hA : ∀ a∈A,∀ i,0≤a i ∧ a i≤(M:ℤ)) :
    ∃ B : Finset ℤ, B.card=A.card ∧
      (∀ b∈B,0≤b ∧ b≤(Fintype.card ι*M*Q^(Fintype.card ι-1):ℕ)) ∧
      ∀ q≤h,(restrictedSums B q).card=(restrictedSums A q).card := by
  classical
  let e := Fintype.equivFin ι
  let φ := reindexCoordinates e
  let A' := A.image φ
  have hA' : ∀ a∈A',∀ i,0≤a i ∧ a i≤(M:ℤ) := by
    intro a ha i
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    exact hA x hx (e.symm i)
  obtain ⟨B,hBc,hB,hBs⟩ := bounded_integer_model (Fintype.card ι) M h Q A' hD hh hQ hA'
  refine ⟨B,?_,hB,?_⟩
  · rw [hBc]
    exact Finset.card_image_of_injective _ (reindexCoordinates_injective e)
  · intro q hq
    rw [hBs q hq]
    exact card_restrictedSums_image A φ (reindexCoordinates_injective e).injOn q
      (reindexCoordinates_injective e).injOn

end SumsetRanges
