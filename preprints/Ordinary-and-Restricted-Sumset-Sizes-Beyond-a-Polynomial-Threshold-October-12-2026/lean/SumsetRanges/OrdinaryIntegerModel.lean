import SumsetRanges.OrdinaryCompactMoments
import SumsetRanges.OrdinaryModelExponent

open Finset
namespace SumsetRanges

/-- The release's ordinary moment model, with its stated exponent. -/
theorem ordinary_integer_model {τ : Type*} [Fintype τ] [DecidableEq τ]
    (h k n : ℕ) (hh : 2≤h) (hk : h^2+2*h+2≤k) (hn : n≤k)
    (hτ : Fintype.card τ+1≤2*h)
    (A : Finset (OrdinaryLargeSpace (Fin n) τ)) (hcard : A.card=k)
    (hA : ∀a∈A,(∑i,a.1 i)≤h ∧ a.2.1≤h*k ∧ ∀t,a.2.2 t=0 ∨ a.2.2 t=1) :
    ∃B : Finset ℤ,B.card=k ∧ (∀b∈B,0≤b ∧ b≤(k^(ordinaryExponent h):ℕ)) ∧
      ∀q≤h,(ordinarySums B q).card=(ordinarySums A q).card := by
  classical
  let L := h*h
  let φ := ordinaryCompactMoment n L τ
  let M := h*k^L
  let A' := A.image φ
  have hk1 : 1≤k := by omega
  have hh1 : 1≤h := by omega
  have hinj (q : ℕ) (hq : q≤h) : Set.InjOn φ (ordinarySums A q) :=
    ordinaryCompactMoment_injOn A h q (fun a ha => (hA a ha).1) hq
  have hinjA : Set.InjOn φ A := by
    simpa [ordinarySums] using hinj 1 (by omega)
  have hb : ∀a∈A',∀i,0≤a i ∧ a i≤(M:ℤ) := by
    intro a ha i
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    exact ordinaryCompactMoment_bounds h k hh1 hk1 hn x (hA x hx) i
  have hD : 1≤Fintype.card (OrdinaryCoordinate L τ) := by
    simp only [OrdinaryCoordinate,Fintype.card_sum,Fintype.card_fin,Fintype.card_option]; omega
  have hDh : Fintype.card (OrdinaryCoordinate L τ)≤h^2+2*h+2 := by
    simp only [OrdinaryCoordinate,Fintype.card_sum,Fintype.card_fin,Fintype.card_option]
    dsimp [L]
    nlinarith
  obtain ⟨B,hBc,hB,hBs⟩ := finite_bounded_ordinary_integer_model M h (h*M+1) A' hD hh1 (by omega) hb
  refine ⟨B,?_,?_,?_⟩
  · rw [hBc,Finset.card_image_of_injOn hinjA,hcard]
  · intro b hb'
    refine ⟨(hB b hb').1,(hB b hb').2.trans ?_⟩
    exact_mod_cast ordinary_model_diameter_bound h k (Fintype.card (OrdinaryCoordinate L τ))
      hh1 (by nlinarith) hD (hDh.trans hk) hDh
  · intro q hq
    rw [hBs q hq]
    change (ordinarySums (A.image φ) q).card=(ordinarySums A q).card
    rw [ordinarySums_image]
    exact Finset.card_image_of_injOn (hinj q hq)

end SumsetRanges
