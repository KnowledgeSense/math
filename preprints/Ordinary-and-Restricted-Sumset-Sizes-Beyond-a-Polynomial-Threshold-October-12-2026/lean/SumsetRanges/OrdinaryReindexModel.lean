import SumsetRanges.OrdinaryIntegerModel

open Finset
namespace SumsetRanges

def ordinaryAtomReindex {ι κ τ : Type*} (e : ι ≃ κ) :
    OrdinaryLargeSpace ι τ →+ OrdinaryLargeSpace κ τ where
  toFun a := (fun i => a.1 (e.symm i),a.2)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem ordinaryAtomReindex_injective {ι κ τ : Type*} (e : ι ≃ κ) :
    Function.Injective (ordinaryAtomReindex (τ:=τ) e) := by
  intro a b he
  apply Prod.ext
  · funext i
    have hi := congrFun (congrArg Prod.fst he) (e i)
    simpa [ordinaryAtomReindex] using hi
  · exact congrArg (fun x : OrdinaryLargeSpace κ τ => x.2) he

theorem ordinary_finite_integer_model {ι τ : Type*} [Fintype ι] [Fintype τ]
    [DecidableEq ι] [DecidableEq τ]
    (h k : ℕ) (hh : 2≤h) (hk : h^2+2*h+2≤k) (hι : Fintype.card ι≤k)
    (hτ : Fintype.card τ+1≤2*h)
    (A : Finset (OrdinaryLargeSpace ι τ)) (hcard : A.card=k)
    (hA : ∀a∈A,(∑i,a.1 i)≤h ∧ a.2.1≤h*k ∧ ∀t,a.2.2 t=0 ∨ a.2.2 t=1) :
    ∃B : Finset ℤ,B.card=k ∧ (∀b∈B,0≤b ∧ b≤(k^(ordinaryExponent h):ℕ)) ∧
      ∀q≤h,(ordinarySums B q).card=(ordinarySums A q).card := by
  classical
  let e := Fintype.equivFin ι
  let φ := ordinaryAtomReindex (τ:=τ) e
  let A' := A.image φ
  have hi : Function.Injective φ := ordinaryAtomReindex_injective e
  have hc : A'.card=k := by rw [Finset.card_image_of_injective _ hi,hcard]
  have hb : ∀a∈A',(∑i,a.1 i)≤h ∧ a.2.1≤h*k ∧ ∀t,a.2.2 t=0 ∨ a.2.2 t=1 := by
    intro a ha
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    refine ⟨?_,(hA x hx).2⟩
    change (∑i,x.1 (e.symm i))≤h
    rw [Equiv.sum_comp e.symm]
    exact (hA x hx).1
  obtain ⟨B,hBc,hB,hBs⟩ := ordinary_integer_model h k (Fintype.card ι) hh hk hι hτ A' hc hb
  refine ⟨B,hBc,hB,?_⟩
  intro q hq
  rw [hBs q hq,ordinarySums_image,Finset.card_image_of_injective _ hi]

end SumsetRanges
