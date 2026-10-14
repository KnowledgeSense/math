import SumsetRanges.OrdinaryMixedSpace
import SumsetRanges.CarryHSeries

open Finset
namespace SumsetRanges

def mixedLiftHom (ι : Type*) : ((ι→ℕ)×ℤ) →+ OrdinarySpace ι (Fin 1) where
  toFun a := (a.1,fun _ => a.2)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem mixedLiftHom_injective (ι : Type*) : Function.Injective (mixedLiftHom ι) := by
  intro a b he
  apply Prod.ext
  · exact congrArg (fun x : OrdinarySpace ι (Fin 1) => x.1) he
  · exact congrFun (congrArg (fun x : OrdinarySpace ι (Fin 1) => x.2) he) 0

noncomputable def mixedLift {ι : Type*} [Fintype ι] (A : Finset (ι→ℕ)) :
    Finset (OrdinarySpace ι (Fin 1)) := by
  classical
  exact (homogenized A).image (mixedLiftHom ι)

theorem mixedLift_bound {ι : Type*} [Fintype ι] (A : Finset (ι→ℕ)) (H : ℕ)
    (hA : ∀a∈A,(∑i,a i)≤H) : ∀a∈mixedLift A,MixedBound H a := by
  classical
  intro a ha
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
  refine ⟨hA v hv,fun _ => Or.inr rfl,?_⟩
  simp [mixedDegree,mixedLiftHom]

theorem mixedLift_degree {ι : Type*} [Fintype ι] (A : Finset (ι→ℕ)) :
    ∀a∈mixedLift A,mixedDegree ι (Fin 1) a=1 := by
  classical
  intro a ha
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hp
  simp [mixedDegree,mixedLiftHom]

theorem card_mixedLift {ι : Type*} [Fintype ι] (A : Finset (ι→ℕ)) :
    (mixedLift A).card=A.card := by
  classical
  rw [mixedLift,Finset.card_image_of_injective _ (mixedLiftHom_injective _),card_homogenized]

theorem ordinarySeries_mixedLift {ι : Type*} [Fintype ι] (A : Finset (ι→ℕ)) :
    ordinarySeries (mixedLift A)=ordinarySeries A := by
  classical
  rw [mixedLift,ordinarySeries_image_injective _ _ (mixedLiftHom_injective _),ordinarySeries_homogenized]

theorem carryH_mass_bound (m r : ℕ) (hm : 1≤m) : ∀v∈carryH m r,(∑i,v i)≤m := by
  intro v hv
  obtain ⟨⟨i,b⟩,_,rfl⟩ := Finset.mem_image.mp hv
  cases b <;> simp [carryPoint]
  exact hm

theorem carryG_mass_bound (m r : ℕ) (hm : 1≤m) : ∀v∈carryG m r,(∑i,v i)≤m := by
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · simp
  · exact carryH_mass_bound m r hm v hv

noncomputable def ordinaryPair (m r u : ℕ) := mixedJoin
  (mixedLift (carryG (m+1) r)) (mixedLift (carryH m u))

theorem ordinaryPair_bound (m r u : ℕ) (hm : 2≤m) :
    ∀a∈ordinaryPair m r u,MixedBound (m+1) a := by
  apply mixedJoin_bound
  · exact mixedLift_bound _ _ (carryG_mass_bound _ _ (by omega))
  · exact mixedLift_bound _ _ (fun v hv => (carryH_mass_bound m u (by omega) v hv).trans (by omega))

theorem card_ordinaryPair (m r u : ℕ) (hm : 2≤m) :
    (ordinaryPair m r u).card=2*r+1+2*u := by
  rw [ordinaryPair,card_mixedJoin _ _ (mixedLift_degree _),card_mixedLift,card_mixedLift,
    card_carryG _ _ (by omega),card_carryH _ _ hm]

theorem ordinarySeries_ordinaryPair (m r u : ℕ) :
    ordinarySeries (ordinaryPair m r u)=ordinarySeries (carryG (m+1) r)*ordinarySeries (carryH m u) := by
  rw [ordinaryPair,ordinarySeries_mixedJoin _ _ (mixedLift_degree _),ordinarySeries_mixedLift,ordinarySeries_mixedLift]

end SumsetRanges
