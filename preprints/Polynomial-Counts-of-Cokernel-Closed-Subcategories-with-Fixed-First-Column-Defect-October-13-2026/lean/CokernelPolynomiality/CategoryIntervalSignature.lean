import CokernelPolynomiality.CategoryClosureNecessity
import CokernelPolynomiality.CategoryCountingDefinitions

noncomputable section
namespace CokernelPolynomiality

theorem CokernelSubcategory.intervalSet_injective (n : ℕ) :
    Function.Injective (CokernelSubcategory.intervalSet (n:=n)) := by
  intro C D h
  apply CokernelSubcategory.ext_intervals
  intro a b hab hbn
  have hh := Iff.of_eq (congrArg (fun Y => (a,b) ∈ Y) h)
  simpa only [C.mem_intervalSet,D.mem_intervalSet,hab,hbn,true_and] using hh

theorem CokernelSubcategory.firstColumnSize_intervalSet {n : ℕ} (C : CokernelSubcategory n) :
    firstColumnSize C.intervalSet=C.firstColumnCard := by
  classical
  unfold firstColumnSize firstColumnCard
  symm
  apply Finset.card_bij (fun b _ => (0,b.val))
  · intro b hb
    obtain ⟨_,hC⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨C.mem_intervalSet.mpr ⟨Nat.zero_le _,by omega,hC⟩,rfl⟩
  · intro b hb c hc he
    apply Fin.ext
    exact congrArg Prod.snd he
  · intro p hp
    obtain ⟨hmem,hzero⟩ := Finset.mem_filter.mp hp
    obtain ⟨_,hpn,hC⟩ := C.mem_intervalSet.mp hmem
    have hp0 : p.1=0 := hzero
    let b : Fin (n+1) := ⟨p.2,by omega⟩
    refine ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
    · simpa only [hp0] using hC
    · exact Prod.ext hp0.symm rfl

end CokernelPolynomiality
