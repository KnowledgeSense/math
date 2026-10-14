import Dowling.OrderedWordPartition

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n k : ℕ}

def orderedWordCode (p : GainPartition G n) (e : {i // p.IsRoot i} ≃ Fin k)
    (i : Fin n) : Option (Fin k) :=
  match hi : p.code i with
  | none => none
  | some (r,g) => some (e ⟨r,p.rooted i r g hi⟩)

theorem orderedWordCode_none (p : GainPartition G n) (e : {i // p.IsRoot i} ≃ Fin k)
    (i : Fin n) (hi : p.code i=none) : p.orderedWordCode e i=none := by
  unfold orderedWordCode
  split <;> simp_all

theorem orderedWordCode_some (p : GainPartition G n) (e : {i // p.IsRoot i} ≃ Fin k)
    (i r : Fin n) (g : G) (hi : p.code i=some (r,g)) :
    p.orderedWordCode e i=some (e ⟨r,p.rooted i r g hi⟩) := by
  unfold orderedWordCode
  split
  · rename_i h
    rw [hi] at h
    cases h
  · rename_i r' g' h
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (hi.symm.trans h))
    rfl

def orderedWord (p : GainPartition G n) (e : {i // p.IsRoot i} ≃ Fin k) : OccupiedWord n k :=
  ⟨p.orderedWordCode e,fun c => by
    refine ⟨(e.symm c).val,?_⟩
    rw [p.orderedWordCode_some e _ _ 1 (e.symm c).property]
    exact congrArg some (e.apply_symm_apply c)⟩

theorem orderedWord_root (p : GainPartition G n) (e : {i // p.IsRoot i} ≃ Fin k) (c : Fin k) :
    (p.orderedWord e).root c=(e.symm c).val := by
  have hc : (p.orderedWord e).val (e.symm c).val=some c := by
    change p.orderedWordCode e (e.symm c).val=some c
    rw [p.orderedWordCode_some e _ _ 1 (e.symm c).property]
    exact congrArg some (e.apply_symm_apply c)
  apply le_antisymm ((p.orderedWord e).root_le c _ hc)
  have hw := (p.orderedWord e).root_color c
  let i := (p.orderedWord e).root c
  change p.orderedWordCode e i=some c at hw
  cases hi : p.code i with
  | none => rw [p.orderedWordCode_none e i hi] at hw; cases hw
  | some v =>
    rcases v with ⟨r,g⟩
    rw [p.orderedWordCode_some e i r g hi] at hw
    have hr : (⟨r,p.rooted i r g hi⟩ : {i // p.IsRoot i})=e.symm c := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact Option.some.inj hw
    have hrv := congrArg Subtype.val hr
    rw [← hrv]
    exact p.least i r g hi

def codePotential (p : GainPartition G n) (i : Fin n) : G := ((p.code i).map Prod.snd).getD 1

def orderedLabels (p : GainPartition G n) (e : {i // p.IsRoot i} ≃ Fin k) :
    (p.orderedWord e).Labels G := fun _ i => p.codePotential i.val

theorem orderedPotential_some (p : GainPartition G n) (e : {i // p.IsRoot i} ≃ Fin k)
    (i r : Fin n) (g : G) (hi : p.code i=some (r,g)) :
    (p.orderedWord e).potential (p.orderedLabels e) i=g := by
  let c := e ⟨r,p.rooted i r g hi⟩
  have hw : (p.orderedWord e).val i=some c := p.orderedWordCode_some e i r g hi
  have hr : (p.orderedWord e).root c=r := by
    rw [p.orderedWord_root]
    exact congrArg Subtype.val (e.symm_apply_apply _)
  by_cases hir : i=(p.orderedWord e).root c
  · rw [hir,(p.orderedWord e).potential_root]
    have hir' : i=r := hir.trans hr
    have he := Option.some.inj (hi.symm.trans
      ((congrArg p.code hir').trans (p.rooted i r g hi)))
    exact (congrArg Prod.snd he).symm
  · rw [(p.orderedWord e).potential_nonanchor (p.orderedLabels e) c ⟨i,hw,hir⟩]
    change p.codePotential i=g
    simp only [codePotential,hi,Option.map_some,Option.getD_some]

theorem partition_orderedWord (p : GainPartition G n) (e : {i // p.IsRoot i} ≃ Fin k) :
    (p.orderedWord e).partition (p.orderedLabels e)=p := by
  apply code_injective
  funext i
  rw [OccupiedWord.partition_code]
  cases hi : p.code i with
  | none =>
    rw [show (p.orderedWord e).val i=none from p.orderedWordCode_none e i hi]
    rfl
  | some v =>
    rcases v with ⟨r,g⟩
    rw [show (p.orderedWord e).val i=some (e ⟨r,p.rooted i r g hi⟩) from p.orderedWordCode_some e i r g hi]
    simp only [Option.map_some]
    rw [p.orderedWord_root,p.orderedPotential_some e i r g hi]
    exact congrArg (fun x => some (x,g)) (congrArg Subtype.val (e.symm_apply_apply _))

end Dowling.GainPartition
