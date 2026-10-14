import Dowling.OrderedWordDefinitions

noncomputable section
namespace Dowling.OccupiedWord
open scoped Classical
variable {G : Type*} [Group G] {n k : ℕ}

def potential (w : OccupiedWord n k) (l : w.Labels G) (i : Fin n) : G :=
  match hi : w.val i with
  | none => 1
  | some c => if h : i=w.root c then 1 else l c ⟨i,hi,h⟩

theorem potential_root (w : OccupiedWord n k) (l : w.Labels G) (c : Fin k) :
    w.potential l (w.root c)=1 := by
  unfold potential
  split
  · rfl
  · rename_i d hd
    have he : d=c := Option.some.inj (hd.symm.trans (w.root_color c))
    subst d
    simp

theorem potential_nonanchor (w : OccupiedWord n k) (l : w.Labels G) (c : Fin k)
    (i : w.Nonanchor c) : w.potential l i.val=l c i := by
  unfold potential
  split
  · rename_i hi
    rw [i.property.1] at hi
    cases hi
  · rename_i d hd
    have he : d=c := Option.some.inj (hd.symm.trans i.property.1)
    subst d
    simp only [dite_eq_right i.property.2]
    rfl

def partition (w : OccupiedWord n k) (l : w.Labels G) : GainPartition G n where
  code i := (w.val i).map (fun c => (w.root c,w.potential l i))
  rooted := by
    intro i j g hij
    cases hi : w.val i with
    | none => simp [hi] at hij
    | some c =>
      simp only [hi,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hij
      obtain ⟨rfl,rfl⟩ := hij
      rw [w.root_color c,w.potential_root l c]
      rfl
  least := by
    intro i j g hij
    cases hi : w.val i with
    | none => simp [hi] at hij
    | some c =>
      simp only [hi,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hij
      obtain ⟨rfl,rfl⟩ := hij
      exact w.root_le c i hi

theorem partition_code (w : OccupiedWord n k) (l : w.Labels G) (i : Fin n) :
    (w.partition l).code i=(w.val i).map (fun c => (w.root c,w.potential l i)) := rfl

theorem partition_root (w : OccupiedWord n k) (l : w.Labels G) (c : Fin k) :
    (w.partition l).IsRoot (w.root c) := by
  change (w.val (w.root c)).map _=some (w.root c,1)
  rw [w.root_color c,w.potential_root l c]
  rfl

theorem partition_root_exists (w : OccupiedWord n k) (l : w.Labels G) (i : Fin n)
    (hi : (w.partition l).IsRoot i) : ∃ c, w.root c=i := by
  change (w.val i).map _=some (i,1) at hi
  cases hw : w.val i with
  | none => simp [hw] at hi
  | some c =>
    simp only [hw,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hi
    exact ⟨c,hi.1⟩

/-- The ordered block labels are exactly an ordering of the actual partition roots. -/
def rootEquiv (w : OccupiedWord n k) (l : w.Labels G) : Fin k ≃ {i // (w.partition l).IsRoot i} :=
  Equiv.ofBijective (fun c => ⟨w.root c,w.partition_root l c⟩) (by
    constructor
    · intro c d h
      exact w.root_injective (congrArg Subtype.val h)
    · intro i
      obtain ⟨c,hc⟩ := w.partition_root_exists l i.val i.property
      exact ⟨c,Subtype.ext hc⟩)

theorem partition_roots_card (w : OccupiedWord n k) (l : w.Labels G) :
    (w.partition l).roots.card=k := by
  have h := Fintype.card_congr (w.rootEquiv l)
  rw [Fintype.card_fin,Fintype.card_subtype] at h
  exact h.symm

end Dowling.OccupiedWord
