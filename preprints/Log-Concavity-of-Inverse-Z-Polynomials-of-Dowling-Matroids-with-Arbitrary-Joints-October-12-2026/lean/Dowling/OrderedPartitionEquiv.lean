import Dowling.PartitionOrderedWord

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] {n k : ℕ}

def OrderedPartition (G : Type*) [Group G] (n k : ℕ) :=
  Σ p : GainPartition G n, Fin k ≃ {i // p.IsRoot i}

def DecoratedWord (G : Type*) (n k : ℕ) := Σ w : OccupiedWord n k, w.Labels G

theorem orderedPartition_ext {p q : GainPartition G n} (hp : p=q)
    (e : Fin k ≃ {i // p.IsRoot i}) (f : Fin k ≃ {i // q.IsRoot i})
    (hef : ∀ c, (e c).val=(f c).val) : (⟨p,e⟩ : OrderedPartition G n k)=⟨q,f⟩ := by
  subst q
  have he : e=f := by
    apply Equiv.ext
    intro c
    exact Subtype.ext (hef c)
  subst f
  rfl

namespace OccupiedWord

theorem orderedWord_partition (w : OccupiedWord n k) (l : w.Labels G) :
    (w.partition l).orderedWord (w.rootEquiv l).symm=w := by
  apply Subtype.ext
  funext i
  change (w.partition l).orderedWordCode (w.rootEquiv l).symm i=w.val i
  cases hi : w.val i with
  | none =>
    apply GainPartition.orderedWordCode_none
    rw [partition_code,hi]
    rfl
  | some c =>
    have hp : (w.partition l).code i=some (w.root c,w.potential l i) := by
      rw [partition_code,hi]
      rfl
    rw [GainPartition.orderedWordCode_some _ _ _ _ _ hp]
    change some ((w.rootEquiv l).symm (w.rootEquiv l c))=some c
    rw [Equiv.symm_apply_apply]

theorem partition_labels_injective (w : OccupiedWord n k) : Function.Injective (w.partition (G := G)) := by
  intro l d h
  funext c i
  have hc := congrArg (fun p : GainPartition G n => p.code i.val) h
  simp only [partition_code,i.property.1,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hc
  have hp := hc.2
  rw [w.potential_nonanchor l c i,w.potential_nonanchor d c i] at hp
  exact hp

def orderedPartition (w : OccupiedWord n k) (l : w.Labels G) : OrderedPartition G n k :=
  ⟨w.partition l,w.rootEquiv l⟩

end OccupiedWord

/-- Exact labelled-block equivalence: root orderings account for the k! and
independent normalized labels account for each m^(blockSize−1). -/
def decoratedWordEquiv : DecoratedWord G n k ≃ OrderedPartition G n k :=
  Equiv.ofBijective (fun wl => wl.1.orderedPartition wl.2) (by
    constructor
    · rintro ⟨w,l⟩ ⟨v,d⟩ h
      have hw := congrArg (fun pe : OrderedPartition G n k => pe.1.orderedWord pe.2.symm) h
      change (w.partition l).orderedWord (w.rootEquiv l).symm =
        (v.partition d).orderedWord (v.rootEquiv d).symm at hw
      rw [w.orderedWord_partition l,v.orderedWord_partition d] at hw
      subst v
      have hp := congrArg (fun pe : OrderedPartition G n k => pe.1) h
      have hl : l=d := w.partition_labels_injective hp
      subst d
      rfl
    · rintro ⟨p,e⟩
      refine ⟨⟨p.orderedWord e.symm,p.orderedLabels e.symm⟩,?_⟩
      apply orderedPartition_ext (p.partition_orderedWord e.symm)
      intro c
      exact p.orderedWord_root e.symm c)

end Dowling
