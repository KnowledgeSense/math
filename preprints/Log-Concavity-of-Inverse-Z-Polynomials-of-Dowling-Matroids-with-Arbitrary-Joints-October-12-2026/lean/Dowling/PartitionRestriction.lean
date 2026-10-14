import Dowling.PartitionUpperEquiv

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n m : ℕ}

/-- A vertex set is closed under the actual component-root map. -/
def RootClosed (p : GainPartition G n) (e : Fin m ↪o Fin n) : Prop :=
  ∀ i r g, p.code (e i) = some (r,g) → ∃ j, e j=r

def restrictedRoot (p : GainPartition G n) (e : Fin m ↪o Fin n) (hc : p.RootClosed e)
    (i : Fin m) (r : Fin n) (g : G) (hi : p.code (e i)=some (r,g)) : Fin m :=
  (hc i r g hi).choose

theorem restrictedRoot_spec (p : GainPartition G n) (e : Fin m ↪o Fin n) (hc : p.RootClosed e)
    (i : Fin m) (r : Fin n) (g : G) (hi : p.code (e i)=some (r,g)) :
    e (p.restrictedRoot e hc i r g hi)=r := (hc i r g hi).choose_spec

def restrictionCode (p : GainPartition G n) (e : Fin m ↪o Fin n) (hc : p.RootClosed e)
    (i : Fin m) : Option (Fin m × G) :=
  match hi : p.code (e i) with
  | none => none
  | some (r,g) => some (p.restrictedRoot e hc i r g hi,g)

theorem restrictionCode_map (p : GainPartition G n) (e : Fin m ↪o Fin n) (hc : p.RootClosed e)
    (i : Fin m) : (p.restrictionCode e hc i).map (fun v => (e v.1,v.2))=p.code (e i) := by
  unfold restrictionCode
  split
  · rename_i hi
    exact hi.symm
  · rename_i r g hi
    simpa only [Option.map_some,p.restrictedRoot_spec e hc i r g hi] using hi.symm

omit [Group G] in
theorem restrictionCode_map_injective (e : Fin m ↪o Fin n) :
    Function.Injective (Option.map (fun v : Fin m × G => (e v.1,v.2))) := by
  intro a b h
  cases a with
  | none => cases b <;> simp_all
  | some a =>
    cases b with
    | none => simp_all
    | some b =>
      simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
      exact congrArg some (Prod.ext (e.injective h.1) h.2)

/-- Restriction to any ordered, root-closed vertex set. -/
def restrict (p : GainPartition G n) (e : Fin m ↪o Fin n) (hc : p.RootClosed e) : GainPartition G m where
  code := p.restrictionCode e hc
  rooted := by
    intro i j g hij
    have hcode := p.restrictionCode_map e hc i
    rw [hij] at hcode
    have hr := p.rooted (e i) (e j) g hcode.symm
    apply restrictionCode_map_injective e
    rw [p.restrictionCode_map e hc j]
    exact hr
  least := by
    intro i j g hij
    have hcode := p.restrictionCode_map e hc i
    rw [hij] at hcode
    exact e.le_iff_le.mp (p.least (e i) (e j) g hcode.symm)

@[simp] theorem restrict_code_map (p : GainPartition G n) (e : Fin m ↪o Fin n) (hc : p.RootClosed e)
    (i : Fin m) : ((p.restrict e hc).code i).map (fun v => (e v.1,v.2))=p.code (e i) :=
  p.restrictionCode_map e hc i

theorem restrict_isRoot (p : GainPartition G n) (e : Fin m ↪o Fin n) (hc : p.RootClosed e)
    (i : Fin m) : (p.restrict e hc).IsRoot i ↔ p.IsRoot (e i) := by
  constructor
  · intro hi
    have h := p.restrict_code_map e hc i
    rw [hi] at h
    exact h.symm
  · intro hi
    apply restrictionCode_map_injective e
    rw [p.restrict_code_map e hc i]
    exact hi

end Dowling.GainPartition
