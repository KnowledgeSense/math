import PenneyDensity.Definitions

noncomputable section
namespace PenneyDensity
attribute [local instance] Classical.propDecidable

/-- Equality constraints whose edges always point to a smaller position.
This covers physically overlapping blocks without an independence assumption. -/
structure EqualityForest (N : ℕ) where
  active : Finset (Fin N)
  parent : Fin N → Fin N
  descending : ∀ i∈active,(parent i).val < i.val

namespace EqualityForest
variable {N : ℕ}

 def root (F : EqualityForest N) (i : Fin N) : {r : Fin N // r∉F.active} :=
  if hi : i∈F.active then root F (F.parent i) else ⟨i,hi⟩
termination_by i.val
decreasing_by exact F.descending i hi

 theorem root_inactive (F : EqualityForest N) (r : Fin N) (hr : r∉F.active) :
    F.root r=⟨r,hr⟩ := by rw [root,dite_eq_right hr]

 theorem root_active (F : EqualityForest N) (i : Fin N) (hi : i∈F.active) :
    F.root i=F.root (F.parent i) := by rw [root,dite_eq_left hi]

 def Satisfies (F : EqualityForest N) (f : Fin N → Bool) : Prop :=
  ∀ i∈F.active,f i=f (F.parent i)

 theorem value_at_root (F : EqualityForest N) (f : Fin N → Bool) (hf : F.Satisfies f)
    (i : Fin N) : f i=f (F.root i).val := by
  by_cases hi : i∈F.active
  · rw [F.root_active i hi,hf i hi]
    exact value_at_root F f hf (F.parent i)
  · rw [F.root_inactive i hi]
termination_by i.val
decreasing_by exact F.descending i hi

 def assignmentsEquiv (F : EqualityForest N) :
    {f : Fin N → Bool // F.Satisfies f} ≃ ({r : Fin N // r∉F.active} → Bool) where
  toFun f r := f.val r.val
  invFun g := ⟨fun i => g (F.root i),by
    intro i hi
    change g (F.root i)=g (F.root (F.parent i))
    rw [F.root_active i hi]⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    exact (F.value_at_root f.val f.property i).symm
  right_inv g := by
    funext r
    change g (F.root r.val)=g r
    rw [F.root_inactive r.val r.property]

 theorem card_assignments (F : EqualityForest N) :
    Fintype.card {f : Fin N → Bool // F.Satisfies f}=2^(N-F.active.card) := by
  classical
  rw [Fintype.card_congr F.assignmentsEquiv,Fintype.card_fun,Fintype.card_bool,
    Fintype.card_subtype_compl]
  simp

end EqualityForest

/-- An exact finite-coordinate cylinder count. -/
def fixedAssignmentsEquiv {α : Type*} [DecidableEq α] (S : Finset α) (v : α → Bool) :
    {f : α → Bool // ∀ i∈S,f i=v i} ≃ ({i : α // i∉S} → Bool) where
  toFun f i := f.val i.val
  invFun g := ⟨fun i => if hi : i∈S then v i else g ⟨i,hi⟩,by
    intro i hi
    simp only [dite_eq_left hi]⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    by_cases hi : i∈S
    · simp only [dite_eq_left hi]
      exact (f.property i hi).symm
    · simp only [dite_eq_right hi]
  right_inv g := by
    funext i
    simp only [dite_eq_right i.property]

 theorem card_fixed_assignments {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (v : α → Bool) :
    Fintype.card {f : α → Bool // ∀ i∈S,f i=v i}=2^(Fintype.card α-S.card) := by
  classical
  rw [Fintype.card_congr (fixedAssignmentsEquiv S v),Fintype.card_fun,
    Fintype.card_bool,Fintype.card_subtype_compl]
  simp

end PenneyDensity
