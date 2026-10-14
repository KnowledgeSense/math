import Dowling.PartitionCompression
import Dowling.FullUpperIntervals

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

theorem ext_code {p q : GainPartition G n} (h : p.code=q.code) : p=q := by
  cases p
  cases q
  cases h
  rfl

/-- One nonempty balanced block, with its actual (possibly noncommutative) gains. -/
def SingleBalancedBlock (p : GainPartition G n) : Prop :=
  ∃ r, ∀ i, ∃ g, p.code i=some (r,g)

/-- A canonical block-root map with vertex potentials gives a literal balanced
partition. Every vertex remains in a nonzero block. -/
def fromBlockRoots (R : Fin n → Fin n) (hR : ∀ i, R (R i)=R i)
    (hmin : ∀ i, R i ≤ i) (u : Fin n → G) : GainPartition G n where
  code i := some (R i,(u (R i))⁻¹*u i)
  rooted := by
    intro i j g h
    have hr : R i=j := congrArg Prod.fst (Option.some.inj h)
    subst j
    simp only [hR,inv_mul_cancel]
  least := by
    intro i j g h
    have hr : R i=j := congrArg Prod.fst (Option.some.inj h)
    rw [← hr]
    exact hmin i

/-- The extra distinguished vertex records the zero block of a trivial-group
Dowling partition. -/
def unitBlockRoot (p : GainPartition Unit n) : Fin (n+1) → Fin (n+1) :=
  Fin.cases 0 (fun i => match p.code i with
    | none => 0
    | some (r,_) => r.succ)

@[simp] theorem unitBlockRoot_zero (p : GainPartition Unit n) : p.unitBlockRoot 0=0 := rfl

 theorem unitBlockRoot_succ_none (p : GainPartition Unit n) (i : Fin n)
    (hi : p.code i=none) : p.unitBlockRoot i.succ=0 := by
  simp [unitBlockRoot,hi]

 theorem unitBlockRoot_succ_some (p : GainPartition Unit n) (i r : Fin n) (g : Unit)
    (hi : p.code i=some (r,g)) : p.unitBlockRoot i.succ=r.succ := by
  simp [unitBlockRoot,hi]

 theorem unitBlockRoot_le (p : GainPartition Unit n) (i : Fin (n+1)) : p.unitBlockRoot i ≤ i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · cases hj : p.code j with
    | none => rw [p.unitBlockRoot_succ_none j hj]; exact Fin.zero_le _
    | some v =>
      rcases v with ⟨r,g⟩
      rw [p.unitBlockRoot_succ_some j r g hj]
      exact Fin.succ_le_succ_iff.mpr (p.least j r g hj)

 theorem unitBlockRoot_idempotent (p : GainPartition Unit n) (i : Fin (n+1)) :
    p.unitBlockRoot (p.unitBlockRoot i)=p.unitBlockRoot i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · cases hj : p.code j with
    | none => rw [p.unitBlockRoot_succ_none j hj,p.unitBlockRoot_zero]
    | some v =>
      rcases v with ⟨r,g⟩
      rw [p.unitBlockRoot_succ_some j r g hj]
      exact p.unitBlockRoot_succ_some r r 1 (p.rooted j r g hj)

def braidLift (p : GainPartition Unit n) (u : Fin (n+1) → G) : GainPartition G (n+1) :=
  fromBlockRoots p.unitBlockRoot p.unitBlockRoot_idempotent p.unitBlockRoot_le u

/-- The full balanced block with prescribed potentials. -/
def braidTop (u : Fin (n+1) → G) : GainPartition G (n+1) :=
  fromBlockRoots (fun _ => 0) (fun _ => rfl) (fun _ => Fin.zero_le _) u

 theorem braidTop_single (u : Fin (n+1) → G) : (braidTop u).SingleBalancedBlock :=
  ⟨0,fun i => ⟨(u 0)⁻¹*u i,rfl⟩⟩

end Dowling.GainPartition
