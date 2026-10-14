import Dowling.PartitionOrder
import Mathlib.Data.Finset.Sort

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

/-- Increasing coordinates on the actual free component roots. -/
def rootOrderIso (p : GainPartition G n) : Fin p.roots.card ≃o {j // p.IsRoot j} :=
  (p.roots.orderIsoOfFin rfl).trans
    { toFun := fun j => ⟨j.val,(Finset.mem_filter.mp j.property).2⟩
      invFun := fun j => ⟨j.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,j.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }

def rootVertex (p : GainPartition G n) (i : Fin p.roots.card) : Fin n := (p.rootOrderIso i).val

theorem rootVertex_isRoot (p : GainPartition G n) (i : Fin p.roots.card) :
    p.IsRoot (p.rootVertex i) := (p.rootOrderIso i).property

theorem rootVertex_strictMono (p : GainPartition G n) : StrictMono p.rootVertex :=
  fun _ _ h => p.rootOrderIso.strictMono h

/-- Actual root values give independent, numbered coordinates on the solution set. -/
def coordinateEquiv (p : GainPartition G n) : p.solutionSet ≃ (Fin p.roots.card → Option G) :=
  p.solutionEquiv.trans (Equiv.piCongrLeft' (fun _ => Option G) p.rootOrderIso.toEquiv.symm)

@[simp] theorem coordinateEquiv_apply (p : GainPartition G n) (x : p.solutionSet)
    (i : Fin p.roots.card) : p.coordinateEquiv x i = x.val (p.rootVertex i) := rfl

@[simp] theorem coordinateEquiv_symm_root (p : GainPartition G n)
    (a : Fin p.roots.card → Option G) (i : Fin p.roots.card) :
    (p.coordinateEquiv.symm a).val (p.rootVertex i) = a i := by
  exact congrFun (p.coordinateEquiv.apply_symm_apply a) i

end Dowling.GainPartition
