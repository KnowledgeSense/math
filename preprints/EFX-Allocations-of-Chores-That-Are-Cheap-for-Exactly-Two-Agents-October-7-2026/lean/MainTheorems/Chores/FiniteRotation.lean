import Mathlib.GroupTheory.Perm.Fin

namespace ResearchMain.Chores

theorem exists_fixed_point_free_permutation (I : Type*) [Fintype I]
    (hn : 2 ≤ Fintype.card I) : ∃ σ : I ≃ I, ∀ i, σ i ≠ i := by
  classical
  let e := Fintype.equivFin I
  let σ := e.trans (finRotate (Fintype.card I)) |>.trans e.symm
  refine ⟨σ, ?_⟩
  intro i hi
  have hrot : finRotate (Fintype.card I) (e i) = e i := by
    have h := congrArg e hi
    simpa only [σ, Equiv.trans_apply, Equiv.apply_symm_apply] using h
  have hmem : e i ∈ (finRotate (Fintype.card I)).support := by
    rw [support_finRotate_of_le hn]
    exact Finset.mem_univ _
  exact (Equiv.Perm.mem_support.mp hmem) hrot

end ResearchMain.Chores
