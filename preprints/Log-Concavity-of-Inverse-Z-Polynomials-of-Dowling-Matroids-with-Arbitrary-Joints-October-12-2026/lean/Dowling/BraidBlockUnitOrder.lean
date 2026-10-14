import Dowling.BraidBlockRootOrder

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {n : ℕ}

 theorem unitBlockRoot_succ_eq_zero_iff (p : GainPartition Unit n) (i : Fin n) :
    p.unitBlockRoot i.succ=0 ↔ p.code i=none := by
  cases hi : p.code i with
  | none => simp [unitBlockRoot,hi]
  | some v => rcases v with ⟨r,g⟩; simp [unitBlockRoot,hi]

 theorem unitBlockRoot_succ_eq_iff (p : GainPartition Unit n) (i j : Fin n) :
    p.unitBlockRoot i.succ=p.unitBlockRoot j.succ ↔
      (p.code i=none ∧ p.code j=none) ∨
        ∃ r, p.code i=some (r,1) ∧ p.code j=some (r,1) := by
  cases hi : p.code i with
  | none => cases hj : p.code j <;> simp [unitBlockRoot,hi,hj,eq_comm]
  | some v =>
    rcases v with ⟨r,g⟩
    cases g
    cases hj : p.code j with
    | none => simp [unitBlockRoot,hi,hj]
    | some w =>
      rcases w with ⟨s,h⟩
      cases h
      simp [unitBlockRoot,hi,hj,eq_comm]

 theorem unitBlockRoot_eq_iff_solution (p : GainPartition Unit n) (i j : Fin n) :
    p.unitBlockRoot i.succ=p.unitBlockRoot j.succ ↔
      ∀ x ∈ p.solutionSet, x i=x j := by
  rw [unitBlockRoot_succ_eq_iff]
  have h := p.solution_link_iff i j 1
  simp only [gainAct_one,mul_one] at h
  have he : (∃ r a b, p.code i=some (r,a) ∧ p.code j=some (r,b) ∧ True) ↔
      ∃ r, p.code i=some (r,1) ∧ p.code j=some (r,1) := by
    constructor
    · rintro ⟨r,a,b,hi,hj,_⟩
      cases a
      cases b
      exact ⟨r,hi,hj⟩
    · rintro ⟨r,hi,hj⟩
      exact ⟨r,1,1,hi,hj,True.intro⟩
  rw [he] at h
  simpa only [eq_comm] using h.symm

 theorem unitBlockRoot_refinement_iff (p q : GainPartition Unit n) :
    p ≤ q ↔ ∀ i, q.unitBlockRoot (p.unitBlockRoot i)=q.unitBlockRoot i := by
  constructor
  · intro hpq i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · cases hj : p.code j with
      | none =>
        rw [p.unitBlockRoot_succ_none j hj,q.unitBlockRoot_zero]
        exact (q.unitBlockRoot_succ_eq_zero_iff j).mpr (code_none_of_le hpq j hj) |>.symm
      | some v =>
        rcases v with ⟨r,g⟩
        cases g
        rw [p.unitBlockRoot_succ_some j r () hj]
        apply (q.unitBlockRoot_eq_iff_solution r j).mpr
        intro x hx
        have he := ((p.mem_solutionSet x).mp (hpq hx)).2 j r () hj
        simpa only [show (() : Unit)=1 from rfl,gainAct_one] using he.symm
  · intro h x hx
    apply (p.mem_solutionSet x).mpr
    constructor
    · intro i hi
      have he := h i.succ
      rw [p.unitBlockRoot_succ_none i hi,q.unitBlockRoot_zero] at he
      have hq := (q.unitBlockRoot_succ_eq_zero_iff i).mp he.symm
      exact ((q.mem_solutionSet x).mp hx).1 i hq
    · intro i r g hi
      cases g
      have he := h i.succ
      rw [p.unitBlockRoot_succ_some i r () hi] at he
      have hrel := (q.unitBlockRoot_eq_iff_solution r i).mp he x hx
      simpa only [show (() : Unit)=1 from rfl,gainAct_one] using hrel.symm

 theorem braidLift_le_iff {G : Type*} [Group G] (p q : GainPartition Unit n)
    (u : Fin (n+1) → G) : p.braidLift u ≤ q.braidLift u ↔ p ≤ q := by
  rw [braidLift,braidLift,fromBlockRoots_le_iff,unitBlockRoot_refinement_iff]

end Dowling.GainPartition
