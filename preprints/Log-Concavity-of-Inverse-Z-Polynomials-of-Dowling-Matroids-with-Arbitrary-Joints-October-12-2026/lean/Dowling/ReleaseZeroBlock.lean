import Dowling.JointDeletionFlats

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

/-- Release an entire zero block as a balanced identity-gain block. The later
flat correspondence uses this operation only for the order-one gain group. -/
def releaseZeroBlock (p : GainPartition G n) (r : Fin n) (hr : p.code r=none)
    (hmin : ∀ i, p.code i=none → r ≤ i) : GainPartition G n where
  code i := match p.code i with | none => some (r,1) | some v => some v
  rooted := by
    intro i j g hij
    cases hi : p.code i with
    | none =>
      simp only [hi,Option.some.injEq,Prod.mk.injEq] at hij
      obtain ⟨rfl,rfl⟩ := hij
      simp [hr]
    | some v =>
      simp only [hi,Option.some.injEq] at hij
      subst v
      rw [p.rooted i j g hi]
  least := by
    intro i j g hij
    cases hi : p.code i with
    | none =>
      simp only [hi,Option.some.injEq,Prod.mk.injEq] at hij
      rw [← hij.1]
      exact hmin i hi
    | some v =>
      simp only [hi,Option.some.injEq] at hij
      subst v
      exact p.least i j g hi

theorem releaseZeroBlock_code_none (p : GainPartition G n) (r : Fin n) (hr : p.code r=none)
    (hmin : ∀ i, p.code i=none → r ≤ i) (i : Fin n) (hi : p.code i=none) :
    (p.releaseZeroBlock r hr hmin).code i=some (r,1) := by simp [releaseZeroBlock,hi]

theorem releaseZeroBlock_code_some (p : GainPartition G n) (r : Fin n) (hr : p.code r=none)
    (hmin : ∀ i, p.code i=none → r ≤ i) (i s : Fin n) (g : G) (hi : p.code i=some (s,g)) :
    (p.releaseZeroBlock r hr hmin).code i=some (s,g) := by simp [releaseZeroBlock,hi]

theorem releaseZeroBlock_no_zero (p : GainPartition G n) (r : Fin n) (hr : p.code r=none)
    (hmin : ∀ i, p.code i=none → r ≤ i) (i : Fin n) :
    (p.releaseZeroBlock r hr hmin).code i≠none := by
  cases hi : p.code i <;> simp [releaseZeroBlock,hi]

theorem exists_least_zero (p : GainPartition G n) (hz : ∃ i, p.code i=none) :
    ∃ r, p.code r=none ∧ ∀ i, p.code i=none → r ≤ i := by
  let Z := Finset.univ.filter (fun i => p.code i=none)
  have hZ : Z.Nonempty := by obtain ⟨i,hi⟩ := hz; exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  refine ⟨Z.min' hZ,(Finset.mem_filter.mp (Finset.min'_mem Z hZ)).2,?_⟩
  intro i hi
  exact Finset.min'_le Z i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)

end Dowling.GainPartition
