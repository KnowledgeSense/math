import Dowling.JointFlat

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

def releaseSingleton (p : GainPartition G n) (i : Fin n) (hi : p.code i=none) : GainPartition G n where
  code j := if j=i then some (j,1) else p.code j
  rooted := by
    intro j r g h
    by_cases hj : j=i
    · simp only [hj,ite_true,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      simp
    · simp only [hj,ite_false] at h
      have hr : r≠i := by
        intro he
        have hh := p.rooted j r g h
        rw [he,hi] at hh
        cases hh
      simp only [hr,ite_false]
      exact p.rooted j r g h
  least := by
    intro j r g h
    by_cases hj : j=i
    · simp only [hj,ite_true,Option.some.injEq,Prod.mk.injEq] at h
      exact le_of_eq (h.1.symm.trans hj.symm)
    · simp only [hj,ite_false] at h
      exact p.least j r g h

theorem releaseSingleton_code (p : GainPartition G n) (i : Fin n) (hi : p.code i=none) (j : Fin n) :
    (p.releaseSingleton i hi).code j=if j=i then some (j,1) else p.code j := rfl

theorem releaseSingleton_no_zero (p : GainPartition G n) (i : Fin n) (hi : p.code i=none)
    (hz : ∀ j, p.code j=none → j=i) (j : Fin n) : (p.releaseSingleton i hi).code j≠none := by
  rw [releaseSingleton_code]
  split
  · simp
  · intro h
    exact ‹j≠i› (hz j h)

theorem releaseSingleton_admissible (p : GainPartition G n) (i : Fin n) (hi : p.code i=none)
    (hz : ∀ j, p.code j=none → j=i) (X : Set (Fin n)) : Admissible X (p.releaseSingleton i hi) :=
  fun j hj => False.elim (p.releaseSingleton_no_zero i hi hz j hj)

theorem code_root_ne_zero (p : GainPartition G n) (i : Fin n) (hi : p.code i=none)
    (j r : Fin n) (g : G) (hj : p.code j=some (r,g)) : r≠i := by
  intro hri
  have hr := p.rooted j r g hj
  rw [hri,hi] at hr
  cases hr

end Dowling.GainPartition
end
