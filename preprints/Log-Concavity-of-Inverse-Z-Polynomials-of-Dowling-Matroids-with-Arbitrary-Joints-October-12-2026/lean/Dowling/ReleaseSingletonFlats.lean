import Dowling.ReleaseSingleton

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

theorem releaseSingleton_link_iff (p : GainPartition G n) (i : Fin n) (hi : p.code i=none)
    (hz : ∀ j, p.code j=none → j=i) (X : Set (Fin n)) (e : Link G n) :
    Sum.inr e ∈ flatEdges X (p.releaseSingleton i hi) ↔ Sum.inr e ∈ flatEdges X p := by
  rw [flatEdges_link,flatEdges_link]
  have hzero : ¬(p.code e.tail=none ∧ p.code e.head=none) := by
    rintro ⟨ht,hh⟩
    exact e.ordered.ne ((hz _ ht).trans (hz _ hh).symm)
  have hrelease : ¬((p.releaseSingleton i hi).code e.tail=none ∧
      (p.releaseSingleton i hi).code e.head=none) :=
    fun h => p.releaseSingleton_no_zero i hi hz _ h.1
  rw [or_iff_right hzero,or_iff_right hrelease]
  by_cases ht : e.tail=i
  · have hh : e.head≠i := by intro he; exact e.ordered.ne (ht.trans he.symm)
    simp only [p.releaseSingleton_code,ht,hh,ite_true,ite_false,hi,Option.some.injEq,Prod.mk.injEq]
    constructor
    · rintro ⟨r,a,b,⟨hir,_⟩,hr,_⟩
      exact False.elim (p.code_root_ne_zero i hi e.head r b hr hir.symm)
    · rintro ⟨r,a,b,ha,_⟩
      cases ha
  · by_cases hh : e.head=i
    · simp only [p.releaseSingleton_code,ht,hh,ite_true,ite_false,hi,Option.some.injEq,Prod.mk.injEq]
      constructor
      · rintro ⟨r,a,b,hr,⟨hir,_⟩,_⟩
        exact False.elim (p.code_root_ne_zero i hi e.tail r a hr hir.symm)
      · rintro ⟨r,a,b,_,hb,_⟩
        cases hb
    · simp only [p.releaseSingleton_code,ht,hh,ite_false]

theorem flatEdges_releaseSingleton (p : GainPartition G n) (i : Fin n) (hi : p.code i=none)
    (hz : ∀ j, p.code j=none → j=i) (X : Set (Fin n)) :
    flatEdges X (p.releaseSingleton i hi)=flatEdges X p\{Sum.inl i} := by
  ext e
  cases e with
  | inl j =>
    rw [flatEdges_joint]
    simp only [p.releaseSingleton_no_zero i hi hz j,and_false,Set.mem_sdiff,
      flatEdges_joint,Set.mem_singleton_iff,Sum.inl.injEq,false_iff,not_and]
    intro h hj
    exact hj (hz j h.2)
  | inr e =>
    simp only [Set.mem_sdiff,Set.mem_singleton_iff,Sum.inr_ne_inl,not_false_eq_true,and_true]
    exact releaseSingleton_link_iff p i hi hz X e

end Dowling
