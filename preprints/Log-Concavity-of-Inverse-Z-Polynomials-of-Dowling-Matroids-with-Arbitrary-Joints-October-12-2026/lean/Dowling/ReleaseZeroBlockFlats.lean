import Dowling.ReleaseZeroBlock
import Dowling.FlatCodeLinks

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] [Subsingleton G] {n : ℕ}

theorem releaseZeroBlock_link_iff (p : GainPartition G n) (r : Fin n) (hr : p.code r=none)
    (hmin : ∀ j, p.code j=none → r ≤ j) (X : Set (Fin n)) (e : Link G n) :
    Sum.inr e ∈ flatEdges X (p.releaseZeroBlock r hr hmin) ↔ Sum.inr e ∈ flatEdges X p := by
  let q := p.releaseZeroBlock r hr hmin
  cases ht : p.code e.tail with
  | none =>
    have hqt : q.code e.tail=some (r,1) := p.releaseZeroBlock_code_none r hr hmin _ ht
    cases hh : p.code e.head with
    | none =>
      have hqh : q.code e.head=some (r,1) := p.releaseZeroBlock_code_none r hr hmin _ hh
      rw [flatEdges_link_some_some X q e r r 1 1 hqt hqh]
      have hp : Sum.inr e ∈ flatEdges X p := (flatEdges_link X p e).mpr (Or.inl ⟨ht,hh⟩)
      simp only [hp,and_self,one_mul,Subsingleton.elim e.gain 1]
    | some v =>
      rcases v with ⟨s,b⟩
      have hqh : q.code e.head=some (s,b) := p.releaseZeroBlock_code_some r hr hmin _ _ _ hh
      rw [flatEdges_link_some_some X q e r s 1 b hqt hqh]
      have hsr := p.code_root_ne_zero r hr e.head s b hh
      have hp := flatEdges_link_none_some X p e s b ht hh
      simp [hsr.symm,hp]
  | some v =>
    rcases v with ⟨s,a⟩
    have hqt : q.code e.tail=some (s,a) := p.releaseZeroBlock_code_some r hr hmin _ _ _ ht
    cases hh : p.code e.head with
    | none =>
      have hqh : q.code e.head=some (r,1) := p.releaseZeroBlock_code_none r hr hmin _ hh
      rw [flatEdges_link_some_some X q e s r a 1 hqt hqh]
      have hsr := p.code_root_ne_zero r hr e.tail s a ht
      have hp := flatEdges_link_some_none X p e s a ht hh
      simp [hsr,hp]
    | some v =>
      rcases v with ⟨t,b⟩
      have hqh : q.code e.head=some (t,b) := p.releaseZeroBlock_code_some r hr hmin _ _ _ hh
      rw [flatEdges_link_some_some X q e s t a b hqt hqh,
        flatEdges_link_some_some X p e s t a b ht hh]

/-- With identity gains, a zero block having only the deleted marked vertex
becomes a genuine balanced clique block, rather than staying a zero block. -/
theorem flatEdges_releaseZeroBlock (p : GainPartition G n) (r : Fin n) (hr : p.code r=none)
    (hmin : ∀ j, p.code j=none → r ≤ j) (X : Set (Fin n)) (i : Fin n)
    (hmark : ∀ j∈X, p.code j=none → j=i) :
    flatEdges X (p.releaseZeroBlock r hr hmin)=flatEdges X p\{Sum.inl i} := by
  ext e
  cases e with
  | inl j =>
    rw [flatEdges_joint]
    simp only [p.releaseZeroBlock_no_zero r hr hmin j,and_false,Set.mem_sdiff,
      flatEdges_joint,Set.mem_singleton_iff,Sum.inl.injEq,false_iff,not_and]
    intro h hj
    exact hj (hmark j h.1 h.2)
  | inr e =>
    simp only [Set.mem_sdiff,Set.mem_singleton_iff,Sum.inr_ne_inl,not_false_eq_true,and_true]
    exact releaseZeroBlock_link_iff p r hr hmin X e

end Dowling
