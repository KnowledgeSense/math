import Dowling.FlatEdges

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

theorem flatEdges_link_some_some (X : Set (Fin n)) (p : GainPartition G n) (e : Link G n)
    (r s : Fin n) (a b : G) (ht : p.code e.tail=some (r,a)) (hh : p.code e.head=some (s,b)) :
    Sum.inr e ∈ flatEdges X p ↔ r=s ∧ b=a*e.gain := by
  rw [flatEdges_link]
  simp only [ht,hh,Option.some.injEq,Prod.mk.injEq,Option.some_ne_none,false_and,false_or]
  constructor
  · rintro ⟨v,c,d,⟨hr,hca⟩,⟨hs,hdb⟩,hd⟩
    exact ⟨hr.trans hs.symm,by simpa only [← hca,← hdb] using hd⟩
  · rintro ⟨rfl,hb⟩
    exact ⟨r,a,b,⟨rfl,rfl⟩,⟨rfl,rfl⟩,hb⟩

theorem flatEdges_link_none_some (X : Set (Fin n)) (p : GainPartition G n) (e : Link G n)
    (s : Fin n) (b : G) (ht : p.code e.tail=none) (hh : p.code e.head=some (s,b)) :
    Sum.inr e ∉ flatEdges X p := by
  rw [flatEdges_link]
  rintro (⟨_,h⟩ | ⟨r,a,_,h,_⟩)
  · rw [hh] at h; cases h
  · rw [ht] at h; cases h

theorem flatEdges_link_some_none (X : Set (Fin n)) (p : GainPartition G n) (e : Link G n)
    (r : Fin n) (a : G) (ht : p.code e.tail=some (r,a)) (hh : p.code e.head=none) :
    Sum.inr e ∉ flatEdges X p := by
  rw [flatEdges_link]
  rintro (⟨h,_⟩ | ⟨_,_,_,_,h,_⟩)
  · rw [ht] at h; cases h
  · rw [hh] at h; cases h

end Dowling
