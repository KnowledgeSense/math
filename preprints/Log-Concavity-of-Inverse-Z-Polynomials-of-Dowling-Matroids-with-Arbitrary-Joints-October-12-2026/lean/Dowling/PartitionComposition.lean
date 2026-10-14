import Dowling.RootCoordinates

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

def compositeCode (p : GainPartition G n) (q : GainPartition G p.roots.card)
    (i : Fin n) : Option (Fin n × G) :=
  match hi : p.code i with
  | none => none
  | some (r,g) =>
    (q.code (p.rootOrderIso.symm ⟨r,p.rooted i r g hi⟩)).map
      (fun v => (p.rootVertex v.1,v.2*g))

theorem compositeCode_none (p : GainPartition G n) (q : GainPartition G p.roots.card)
    (i : Fin n) (hi : p.code i = none) : p.compositeCode q i = none := by
  unfold compositeCode
  split <;> simp_all

theorem compositeCode_some (p : GainPartition G n) (q : GainPartition G p.roots.card)
    (i r : Fin n) (g : G) (hi : p.code i = some (r,g)) :
    p.compositeCode q i =
      (q.code (p.rootOrderIso.symm ⟨r,p.rooted i r g hi⟩)).map
        (fun v => (p.rootVertex v.1,v.2*g)) := by
  unfold compositeCode
  split
  · rename_i h
    rw [hi] at h
    cases h
  · rename_i r' g' h
    have he := Option.some.inj (hi.symm.trans h)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    rfl

@[simp] theorem compositeCode_rootVertex (p : GainPartition G n)
    (q : GainPartition G p.roots.card) (i : Fin p.roots.card) :
    p.compositeCode q (p.rootVertex i) = (q.code i).map (fun v => (p.rootVertex v.1,v.2)) := by
  rw [compositeCode_some _ _ _ _ 1 (p.rootVertex_isRoot i)]
  have he : (⟨p.rootVertex i,p.rooted _ _ 1 (p.rootVertex_isRoot i)⟩ : {j // p.IsRoot j}) =
      p.rootOrderIso i := rfl
  rw [he,p.rootOrderIso.symm_apply_apply]
  simp only [mul_one]

/-- Coarsening the free components by a second group partition, with ordered
potentials multiplied in their actual right-action order. -/
def compose (p : GainPartition G n) (q : GainPartition G p.roots.card) : GainPartition G n where
  code := p.compositeCode q
  rooted := by
    intro i j g hij
    cases hi : p.code i with
    | none => rw [p.compositeCode_none q i hi] at hij; cases hij
    | some v =>
      rcases v with ⟨r,a⟩
      rw [p.compositeCode_some q i r a hi] at hij
      cases hq : q.code (p.rootOrderIso.symm ⟨r,p.rooted i r a hi⟩) with
      | none => simp [hq] at hij
      | some v =>
        rcases v with ⟨s,b⟩
        simp only [hq,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hij
        obtain ⟨rfl,rfl⟩ := hij
        rw [compositeCode_rootVertex, q.rooted _ _ _ hq]
        rfl
  least := by
    intro i j g hij
    cases hi : p.code i with
    | none => rw [p.compositeCode_none q i hi] at hij; cases hij
    | some v =>
      rcases v with ⟨r,a⟩
      rw [p.compositeCode_some q i r a hi] at hij
      cases hq : q.code (p.rootOrderIso.symm ⟨r,p.rooted i r a hi⟩) with
      | none => simp [hq] at hij
      | some v =>
        rcases v with ⟨s,b⟩
        simp only [hq,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hij
        obtain ⟨rfl,rfl⟩ := hij
        have hs := p.rootOrderIso.monotone (q.least _ _ _ hq)
        have hs' : p.rootOrderIso s ≤ ⟨r,p.rooted i r a hi⟩ := by
          simpa only [OrderIso.apply_symm_apply] using hs
        have hsr : p.rootVertex s ≤ r := hs'
        exact hsr.trans (p.least i r a hi)

end Dowling.GainPartition
