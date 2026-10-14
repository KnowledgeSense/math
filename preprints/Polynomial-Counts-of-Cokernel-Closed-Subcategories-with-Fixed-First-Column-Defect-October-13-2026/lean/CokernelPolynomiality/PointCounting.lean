import CokernelPolynomiality.FinitePoints

namespace CokernelPolynomiality
noncomputable section

 theorem graphPoints_firstColumn {n : ℕ} (G : SimpleGraph (Fin (n+2))) :
    (graphPoints G).filter (fun p => p.1 = 0) =
      (rootNeighbors G).image (fun v => (0,v.val-1)) := by
  classical
  ext p
  rcases p with ⟨a,b⟩
  constructor
  · intro h
    obtain ⟨hp,ha⟩ := Finset.mem_filter.mp h
    change a = 0 at ha
    subst a
    obtain ⟨_,hbn⟩ := mem_triangle.mp (graphPoints_subset G hp)
    have hg := (mem_graphPoints G (Nat.zero_le _) hbn).mp hp
    exact Finset.mem_image.mpr ⟨⟨b+1,by omega⟩,(mem_rootNeighbors _ _).mpr hg,by simp⟩
  · intro h
    obtain ⟨v,hv,hp⟩ := Finset.mem_image.mp h
    have hg := (mem_rootNeighbors G v).mp hv
    have hpos : 0 < v.val := by
      have hn := hg.ne
      have hv0 : v ≠ 0 := Ne.symm hn
      have : v.val ≠ 0 := fun h => hv0 (Fin.ext h)
      omega
    have hab : (0,v.val-1) = (a,b) := hp
    rw [← hab]
    apply Finset.mem_filter.mpr
    refine ⟨?_,rfl⟩
    apply (mem_graphPoints G (Nat.zero_le _) (by have := v.isLt; omega)).mpr
    convert hg using 1 <;> apply Fin.ext <;> simp [Nat.sub_add_cancel hpos]

 theorem graphPoints_firstColumnSize {n : ℕ} (G : SimpleGraph (Fin (n+2))) :
    firstColumnSize (graphPoints G) = (rootNeighbors G).card := by
  classical
  unfold firstColumnSize
  rw [graphPoints_firstColumn]
  apply Finset.card_image_of_injOn
  intro u hu v hv huv
  have hu' := (mem_rootNeighbors G u).mp hu
  have hv' := (mem_rootNeighbors G v).mp hv
  have up : 0 < u.val := by
    have hn : u.val ≠ 0 := fun h => hu'.ne (Fin.ext h).symm
    omega
  have vp : 0 < v.val := by
    have hn : v.val ≠ 0 := fun h => hv'.ne (Fin.ext h).symm
    omega
  have he : u.val-1 = v.val-1 := congrArg Prod.snd huv
  apply Fin.ext
  omega

 abbrev ClosedPoints (n k : ℕ) :=
  {Y : Finset (ℕ × ℕ) // Y ⊆ triangle n ∧ IsClosed Y ∧ firstColumnSize Y = k}

 abbrev RootedGraphs (N k : ℕ) :=
  {G : SimpleGraph (Fin (N+1)) // Admissible G ∧ (rootNeighbors G).card = k}

 def closedPointEquiv (n k : ℕ) : ClosedPoints n k ≃ RootedGraphs (n+1) k where
  toFun Y := ⟨boundedPointGraph n Y.val, boundedPointGraph_admissible Y.property.2.1, by
    have h := graphPoints_firstColumnSize (boundedPointGraph n Y.val)
    rw [graphPoints_boundedPointGraph Y.val Y.property.1] at h
    exact h.symm.trans Y.property.2.2⟩
  invFun G := ⟨graphPoints G.val,graphPoints_subset _,graphPoints_closed _ G.property.1,
    (graphPoints_firstColumnSize G.val).trans G.property.2⟩
  left_inv Y := Subtype.ext (graphPoints_boundedPointGraph Y.val Y.property.1)
  right_inv G := Subtype.ext (boundedPointGraph_graphPoints G.val)

 def graphModelEquiv (i m : ℕ) : GraphModel i m ≃ RootedGraphs (i+m) m where
  toFun G := ⟨G.graph,G.admissible,G.neighbors_card⟩
  invFun G := ⟨G.val,G.property.1,G.property.2⟩
  left_inv _G := rfl
  right_inv _G := rfl

 theorem r_eq_card_closedPoints (n k : ℕ) : r n k = Nat.card (ClosedPoints n k) := by
  classical
  let S := (triangle n).powerset.filter (fun Y => IsClosed Y ∧ firstColumnSize Y = k)
  have hS : ∀ Y, Y ∈ S ↔ Y ⊆ triangle n ∧ IsClosed Y ∧ firstColumnSize Y = k := by
    intro Y
    simp only [S,Finset.mem_filter,Finset.mem_powerset]
  let e : {Y // Y ∈ S} ≃ ClosedPoints n k :=
    { toFun := fun Y => ⟨Y.val,(hS Y.val).mp Y.property⟩
      invFun := fun Y => ⟨Y.val,(hS Y.val).mpr Y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change S.card = _
  rw [← Nat.card_congr e,Nat.card_eq_fintype_card]
  exact (Fintype.card_coe S).symm

 theorem r_binomial_formula (n i m : ℕ) (h : n+1 = i+m) :
    r n m = ∑ q : Fin (2*i+1), templateCount i q * m.choose q := by
  rw [r_eq_card_closedPoints,Nat.card_congr (closedPointEquiv n m),h,
    ← Nat.card_congr (graphModelEquiv i m),Nat.card_eq_fintype_card]
  exact graphModel_card_formula i m

end
end CokernelPolynomiality
