import Fan.Configurations
import Mathlib.Order.Fin.Basic

namespace Fan

noncomputable def joinSets {m n : ℕ} (S : Finset (Fin m)) (T : Finset (Fin n)) :
    Finset (Fin (m+n)) :=
  S.map (Fin.castAddOrderEmb n).toEmbedding ∪ T.map (Fin.natAddOrderEmb m).toEmbedding

theorem castAdd_ne_natAdd {m n : ℕ} (i : Fin m) (j : Fin n) : i.castAdd n ≠ j.natAdd m := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  have := i.isLt
  omega

@[simp] theorem mem_join_left {m n : ℕ} (S : Finset (Fin m)) (T : Finset (Fin n)) (i : Fin m) :
    i.castAdd n ∈ joinSets S T ↔ i∈S := by
  classical
  simp only [joinSets,Finset.mem_union,Finset.mem_map]
  constructor
  · rintro (⟨j,hj,he⟩ | ⟨j,_,he⟩)
    · have hij : j=i := (Fin.castAddOrderEmb n).injective he
      simpa only [hij] using hj
    · exact False.elim (castAdd_ne_natAdd i j he.symm)
  · intro hi
    exact Or.inl ⟨i,hi,rfl⟩

@[simp] theorem mem_join_right {m n : ℕ} (S : Finset (Fin m)) (T : Finset (Fin n)) (j : Fin n) :
    j.natAdd m ∈ joinSets S T ↔ j∈T := by
  classical
  simp only [joinSets,Finset.mem_union,Finset.mem_map]
  constructor
  · rintro (⟨i,_,he⟩ | ⟨i,hi,he⟩)
    · exact False.elim (castAdd_ne_natAdd i j he)
    · have hij : i=j := (Fin.natAddOrderEmb m).injective he
      simpa only [hij] using hi
  · intro hj
    exact Or.inr ⟨j,hj,rfl⟩

theorem joinSets_card {m n : ℕ} (S : Finset (Fin m)) (T : Finset (Fin n)) :
    (joinSets S T).card=S.card+T.card := by
  classical
  unfold joinSets
  rw [Finset.card_union_of_disjoint,Finset.card_map,Finset.card_map]
  apply Finset.disjoint_left.mpr
  intro k hk1 hk2
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hk1
  obtain ⟨j,_,he⟩ := Finset.mem_map.mp hk2
  exact castAdd_ne_natAdd i j he.symm

theorem joinSets_subset_iff {m n : ℕ} (S S' : Finset (Fin m)) (T T' : Finset (Fin n)) :
    joinSets S T ⊆ joinSets S' T' ↔ S⊆S' ∧ T⊆T' := by
  constructor
  · intro h
    constructor
    · intro i hi
      exact (mem_join_left S' T' i).mp (h ((mem_join_left S T i).mpr hi))
    · intro j hj
      exact (mem_join_right S' T' j).mp (h ((mem_join_right S T j).mpr hj))
  · rintro ⟨hS,hT⟩ k
    refine Fin.addCases ?_ ?_ k
    · intro i hi
      exact (mem_join_left S' T' i).mpr (hS ((mem_join_left S T i).mp hi))
    · intro j hj
      exact (mem_join_right S' T' j).mpr (hT ((mem_join_right S T j).mp hj))

theorem joinSets_union {m n : ℕ} (S S' : Finset (Fin m)) (T T' : Finset (Fin n)) :
    joinSets S T ∪ joinSets S' T'=joinSets (S∪S') (T∪T') := by
  classical
  ext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    simp only [Finset.mem_union,mem_join_left]
  · intro j
    simp only [Finset.mem_union,mem_join_right]

noncomputable def leftSet {m n : ℕ} (S : Finset (Fin (m+n))) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i => i.castAdd n∈S
noncomputable def rightSet {m n : ℕ} (S : Finset (Fin (m+n))) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j => j.natAdd m∈S

@[simp] theorem mem_leftSet {m n : ℕ} (S : Finset (Fin (m+n))) (i : Fin m) :
    i∈leftSet S ↔ i.castAdd n∈S := by classical simp [leftSet]
@[simp] theorem mem_rightSet {m n : ℕ} (S : Finset (Fin (m+n))) (j : Fin n) :
    j∈rightSet S ↔ j.natAdd m∈S := by classical simp [rightSet]

theorem joinSets_left_right {m n : ℕ} (S : Finset (Fin (m+n))) :
    joinSets (leftSet S) (rightSet S)=S := by
  ext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    simp only [mem_join_left,mem_leftSet]
  · intro j
    simp only [mem_join_right,mem_rightSet]

@[simp] theorem leftSet_join {m n : ℕ} (S : Finset (Fin m)) (T : Finset (Fin n)) :
    leftSet (joinSets S T)=S := by ext i; simp only [mem_leftSet,mem_join_left]
@[simp] theorem rightSet_join {m n : ℕ} (S : Finset (Fin m)) (T : Finset (Fin n)) :
    rightSet (joinSets S T)=T := by ext i; simp only [mem_rightSet,mem_join_right]

end Fan
