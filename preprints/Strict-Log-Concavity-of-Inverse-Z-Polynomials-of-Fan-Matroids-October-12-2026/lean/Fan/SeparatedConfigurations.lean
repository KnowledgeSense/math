import Fan.FiniteSplit
import Fan.ConfigurationInvariant

namespace Fan

noncomputable def joinPair {m n : ℕ} (p : Pair m) (q : Pair n) : Pair (m+n) :=
  (joinSets p.1 q.1,joinSets p.2 q.2)

/-- A missing join separates the lower interval precisely when the two boundary
spokes are not both selected. -/
def Compatible {m n : ℕ} (p : Pair m) (q : Pair n) : Prop :=
  ∀ i : Fin m, ∀ j : Fin n, i.val+1=m → j.val=0 → ¬(i∈p.1 ∧ j∈q.1)

theorem compatible_mono {m n : ℕ} {p p' : Pair m} {q q' : Pair n}
    (hc : Compatible p q) (hp : p' ≤ p) (hq : q' ≤ q) : Compatible p' q' := by
  intro i j hi hj ⟨hpi,hqj⟩
  exact hc i j hi hj ⟨hp.1 hpi,hq.1 hqj⟩

theorem valid_joinPair {m n : ℕ} {p : Pair m} {q : Pair n}
    (hp : Valid p) (hq : Valid q) (hc : Compatible p q) : Valid (joinPair p q) := by
  constructor
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro i hi
      exact hp.1 i ((mem_join_left p.2 q.2 i).mp hi)
    · intro i hi
      have hpos := hq.1 i ((mem_join_right p.2 q.2 i).mp hi)
      change 0<m+i.val
      omega
  · intro i j
    refine Fin.addCases ?_ ?_ i
    · intro a
      refine Fin.addCases ?_ ?_ j
      · intro b hab
        have hab' : a.val+1=b.val := hab
        simpa only [joinPair,mem_join_left] using hp.2 a b hab'
      · intro b hab
        have hav := a.isLt
        have he : a.val+1=m ∧ b.val=0 := by
          change a.val+1=m+b.val at hab
          omega
        have hb : b∉q.2 := fun hb => by have := hq.1 b hb; omega
        change (b.natAdd m∈joinSets p.2 q.2 →
          (a.castAdd n∈joinSets p.1 q.1 ↔ b.natAdd m∈joinSets p.1 q.1)) ∧
          (a.castAdd n∈joinSets p.1 q.1 → b.natAdd m∈joinSets p.1 q.1 →
            b.natAdd m∈joinSets p.2 q.2)
        simp only [mem_join_left,mem_join_right,hb,false_implies,true_and]
        exact fun ha hb => hc a b he.1 he.2 ⟨ha,hb⟩
    · intro a
      refine Fin.addCases ?_ ?_ j
      · intro b hab
        have hb := b.isLt
        change m+a.val+1=b.val at hab
        omega
      · intro b hab
        have hab' : a.val+1=b.val := by
          change m+a.val+1=m+b.val at hab
          omega
        simpa only [joinPair,mem_join_right] using hq.2 a b hab'

theorem joinPair_le_iff {m n : ℕ} (p p' : Pair m) (q q' : Pair n) :
    joinPair p q ≤ joinPair p' q' ↔ p ≤ p' ∧ q ≤ q' := by
  change (joinSets p.1 q.1 ⊆ joinSets p'.1 q'.1 ∧
    joinSets p.2 q.2 ⊆ joinSets p'.2 q'.2) ↔ (p.1⊆p'.1 ∧ p.2⊆p'.2) ∧
    (q.1⊆q'.1 ∧ q.2⊆q'.2)
  rw [joinSets_subset_iff,joinSets_subset_iff]
  tauto

noncomputable def leftPair {m n : ℕ} (p : Pair (m+n)) : Pair m :=
  (leftSet p.1,leftSet p.2)
noncomputable def rightPair {m n : ℕ} (p : Pair (m+n)) : Pair n :=
  (rightSet p.1,rightSet p.2)

@[simp] theorem leftPair_join {m n : ℕ} (p : Pair m) (q : Pair n) :
    leftPair (joinPair p q)=p := by simp [leftPair,joinPair]
@[simp] theorem rightPair_join {m n : ℕ} (p : Pair m) (q : Pair n) :
    rightPair (joinPair p q)=q := by simp [rightPair,joinPair]

theorem joinPair_left_right {m n : ℕ} (p : Pair (m+n)) :
    joinPair (leftPair p) (rightPair p)=p := by
  apply Prod.ext <;> exact joinSets_left_right _

theorem Valid.left_valid {m n : ℕ} {p : Pair (m+n)} (hp : Valid p) : Valid (leftPair p) := by
  constructor
  · intro i hi
    exact hp.1 (i.castAdd n) ((mem_leftSet p.2 i).mp hi)
  · intro i j hij
    simpa only [leftPair,mem_leftSet] using hp.2 (i.castAdd n) (j.castAdd n) hij

/-- On the right block, the missing boundary join is needed to exclude an
extraneous join at index zero. -/
theorem Valid.right_valid {m n : ℕ} {p : Pair (m+n)} (hp : Valid p)
    (hgap : ∀ j : Fin n, j.val=0 → j.natAdd m∉p.2) : Valid (rightPair p) := by
  constructor
  · intro j hj
    have hj' := (mem_rightSet p.2 j).mp hj
    by_contra hn
    exact hgap j (by omega) hj'
  · intro i j hij
    have he : (i.natAdd m).val+1=(j.natAdd m).val := by
      simp only [Fin.val_natAdd]
      omega
    simpa only [rightPair,mem_rightSet] using hp.2 (i.natAdd m) (j.natAdd m) he

theorem Valid.compatible_split {m n : ℕ} {p : Pair (m+n)} (hp : Valid p)
    (hgap : ∀ j : Fin n, j.val=0 → j.natAdd m∉p.2) :
    Compatible (leftPair p) (rightPair p) := by
  intro i j hi hj ⟨hsi,hsj⟩
  apply hgap j hj
  have he : (i.castAdd n).val+1=(j.natAdd m).val := by
    simp only [Fin.val_castAdd,Fin.val_natAdd]
    omega
  exact (hp.2 _ _ he).2 ((mem_leftSet p.1 i).mp hsi) ((mem_rightSet p.1 j).mp hsj)

theorem joinPair_rank {m n : ℕ} (p : Configuration m) (q : Configuration n)
    (hc : Compatible p.val q.val) :
    configurationRank ⟨joinPair p.val q.val,valid_joinPair p.property q.property hc⟩ =
      configurationRank p+configurationRank q := by
  unfold configurationRank
  change (joinSets p.val.1 q.val.1 ∪ joinSets p.val.2 q.val.2).card=_
  rw [joinSets_union,joinSets_card]

end Fan
