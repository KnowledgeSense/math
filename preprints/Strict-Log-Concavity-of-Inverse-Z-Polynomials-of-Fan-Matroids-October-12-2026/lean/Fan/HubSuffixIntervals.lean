import Fan.HubSuffixIntervalsData

noncomputable section
open scoped Classical
namespace Fan

theorem full_suffix_rim {m r : ℕ} (z : Configuration (m+r))
    (hz : ∀ j : Fin r,j.natAdd m∈z.val.1) (j : Fin r) :
    j.natAdd m∈z.val.2 ↔ 0<j.val ∨
      ∃ i : Fin m,i.val+1=m ∧ i.castAdd r∈z.val.1 := by
  constructor
  · intro hj
    by_cases hjpos : 0<j.val
    · exact Or.inl hjpos
    · have hj0 : j.val=0 := by omega
      have hm : 0<m := by have := z.property.1 (j.natAdd m) hj; simp only [Fin.val_natAdd] at this; omega
      let i : Fin m := ⟨m-1,by omega⟩
      have he : (i.castAdd r).val+1=(j.natAdd m).val := by
        simp only [Fin.val_castAdd,Fin.val_natAdd]
        dsimp [i]
        omega
      have hi := ((z.property.2 _ _ he).1 hj).mpr (hz j)
      exact Or.inr ⟨i,by dsimp [i]; omega,hi⟩
  · intro hj
    by_cases hjpos : 0<j.val
    · let i : Fin r := ⟨j.val-1,by have := j.isLt; omega⟩
      have he : (i.natAdd m).val+1=(j.natAdd m).val := by
        simp only [Fin.val_natAdd]
        dsimp [i]
        omega
      exact (z.property.2 _ _ he).2 (hz i) (hz j)
    · obtain h | ⟨i,hi,his⟩ := hj
      · omega
      · have he : (i.castAdd r).val+1=(j.natAdd m).val := by
          simp only [Fin.val_castAdd,Fin.val_natAdd]
          omega
        exact (z.property.2 _ _ he).2 his (hz j)

def hubPrefix {m r : ℕ} (z : Configuration (m+r)) : Configuration m :=
  ⟨leftPair z.val,z.property.left_valid⟩

theorem glueHubRun_reconstruct {m r : ℕ} (z : Configuration (m+r))
    (hz : ∀ j : Fin r,j.natAdd m∈z.val.1) : glueHubRun (hubPrefix z) r=z := by
  apply Subtype.ext
  apply Prod.ext
  · apply Finset.ext
    intro k
    refine Fin.addCases ?_ ?_ k
    · intro i
      change i.castAdd r∈joinSets (leftSet z.val.1) Finset.univ ↔ i.castAdd r∈z.val.1
      rw [mem_join_left,mem_leftSet]
    · intro j
      change j.natAdd m∈joinSets (leftSet z.val.1) Finset.univ ↔ j.natAdd m∈z.val.1
      simp only [mem_join_right,Finset.mem_univ,hz j]
  · apply Finset.ext
    intro k
    refine Fin.addCases ?_ ?_ k
    · intro i
      change i.castAdd r∈joinSets (leftSet z.val.2) (hubSuffixRims (leftPair z.val) r) ↔ i.castAdd r∈z.val.2
      rw [mem_join_left,mem_leftSet]
    · intro j
      change j.natAdd m∈joinSets (leftSet z.val.2) (hubSuffixRims (leftPair z.val) r) ↔ j.natAdd m∈z.val.2
      rw [mem_join_right,mem_hubSuffixRims,full_suffix_rim z hz j]
      simp only [leftPair,mem_leftSet]

def hubRunEmbedding (m r : ℕ) : Configuration m ↪o Configuration (m+r) :=
  OrderEmbedding.ofMapLEIff (fun p => glueHubRun p r) (fun p q => glueHubRun_le_iff p q r)

theorem hubRunEmbedding_fills (m r : ℕ) :
    ∀ a b z,hubRunEmbedding m r a ≤ z → z ≤ hubRunEmbedding m r b →
      ∃ x,hubRunEmbedding m r x=z := by
  intro a _ z ha _
  refine ⟨hubPrefix z,glueHubRun_reconstruct z ?_⟩
  intro j
  have h : (glueHubRun a r).val.1 ⊆ z.val.1 := ha.1
  apply h
  exact (mem_join_right a.val.1 Finset.univ j).mpr (Finset.mem_univ j)

theorem upperMu_glueHubRun {m : ℕ} (p : Configuration m) (r : ℕ) :
    upperMu (glueHubRun p r)=upperMu p := by
  have h := MatroidInverseZ.mu_interval_transport (hubRunEmbedding m r)
    (hubRunEmbedding_fills m r) p ⊤
  change IncidenceAlgebra.mu ℤ (glueHubRun p r) (glueHubRun ⊤ r)=_ at h
  rw [glueHubRun_top] at h
  exact h

theorem top_rim_iff {r : ℕ} (j : Fin r) : j∈(⊤ : Configuration r).val.2 ↔ 0<j.val := by
  constructor
  · exact (⊤ : Configuration r).property.1 j
  · intro hj
    let i : Fin r := ⟨j.val-1,by have := j.isLt; omega⟩
    have he : i.val+1=j.val := by dsimp [i]; omega
    exact ((⊤ : Configuration r).property.2 i j he).2 (top_spoke i) (top_spoke j)

theorem joined_top_eq_glueHubRun {m : ℕ} (p : Configuration m) (hp : EndsNonhub p) (r : ℕ) :
    joinedConfiguration p (⊤ : Configuration r) (hp.compatible _)=glueHubRun p r := by
  have hs : (⊤ : Configuration r).val.1=Finset.univ := by ext j; simp [top_spoke]
  have hn : ¬∃ i : Fin m,i.val+1=m ∧ i∈p.val.1 := by
    rintro ⟨i,hi,hm⟩
    exact hp i hi hm
  have hr : hubSuffixRims p.val r=(⊤ : Configuration r).val.2 := by
    ext j
    rw [mem_hubSuffixRims,top_rim_iff]
    simp only [hn,or_false]
  apply Subtype.ext
  change (joinSets p.val.1 (⊤ : Configuration r).val.1,joinSets p.val.2 (⊤ : Configuration r).val.2)=
    (joinSets p.val.1 Finset.univ,joinSets p.val.2 (hubSuffixRims p.val r))
  rw [hs,hr]

/-- The actual upper Möbius invariant is unchanged by a separated full hub suffix. -/
theorem upperMu_joined_top {m : ℕ} (p : Configuration m) (hp : EndsNonhub p) (r : ℕ) :
    upperMu (joinedConfiguration p (⊤ : Configuration r) (hp.compatible _))=upperMu p := by
  rw [joined_top_eq_glueHubRun p hp r,upperMu_glueHubRun]

end Fan
