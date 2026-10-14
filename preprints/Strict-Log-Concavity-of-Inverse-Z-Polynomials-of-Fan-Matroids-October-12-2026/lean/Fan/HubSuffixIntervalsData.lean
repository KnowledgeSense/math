import Fan.ConfigurationCast
import Fan.ExtensionSums

noncomputable section
open scoped Classical
namespace Fan

/-- Appending a full hub run includes the boundary rim exactly when the last
prefix spoke is selected. This is defined for every prefix, including length zero. -/
def hubSuffixRims {m : ℕ} (p : Pair m) (r : ℕ) : Finset (Fin r) :=
  Finset.univ.filter fun j => 0<j.val ∨ ∃ i : Fin m,i.val+1=m ∧ i∈p.1

def glueHubPair {m : ℕ} (p : Pair m) (r : ℕ) : Pair (m+r) :=
  (joinSets p.1 Finset.univ,joinSets p.2 (hubSuffixRims p r))

@[simp] theorem mem_hubSuffixRims {m r : ℕ} (p : Pair m) (j : Fin r) :
    j∈hubSuffixRims p r ↔ 0<j.val ∨ ∃ i : Fin m,i.val+1=m ∧ i∈p.1 := by
  simp [hubSuffixRims]

theorem hubSuffixRims_boundary {m r : ℕ} (p : Pair m) (i : Fin m) (j : Fin r)
    (hi : i.val+1=m) (hj : j.val=0) : j∈hubSuffixRims p r ↔ i∈p.1 := by
  rw [mem_hubSuffixRims]
  constructor
  · rintro (h | ⟨a,ha,hm⟩)
    · omega
    · have he : a=i := Fin.ext (by omega)
      simpa only [he] using hm
  · intro h
    exact Or.inr ⟨i,hi,h⟩

theorem valid_glueHubPair {m : ℕ} (p : Configuration m) (r : ℕ) : Valid (glueHubPair p.val r) := by
  constructor
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro i hi
      exact p.property.1 i ((mem_join_left _ _ i).mp hi)
    · intro i hi
      have hh := (mem_hubSuffixRims p.val i).mp ((mem_join_right _ _ i).mp hi)
      change 0<m+i.val
      rcases hh with hh | ⟨a,ha,_⟩ <;> omega
  · intro i j
    refine Fin.addCases ?_ ?_ i
    · intro a
      refine Fin.addCases ?_ ?_ j
      · intro b hab
        simpa only [glueHubPair,mem_join_left] using p.property.2 a b hab
      · intro b hab
        have ha := a.isLt
        have he : a.val+1=m ∧ b.val=0 := by
          change a.val+1=m+b.val at hab
          omega
        change (b.natAdd m∈joinSets p.val.2 (hubSuffixRims p.val r) →
          (a.castAdd r∈joinSets p.val.1 Finset.univ ↔ b.natAdd m∈joinSets p.val.1 Finset.univ)) ∧
          (a.castAdd r∈joinSets p.val.1 Finset.univ → b.natAdd m∈joinSets p.val.1 Finset.univ →
            b.natAdd m∈joinSets p.val.2 (hubSuffixRims p.val r))
        simp only [mem_join_left,mem_join_right,Finset.mem_univ,iff_true,
          hubSuffixRims_boundary p.val a b he.1 he.2]
        tauto
    · intro a
      refine Fin.addCases ?_ ?_ j
      · intro b hab
        have := b.isLt
        change m+a.val+1=b.val at hab
        omega
      · intro b hab
        have hb : 0<b.val := by change m+a.val+1=m+b.val at hab; omega
        change (b.natAdd m∈joinSets p.val.2 (hubSuffixRims p.val r) →
          (a.natAdd m∈joinSets p.val.1 Finset.univ ↔ b.natAdd m∈joinSets p.val.1 Finset.univ)) ∧
          (a.natAdd m∈joinSets p.val.1 Finset.univ → b.natAdd m∈joinSets p.val.1 Finset.univ →
            b.natAdd m∈joinSets p.val.2 (hubSuffixRims p.val r))
        simp only [mem_join_right,Finset.mem_univ,mem_hubSuffixRims,hb,true_or,
          iff_self,implies_true,and_self]

def glueHubRun {m : ℕ} (p : Configuration m) (r : ℕ) : Configuration (m+r) :=
  ⟨glueHubPair p.val r,valid_glueHubPair p r⟩

@[simp] theorem glueHubRun_left {m : ℕ} (p : Configuration m) (r : ℕ) :
    leftPair (glueHubRun p r).val=p.val := by
  simp only [glueHubRun,glueHubPair,leftPair,leftSet_join]

theorem glueHubRun_le_iff {m : ℕ} (p q : Configuration m) (r : ℕ) :
    glueHubRun p r ≤ glueHubRun q r ↔ p ≤ q := by
  change (joinSets p.val.1 Finset.univ ⊆ joinSets q.val.1 Finset.univ ∧
    joinSets p.val.2 (hubSuffixRims p.val r) ⊆ joinSets q.val.2 (hubSuffixRims q.val r)) ↔ _
  rw [joinSets_subset_iff,joinSets_subset_iff]
  constructor
  · rintro ⟨⟨h1,_⟩,⟨h2,_⟩⟩
    exact ⟨h1,h2⟩
  · intro hpq
    refine ⟨⟨hpq.1,Finset.Subset.refl _⟩,⟨hpq.2,?_⟩⟩
    intro j hj
    rw [mem_hubSuffixRims] at hj ⊢
    rcases hj with hj | ⟨i,hi,hm⟩
    · exact Or.inl hj
    · exact Or.inr ⟨i,hi,hpq.1 hm⟩

theorem glueHubRun_rank {m : ℕ} (p : Configuration m) (r : ℕ) :
    configurationRank (glueHubRun p r)=configurationRank p+r := by
  change (joinSets p.val.1 Finset.univ ∪ joinSets p.val.2 (hubSuffixRims p.val r)).card=_
  rw [joinSets_union,Finset.union_eq_left.mpr (Finset.subset_univ _),
    joinSets_card,Finset.card_univ,Fintype.card_fin]
  rfl

theorem glueHubRun_top (m r : ℕ) : glueHubRun (⊤ : Configuration m) r=⊤ := by
  by_contra h
  have hl : glueHubRun (⊤ : Configuration m) r < ⊤ := lt_of_le_of_ne le_top h
  have hr := configurationRank_strictMono (m+r) hl
  rw [glueHubRun_rank,configuration_top_rank,configuration_top_rank] at hr
  omega

end Fan
