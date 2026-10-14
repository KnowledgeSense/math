import Dowling.JointTau

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

/-- A specified zero set with every outside vertex a singleton balanced block. -/
def zeroSetPartition (Z : Finset (Fin n)) : GainPartition G n where
  code i := if i∈Z then none else some (i,1)
  rooted := by
    intro i j g h
    split at h
    · cases h
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h)
      simp_all
  least := by
    intro i j g h
    split at h
    · cases h
    · have he := congrArg Prod.fst (Option.some.inj h)
      exact le_of_eq he.symm

theorem zeroSetPartition_code (Z : Finset (Fin n)) (i : Fin n) :
    (zeroSetPartition (G := G) Z).code i=if i∈Z then none else some (i,1) := rfl

theorem zeroSetPartition_zero_fiber (Z : Finset (Fin n)) :
    (zeroSetPartition (G := G) Z).fiber none=Z := by
  ext i
  rw [mem_zero_fiber,zeroSetPartition_code]
  by_cases hi : i∈Z <;> simp [hi]

theorem zeroSetPartition_balanced_fiber (Z : Finset (Fin n)) (r : Fin n) :
    (zeroSetPartition (G := G) Z).fiber (some r)=if r∈Z then ∅ else {r} := by
  ext i
  simp only [GainPartition.fiber, GainPartition.blockColor, zeroSetPartition_code]
  by_cases hi : i∈Z <;> by_cases hr : r∈Z <;> simp_all
  · rintro rfl
    exact hr hi
  · rintro rfl
    exact hi hr

theorem zeroSetPartition_singletons (Z : Finset (Fin n)) (r : Fin n) :
    ((zeroSetPartition (G := G) Z).fiber (some r)).card≤1 := by
  rw [zeroSetPartition_balanced_fiber]
  split <;> simp

theorem zeroSetPartition_rank (Z : Finset (Fin n)) :
    partitionRank (zeroSetPartition (G := G) Z)=Z.card := by
  rw [partitionRank_singleton_outside _ (zeroSetPartition_singletons Z),zeroSetPartition_zero_fiber]

theorem zeroSetPartition_roots_card (Z : Finset (Fin n)) :
    (zeroSetPartition (G := G) Z).roots.card=n-Z.card := by
  have h := zeroSetPartition_rank (G := G) Z
  change n-(zeroSetPartition (G := G) Z).roots.card=Z.card at h
  have hr := (zeroSetPartition (G := G) Z).roots_card_le
  omega

theorem zeroSetPartition_admissible_mark (Z : Finset (Fin n)) (X : Set (Fin n))
    (h : ∃ i∈Z, i∈X) : Admissible X (zeroSetPartition (G := G) Z) := by
  obtain ⟨i,hiZ,hiX⟩ := h
  intro j _
  exact Or.inl ⟨i,hiX,by simp [zeroSetPartition_code,hiZ]⟩

/-- Singleton balanced fibers force their potential labels to be the identity,
so no hidden gauge multiplicity survives the tau correction. -/
theorem eq_zeroSetPartition_of_singletons (p : GainPartition G n)
    (hp : ∀ r : Fin n, (p.fiber (some r)).card≤1) : p=zeroSetPartition (p.fiber none) := by
  apply GainPartition.code_injective
  funext i
  rw [zeroSetPartition_code]
  cases hi : p.code i with
  | none =>
    rw [ite_eq_left ((mem_zero_fiber p i).mpr hi)]
  | some v =>
    rcases v with ⟨r,g⟩
    have hni : i∉p.fiber none := by rw [mem_zero_fiber,hi]; simp
    rw [ite_eq_right hni]
    have hif : i∈p.fiber (some r) := by simp [GainPartition.fiber,GainPartition.blockColor,hi]
    have hrf : r∈p.fiber (some r) := by
      simp [GainPartition.fiber,GainPartition.blockColor,p.rooted i r g hi]
    have hir : i=r := Finset.card_le_one.mp (hp r) i hif r hrf
    have he : p.code i=some (i,1) := by
      have hr := p.rooted i r g hi
      simpa only [← hir] using hr
    exact hi.symm.trans he

end Dowling
