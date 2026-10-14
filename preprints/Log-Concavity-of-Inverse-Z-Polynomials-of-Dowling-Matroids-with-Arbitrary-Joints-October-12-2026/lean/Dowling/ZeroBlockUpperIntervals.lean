import Dowling.FullUpperIntervals

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ} {X : Set (Fin n)}

omit [Fintype G] in
theorem admissible_above_nonempty_zero {p q : GainPartition G n}
    (hp : Admissible X p) (hz : ∃ i, p.code i=none) (hpq : p≤q) : Admissible X q := by
  obtain ⟨i,hi⟩ := hz
  intro j _
  rcases hp i hi with ⟨a,haX,ha⟩ | ⟨hG,a,hai,ha⟩
  · exact Or.inl ⟨a,haX,GainPartition.code_none_of_le hpq a ha⟩
  · right
    refine ⟨hG,?_⟩
    by_cases hji : j=i
    · exact ⟨a,by simpa only [hji] using hai,GainPartition.code_none_of_le hpq a ha⟩
    · exact ⟨i,Ne.symm hji,GainPartition.code_none_of_le hpq i hi⟩

/-- Once a genuine zero component is present, every further coarsening is
admissible, including for the trivial gain group. -/
def zeroBlockUpperEmbedding (p : Configuration G X) (hz : ∃ i, p.val.code i=none) :
    Configuration G (Set.univ : Set (Fin p.val.roots.card)) ↪o Configuration G X where
  toFun q := ⟨p.val.compose q.val,
    admissible_above_nonempty_zero p.property hz (p.val.compose_solution_subset q.val)⟩
  inj' := by
    intro q r h
    apply Subtype.ext
    apply le_antisymm
    · exact (p.val.compose_le_compose_iff _ _).mp (congrArg Subtype.val h).le
    · exact (p.val.compose_le_compose_iff _ _).mp (congrArg Subtype.val h).ge
  map_rel_iff' := p.val.compose_le_compose_iff _ _

omit [Fintype G] in
theorem zeroBlockUpperEmbedding_range (p : Configuration G X) (hz : ∃ i, p.val.code i=none)
    (y : Configuration G X) (hy : p≤y) : ∃ q, zeroBlockUpperEmbedding p hz q=y := by
  refine ⟨⟨p.val.compress y.val hy,admissible_univ _⟩,?_⟩
  exact Subtype.ext (p.val.compose_compress y.val hy)

omit [Fintype G] in
theorem zeroBlockUpperEmbedding_interval (p : Configuration G X) (hz : ∃ i, p.val.code i=none) :
    ∀ a b y, zeroBlockUpperEmbedding p hz a≤y → y≤zeroBlockUpperEmbedding p hz b →
      ∃ q, zeroBlockUpperEmbedding p hz q=y := by
  intro a _ y hay _
  apply zeroBlockUpperEmbedding_range
  exact (show p≤zeroBlockUpperEmbedding p hz a from p.val.compose_solution_subset a.val).trans hay

theorem zeroBlockUpperEmbedding_rank (p : Configuration G X) (hz : ∃ i, p.val.code i=none)
    (a b : Configuration G (Set.univ : Set (Fin p.val.roots.card))) :
    configurationRank X (zeroBlockUpperEmbedding p hz b)-
      configurationRank X (zeroBlockUpperEmbedding p hz a)=
      configurationRank Set.univ b-configurationRank Set.univ a :=
  p.val.compose_rank_difference a.val b.val

omit [Fintype G] in
theorem zeroBlockUpperEmbedding_bot (p : Configuration G X) (hz : ∃ i, p.val.code i=none) :
    zeroBlockUpperEmbedding p hz ⊥=p := by
  apply Subtype.ext
  apply GainPartition.solutionSet_injective
  ext x
  change x∈(p.val.compose GainPartition.discrete).solutionSet ↔ x∈p.val.solutionSet
  rw [p.val.mem_compose_solutionSet,GainPartition.discrete_solutionSet]
  simp only [Set.mem_univ,and_true]

theorem zeroBlockUpperEmbedding_top (p : Configuration G X) (hz : ∃ i, p.val.code i=none) :
    zeroBlockUpperEmbedding p hz ⊤=⊤ := by
  apply le_antisymm le_top
  obtain ⟨q,hq⟩ := zeroBlockUpperEmbedding_range p hz ⊤ le_top
  rw [← hq]
  exact (zeroBlockUpperEmbedding p hz).monotone le_top

/-- Every retained-joint flat with nonempty zero block has the full Dowling
contraction on its literal balanced components. -/
theorem zeroBlock_upper_inverseZ (p : Configuration G X) (hz : ∃ i, p.val.code i=none) :
    MatroidInverseZ.inverseZ (configurationRank X) p ⊤=fullY G p.val.roots.card := by
  have h := MatroidInverseZ.inverseZ_interval_transport (zeroBlockUpperEmbedding p hz)
    (zeroBlockUpperEmbedding_interval p hz) (configurationRank Set.univ) (configurationRank X)
    (zeroBlockUpperEmbedding_rank p hz) ⊥ ⊤
  rw [zeroBlockUpperEmbedding_bot,zeroBlockUpperEmbedding_top] at h
  exact h

theorem zeroBlock_upper_kl (p : Configuration G X) (hz : ∃ i, p.val.code i=none) :
    MatroidInverseZ.kl (configurationRank X) ⊤ p=fullP G p.val.roots.card := by
  have h := MatroidInverseZ.kl_interval_transport (zeroBlockUpperEmbedding p hz)
    (zeroBlockUpperEmbedding_interval p hz) (configurationRank Set.univ) (configurationRank X)
    (zeroBlockUpperEmbedding_rank p hz) ⊥ ⊤
  rw [zeroBlockUpperEmbedding_bot,zeroBlockUpperEmbedding_top] at h
  exact h

end Dowling
