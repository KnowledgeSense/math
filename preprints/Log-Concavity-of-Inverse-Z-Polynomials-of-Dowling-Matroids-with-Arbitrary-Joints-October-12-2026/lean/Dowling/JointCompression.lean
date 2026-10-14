import Dowling.JointFlat
import Dowling.LowerBlockKL

noncomputable section
namespace Dowling
open MatroidInverseZ
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

omit [Fintype G] in
theorem jointPartition_le_iff (i : Fin n) (p : GainPartition G n) :
    jointPartition i≤p ↔ p.code i=none := by
  constructor
  · intro h
    exact GainPartition.code_none_of_le h i (by simp [jointPartition_code])
  · intro hi x hx
    change x∈(GainPartition.discrete.eraseBlock i).solutionSet
    rw [GainPartition.eraseBlock_solutionSet (GainPartition.discrete : GainPartition G n) i rfl,GainPartition.discrete_solutionSet]
    exact ⟨Set.mem_univ _,((p.mem_solutionSet x).mp hx).1 i hi⟩

def jointCompression (p : GainPartition G n) (i : Fin n) (hi : p.code i=none) :
    GainPartition G (jointPartition (G := G) i).roots.card :=
  (jointPartition i).compress p ((jointPartition_le_iff i p).mpr hi)

omit [Fintype G] in
theorem jointCompression_compose (p : GainPartition G n) (i : Fin n) (hi : p.code i=none) :
    (jointPartition i).compose (jointCompression p i hi)=p :=
  (jointPartition i).compose_compress p ((jointPartition_le_iff i p).mpr hi)

theorem jointCompression_roots_card (p : GainPartition G n) (i : Fin n) (hi : p.code i=none) :
    (jointCompression p i hi).roots.card=p.roots.card := by
  rw [← (jointPartition i).compose_roots_card (jointCompression p i hi),jointCompression_compose]

omit [Fintype G] in
theorem jointPartition_isRoot_iff (i j : Fin n) : (jointPartition (G := G) i).IsRoot j ↔ j≠i := by
  change (jointPartition (G := G) i).code j=some (j,1) ↔ _
  rw [jointPartition_code]
  by_cases h : j=i <;> simp [h]

omit [Fintype G] in
theorem joint_rootVertex_ne (i : Fin n) (j : Fin (jointPartition (G := G) i).roots.card) :
    (jointPartition i).rootVertex j≠i :=
  (jointPartition_isRoot_iff i _).mp ((jointPartition i).rootVertex_isRoot j)

omit [Fintype G] in
theorem joint_rootVertex_surjective (i j : Fin n) (hj : j≠i) :
    ∃ c : Fin (jointPartition (G := G) i).roots.card, (jointPartition i).rootVertex c=j := by
  let v : {j // (jointPartition (G := G) i).IsRoot j} := ⟨j,(jointPartition_isRoot_iff i j).mpr hj⟩
  exact ⟨(jointPartition i).rootOrderIso.symm v,
    congrArg Subtype.val ((jointPartition i).rootOrderIso.apply_symm_apply v)⟩

omit [Fintype G] in
theorem jointCompression_code_none_iff (p : GainPartition G n) (i : Fin n) (hi : p.code i=none)
    (j : Fin (jointPartition (G := G) i).roots.card) :
    (jointCompression p i hi).code j=none ↔ p.code ((jointPartition i).rootVertex j)=none := by
  change GainPartition.compressedCode (jointPartition i) p ((jointPartition_le_iff i p).mpr hi) j=none ↔ _
  cases hj : p.code ((jointPartition i).rootVertex j) with
  | none => rw [GainPartition.compressedCode_none _ _ _ j hj]; simp
  | some v =>
    rcases v with ⟨r,g⟩
    rw [GainPartition.compressedCode_some _ _ _ j r g hj]
    simp

theorem configuration_lower_kl (p : Configuration G (Set.univ : Set (Fin n))) :
    kl (configurationRank Set.univ) p ⊥=partitionP p.val := by
  let e := fullPartitionOrderIso (G := G) n
  have h := kl_interval_transport e.toOrderEmbedding
    (fun _ _ y _ _ => ⟨e.symm y,e.apply_symm_apply y⟩)
    partitionRank (configurationRank Set.univ) (fun _ _ => rfl) ⊥ p.val
  change kl (configurationRank Set.univ) (e p.val) (e ⊥)=_ at h
  rw [e.map_bot] at h
  exact h

/-- The actual restriction contracted by its retained joint is evaluated on
the literal compressed gain partition, so its tau coefficient is accessible. -/
theorem joint_restriction_kl {X : Set (Fin n)} (p : Configuration G X)
    (i : Fin n) (hiX : i∈X) (hi : p.val.code i=none) :
    kl (configurationRank X) p (jointConfiguration i hiX)=partitionP (jointCompression p.val i hi) := by
  let a := jointConfiguration (G := G) i hiX
  have hz : ∃ j, a.val.code j=none := ⟨i,by simp [a,jointConfiguration,jointPartition_code]⟩
  let q : Configuration G (Set.univ : Set (Fin a.val.roots.card)) :=
    ⟨jointCompression p.val i hi,admissible_univ _⟩
  have he : zeroBlockUpperEmbedding a hz q=p := Subtype.ext (jointCompression_compose p.val i hi)
  have h := kl_interval_transport (zeroBlockUpperEmbedding a hz) (zeroBlockUpperEmbedding_interval a hz)
    (configurationRank Set.univ) (configurationRank X) (zeroBlockUpperEmbedding_rank a hz) ⊥ q
  rw [he,zeroBlockUpperEmbedding_bot,configuration_lower_kl] at h
  exact h

end Dowling
