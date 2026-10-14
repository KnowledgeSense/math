import Dowling.ZeroBlockUpperIntervals
import Mathlib.Combinatorics.Matroid.Minor.Delete

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

def jointPartition (i : Fin n) : GainPartition G n := GainPartition.discrete.eraseBlock i

omit [Fintype G] in
theorem jointPartition_code (i j : Fin n) :
    (jointPartition (G := G) i).code j=if j=i then none else some (j,1) := rfl

omit [Fintype G] in
theorem jointPartition_admissible {X : Set (Fin n)} (i : Fin n) (hi : i∈X) :
    Admissible X (jointPartition (G := G) i) := by
  intro j _
  exact Or.inl ⟨i,hi,by rw [jointPartition_code]; simp⟩

omit [Fintype G] in
theorem jointPartition_roots_card (i : Fin n) : (jointPartition (G := G) i).roots.card=n-1 := by
  have h := GainPartition.eraseBlock_roots_card (GainPartition.discrete : GainPartition G n) i rfl
  have hd : (GainPartition.discrete : GainPartition G n).roots.card=n := by
    have he : (GainPartition.discrete : GainPartition G n).roots=Finset.univ := by
      ext j
      simp only [GainPartition.roots,Finset.mem_filter,Finset.mem_univ,true_and]
      exact iff_true_intro rfl
    rw [he,Finset.card_univ,Fintype.card_fin]
  rw [hd] at h
  change (jointPartition (G := G) i).roots.card+1=n at h
  omega

def jointConfiguration {X : Set (Fin n)} (i : Fin n) (hi : i∈X) : Configuration G X :=
  ⟨jointPartition i,jointPartition_admissible i hi⟩

omit [Fintype G] in
theorem jointConfiguration_rank {X : Set (Fin n)} (i : Fin n) (hi : i∈X) :
    configurationRank X (jointConfiguration (G := G) i hi)=1 := by
  change n-(jointPartition (G := G) i).roots.card=1
  rw [jointPartition_roots_card]
  have := i.isLt
  omega

/-- Contracting any actually retained joint gives the full-Dowling ranked
interval, independently of all other retained joints and of the gain group. -/
theorem joint_upper_inverseZ {X : Set (Fin n)} (i : Fin n) (hi : i∈X) :
    MatroidInverseZ.inverseZ (configurationRank X) (jointConfiguration (G := G) i hi) ⊤=
      fullY G (n-1) := by
  rw [zeroBlock_upper_inverseZ _ ⟨i,by change (jointPartition i).code i=none; simp [jointPartition_code]⟩]
  exact congrArg (fullY G) (jointPartition_roots_card i)

theorem joint_upper_kl {X : Set (Fin n)} (i : Fin n) (hi : i∈X) :
    MatroidInverseZ.kl (configurationRank X) ⊤ (jointConfiguration (G := G) i hi)=
      fullP G (n-1) := by
  rw [zeroBlock_upper_kl _ ⟨i,by change (jointPartition i).code i=none; simp [jointPartition_code]⟩]
  exact congrArg (fullP G) (jointPartition_roots_card i)

/-- Literal matroid deletion removes exactly the chosen available joint. -/
theorem matroid_delete_joint (X : Set (Fin n)) (i : Fin n) :
    (matroid G n X).delete {Sum.inl i}=matroid G n (X\{i}) := by
  rw [Matroid.delete_eq_restrict,matroid_ground,matroid,Matroid.restrict_restrict_eq _ Set.sdiff_subset]
  change (fullMatroid G n).restrict _=(fullMatroid G n).restrict _
  congr 1
  ext e
  cases e with
  | inl j => simp [ground]
  | inr e => simp [ground]

end Dowling
