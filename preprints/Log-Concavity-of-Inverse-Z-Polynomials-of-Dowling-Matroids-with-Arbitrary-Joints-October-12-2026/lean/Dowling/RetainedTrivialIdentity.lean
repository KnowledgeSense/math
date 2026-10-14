import Dowling.JointTrivialDelta

noncomputable section
namespace Dowling
open Finset Polynomial
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] [Subsingleton G] {n : ℕ}

/-- Delete missing joints one at a time while keeping one genuine joint.
Pascal's identity sums the extra order-one correction exactly. -/
theorem retained_trivial_complement (S : Finset (Fin n)) (hS : S≠univ) :
    configurationY (G := G) (S : Set (Fin n))ᶜ=
      fullY G n-C (S.card : ℤ)*jointDelta G n-missingJointCorrection G n S.card := by
  revert hS
  induction S using Finset.induction_on with
  | empty =>
    intro _
    simp [missingJointCorrection_zero,fullY]
  | @insert i S hi ih =>
    intro hS
    have hproper : S≠univ := by
      intro he
      apply hS
      simp [he]
    have hrec := ih hproper
    have hex : ∃ j : Fin n,j∉insert i S := by
      by_contra h
      apply hS
      ext j
      simp only [Finset.mem_univ,iff_true]
      by_contra hj
      exact h ⟨j,hj⟩
    obtain ⟨j,hj⟩ := hex
    have hiX : i∈(S : Set (Fin n))ᶜ := by simpa using hi
    have hjX : j∈(S : Set (Fin n))ᶜ := by
      intro h
      exact hj (Finset.mem_insert_of_mem h)
    have hji : j≠i := fun h => hj (h ▸ Finset.mem_insert_self i S)
    have h := joint_deletion_trivial (G := G) i hiX ⟨j,hjX,hji⟩
    have he : (S : Set (Fin n))ᶜ\{i}=(↑(insert i S) : Set (Fin n))ᶜ := by
      ext a
      simp only [Set.mem_sdiff,Set.mem_compl_iff,Finset.mem_coe,Finset.mem_insert,Set.mem_singleton_iff]
      tauto
    let : DecidablePred (fun a : Fin n => a∈(S : Set (Fin n))ᶜ) := fun _ => Classical.propDecidable _
    have hc : n-((S : Set (Fin n))ᶜ).toFinset.card=S.card := by
      have hle : S.card≤n := by simpa using Finset.card_le_univ S
      have heq : ((S : Set (Fin n))ᶜ).toFinset=univ\S := by ext a; simp
      rw [heq,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin]
      omega
    rw [he] at h
    simp only [hc] at h
    rw [hrec] at h
    rw [Finset.card_insert_of_notMem hi,missingJointCorrection_succ]
    simp only [Nat.cast_add,Nat.cast_one,map_add,map_one]
    linear_combination -h

/-- Exact original order-one retained-joint formula, for every nonempty
retained set. The jointless rank drop is handled by its separate braid interval. -/
theorem retained_trivial_identity (X : Set (Fin n)) (hX : X.Nonempty) :
    configurationY (G := G) X=fullY G n-C ((n-X.toFinset.card : ℕ) : ℤ)*jointDelta G n-
      missingJointCorrection G n (n-X.toFinset.card) := by
  have hproper : Xᶜ.toFinset≠univ := by
    intro h
    obtain ⟨i,hi⟩ := hX
    have : i∈Xᶜ.toFinset := h ▸ Finset.mem_univ i
    exact (Set.mem_toFinset.mp this) hi
  have h := retained_trivial_complement (G := G) Xᶜ.toFinset hproper
  have hc : Xᶜ.toFinset.card=n-X.toFinset.card := by
    have he : Xᶜ.toFinset=univ\X.toFinset := by ext i; simp
    rw [he,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin]
  simpa only [Set.coe_toFinset,compl_compl,hc] using h

end Dowling
