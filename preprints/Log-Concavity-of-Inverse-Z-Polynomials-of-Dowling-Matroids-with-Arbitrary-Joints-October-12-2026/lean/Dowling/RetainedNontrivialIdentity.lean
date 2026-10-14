import Dowling.JointDelta

noncomputable section
namespace Dowling
open Finset Polynomial
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] [Nontrivial G] {n : ℕ}

/-- Each added retained joint has the same genuine inverse-Z increment. -/
theorem retained_nontrivial_from_empty (hn : 2≤n) (S : Finset (Fin n)) :
    configurationY (G := G) (S : Set (Fin n))=
      configurationY (G := G) (∅ : Set (Fin n))+C (S.card : ℤ)*jointDelta G n := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have h := joint_deletion_nontrivial (G := G) hn i
      (show i∈(↑(insert i S) : Set (Fin n)) from by simp)
    have he : (↑(insert i S) : Set (Fin n))\{i}=(S : Set (Fin n)) := by
      ext j
      simp only [Set.mem_sdiff,Finset.mem_coe,Finset.mem_insert,Set.mem_singleton_iff]
      constructor
      · rintro ⟨h,hji⟩
        exact h.resolve_left hji
      · intro hj
        exact ⟨Or.inr hj,fun hji => hi (hji ▸ hj)⟩
    rw [he,ih] at h
    rw [h,Finset.card_insert_of_notMem hi]
    simp only [Nat.cast_add,Nat.cast_one,map_add,map_one]
    ring

/-- Full and jointless endpoints determine every actual retained subset. -/
theorem retained_nontrivial_identity (hn : 2≤n) (X : Set (Fin n)) :
    configurationY (G := G) X=fullY G n-C ((n-X.toFinset.card : ℕ) : ℤ)*jointDelta G n := by
  have hX := retained_nontrivial_from_empty (G := G) hn X.toFinset
  have hU := retained_nontrivial_from_empty (G := G) hn (univ : Finset (Fin n))
  simp only [Set.coe_toFinset] at hX
  simp only [Finset.coe_univ,Finset.card_univ,Fintype.card_fin] at hU
  change fullY G n=_ at hU
  have hcard : X.toFinset.card≤n := by simpa using Finset.card_le_univ X.toFinset
  rw [hX,hU,Nat.cast_sub hcard]
  simp only [map_sub]
  ring

theorem jointless_nontrivial_identity (hn : 2≤n) :
    configurationY (G := G) (∅ : Set (Fin n))=fullY G n-C (n : ℤ)*jointDelta G n := by
  simpa using retained_nontrivial_identity (G := G) hn (∅ : Set (Fin n))

end Dowling
