import MainTheorems.PreorderGamma.Macaulay.FaceCounting

namespace ResearchMain.PreorderGamma.Macaulay

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

noncomputable def canonicalBallotFamily : Finset (Finset (FaceVertex E)) := by
  classical
  exact Finset.univ.filter IsBallotFace

@[simp] theorem mem_canonicalBallotFamily {F : Finset (FaceVertex E)} :
    F ∈ canonicalBallotFamily ↔ IsBallotFace F := by
  classical
  simp [canonicalBallotFamily]

theorem canonicalBallotFamily_downward_closed {F G : Finset (FaceVertex E)}
    (hF : F ∈ canonicalBallotFamily) (hGF : G ⊆ F) : G ∈ canonicalBallotFamily :=
  mem_canonicalBallotFamily.mpr ((mem_canonicalBallotFamily.mp hF).subset hGF)

@[simp] theorem empty_mem_canonicalBallotFamily :
    (∅ : Finset (FaceVertex E)) ∈ canonicalBallotFamily :=
  mem_canonicalBallotFamily.mpr isBallotFace_empty

theorem canonicalBallotFamily_degree_filter (i : ℕ) :
    (canonicalBallotFamily (E := E)).filter (fun F => F.card = i) = ballotFaces i := by
  classical
  ext F
  simp only [Finset.mem_filter, mem_canonicalBallotFamily, mem_ballotFaces]

theorem canonicalBallotFamily_degree_counts (i : ℕ) :
    ((canonicalBallotFamily (E := E)).filter (fun F => F.card = i)).card =
      supportGVector (E := E) i := by
  rw [canonicalBallotFamily_degree_filter, ballotFaces_card_eq_supportGVector]

theorem preorder_g_squarefree_downset :
    ∃ family : Finset (Finset (FaceVertex E)), (∅ : Finset (FaceVertex E)) ∈ family ∧
      (∀ F ∈ family, ∀ G ⊆ F, G ∈ family) ∧
      ∀ i, (family.filter (fun F => F.card = i)).card = supportGVector (E := E) i :=
  ⟨canonicalBallotFamily, empty_mem_canonicalBallotFamily,
    fun _ hF _ hGF => canonicalBallotFamily_downward_closed hF hGF,
    canonicalBallotFamily_degree_counts⟩

end ResearchMain.PreorderGamma.Macaulay
