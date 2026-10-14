import MainTheorems.PreorderGamma.Macaulay.CanonicalMatchings
import MainTheorems.PreorderGamma.Macaulay.BallotSets
import Mathlib.Data.Finset.Sum

namespace ResearchMain.PreorderGamma.Macaulay

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

def occupiedVertices (M : Finset (E × E)) : Finset E := leftSupport M ∪ rightSupport M

def freeVertices (M : Finset (E × E)) : Finset E := Finset.univ \ occupiedVertices M

omit [Fintype E] [Preorder E] in
theorem occupiedVertices_mono {M N : Finset (E × E)} (h : N ⊆ M) :
    occupiedVertices N ⊆ occupiedVertices M :=
  Finset.union_subset_union (leftSupport_mono h) (rightSupport_mono h)

omit [Preorder E] in
theorem freeVertices_antitone {M N : Finset (E × E)} (h : N ⊆ M) :
    freeVertices M ⊆ freeVertices N :=
  Finset.sdiff_subset_sdiff_right Finset.univ (occupiedVertices_mono h)

omit [Fintype E] in
theorem IsOrderMatching.card_occupiedVertices {M : Finset (E × E)}
    (hM : IsOrderMatching M) : (occupiedVertices M).card = 2 * M.card := by
  rw [occupiedVertices, Finset.card_union_of_disjoint hM.disjoint,
    hM.card_leftSupport, hM.card_rightSupport]
  omega

theorem IsOrderMatching.card_freeVertices_add {M : Finset (E × E)}
    (hM : IsOrderMatching M) : (freeVertices M).card + 2 * M.card = Fintype.card E := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (occupiedVertices M))
  simpa only [freeVertices, hM.card_occupiedVertices, Finset.card_univ] using h

theorem IsOrderMatching.card_freeVertices {M : Finset (E × E)}
    (hM : IsOrderMatching M) : (freeVertices M).card = Fintype.card E - 2 * M.card := by
  have h := hM.card_freeVertices_add
  omega

abbrev FaceVertex (E : Type*) := (E × E) ⊕ E

def IsBallotFace (F : Finset (FaceVertex E)) : Prop :=
  IsCanonicalMatching F.toLeft ∧ IsBallotWithin vertexIndex (freeVertices F.toLeft) F.toRight

theorem IsBallotFace.subset {F G : Finset (FaceVertex E)}
    (hF : IsBallotFace F) (hGF : G ⊆ F) : IsBallotFace G := by
  have hl := Finset.toLeft_subset_toLeft hGF
  have hr := Finset.toRight_subset_toRight hGF
  exact ⟨canonical_matching_subset hF.1 hl,
    (hF.2.subset hr).enlarge (freeVertices_antitone hl)⟩

@[simp] theorem isBallotFace_empty : IsBallotFace (∅ : Finset (FaceVertex E)) := by
  change IsCanonicalMatching ∅ ∧ IsBallotWithin vertexIndex (freeVertices ∅) ∅
  exact ⟨canonical_matching_empty, isBallotWithin_empty _ _⟩

theorem IsBallotFace.card_bound {F : Finset (FaceVertex E)}
    (hF : IsBallotFace F) : F.card ≤ Fintype.card E / 2 := by
  have hf := hF.1.1.card_freeVertices_add
  have ha := hF.2.card_bound
  have hc := Finset.card_toLeft_add_card_toRight (u := F)
  omega

noncomputable def ballotFaces (i : ℕ) : Finset (Finset (FaceVertex E)) := by
  classical
  exact Finset.univ.filter fun F => IsBallotFace F ∧ F.card = i

@[simp] theorem mem_ballotFaces {i : ℕ} {F : Finset (FaceVertex E)} :
    F ∈ ballotFaces i ↔ IsBallotFace F ∧ F.card = i := by
  classical
  simp [ballotFaces]

theorem ballotFaces_empty_of_large (i : ℕ) (hi : Fintype.card E / 2 < i) :
    ballotFaces (E := E) i = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro F hf
  obtain ⟨hF, hc⟩ := mem_ballotFaces.mp hf
  have hb := hF.card_bound
  omega

end ResearchMain.PreorderGamma.Macaulay
