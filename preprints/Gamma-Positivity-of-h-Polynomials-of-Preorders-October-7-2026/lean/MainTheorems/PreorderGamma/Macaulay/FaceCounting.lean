import MainTheorems.PreorderGamma.Macaulay.BallotFaces
import MainTheorems.PreorderGamma.Macaulay.BallotCount
import MainTheorems.PreorderGamma.GammaProperties
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace ResearchMain.PreorderGamma.Macaulay

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

noncomputable def facePairs (i : ℕ) : Finset (Σ _k : ℕ, Σ _M : Finset (E × E), Finset E) := by
  classical
  exact (Finset.range (Fintype.card E / 2 + 1)).sigma fun k =>
    (canonicalMatchings k).sigma fun M =>
      if k ≤ i then ballotSets vertexIndex (freeVertices M) (i - k) else ∅

theorem mem_facePairs {i : ℕ} {x : Σ _k : ℕ, Σ _M : Finset (E × E), Finset E} :
    x ∈ facePairs i ↔ x.1 ≤ Fintype.card E / 2 ∧
      IsCanonicalMatching x.2.1 ∧ x.2.1.card = x.1 ∧ x.1 ≤ i ∧
      IsBallotWithin vertexIndex (freeVertices x.2.1) x.2.2 ∧ x.2.2.card = i - x.1 := by
  classical
  simp only [facePairs, Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff, mem_canonicalMatchings]
  by_cases hi : x.1 ≤ i
  · simp only [ite_eq_left hi, mem_ballotSets]
    simp only [and_assoc, hi, true_and]
  · simp only [ite_eq_right hi, Finset.notMem_empty, and_false]
    simp only [hi, false_and, and_false]

theorem facePairs_card_eq_ballotFaces (i : ℕ) :
    (facePairs (E := E) i).card = (ballotFaces (E := E) i).card := by
  classical
  apply Finset.card_bij (fun x _ => x.2.1.disjSum x.2.2)
  · intro x hx
    obtain ⟨_, hM, hcardM, hki, hA, hcardA⟩ := mem_facePairs.mp hx
    apply mem_ballotFaces.mpr
    constructor
    · simpa only [IsBallotFace, Finset.toLeft_disjSum, Finset.toRight_disjSum] using ⟨hM, hA⟩
    · rw [Finset.card_disjSum, hcardM, hcardA]
      omega
  · intro x hx y hy he
    obtain ⟨_, _, hcardx, _, _, _⟩ := mem_facePairs.mp hx
    obtain ⟨_, _, hcardy, _, _, _⟩ := mem_facePairs.mp hy
    obtain ⟨hM, hA⟩ := Finset.disjSum_inj.mp he
    have hk : x.1 = y.1 := by rw [← hcardx, ← hcardy, hM]
    exact Sigma.ext hk (heq_of_eq (Sigma.ext hM (heq_of_eq hA)))
  · intro F hF
    obtain ⟨hb, hc⟩ := mem_ballotFaces.mp hF
    have hfree := hb.1.1.card_freeVertices_add
    have hcard := Finset.card_toLeft_add_card_toRight (u := F)
    refine ⟨⟨F.toLeft.card, F.toLeft, F.toRight⟩, ?_, Finset.toLeft_disjSum_toRight⟩
    apply mem_facePairs.mpr
    dsimp only
    exact ⟨by omega, hb.1, rfl, by omega, hb.2, by omega⟩

theorem ballotFaces_card_expansion (i : ℕ) :
    (ballotFaces (E := E) i).card =
      ∑ k ∈ Finset.range (Fintype.card E / 2 + 1), gammaCoefficient (E := E) k *
        if k ≤ i then ballotNumber (Fintype.card E - 2 * k) (i - k) else 0 := by
  classical
  rw [← facePairs_card_eq_ballotFaces, facePairs, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.card_sigma]
  by_cases hki : k ≤ i
  · simp only [ite_eq_left hki]
    calc
      ∑ M ∈ canonicalMatchings k, (ballotSets vertexIndex (freeVertices M) (i - k)).card =
          ∑ _M ∈ canonicalMatchings (E := E) k,
            ballotNumber (Fintype.card E - 2 * k) (i - k) := by
        apply Finset.sum_congr rfl
        intro M hm
        obtain ⟨hM, hc⟩ := mem_canonicalMatchings.mp hm
        rw [ballotSets_card vertexIndex_injective, hM.1.card_freeVertices, hc]
      _ = (canonicalMatchings (E := E) k).card *
          ballotNumber (Fintype.card E - 2 * k) (i - k) := by simp
      _ = _ := by rw [canonicalMatchings_card]
  · simp only [ite_eq_right hki, Finset.card_empty, Finset.sum_const_zero, Nat.mul_zero]

theorem gammaBasis_g_coeff_ballot (n k i : ℕ) :
    (gammaBasis n k).coeff (i + 1) - (gammaBasis n k).coeff i =
      if k ≤ i + 1 then ballotNumber (n - 2 * k) (i + 1 - k) else 0 := by
  by_cases hki : k ≤ i
  · have hk' : k ≤ i + 1 := by omega
    have hs : i + 1 - k = (i - k) + 1 := by omega
    rw [gammaBasis_coeff, gammaBasis_coeff, ite_eq_left hk', ite_eq_left hki,
      ite_eq_left hk', hs, ballotNumber_succ]
  · by_cases hk' : k ≤ i + 1
    · have hk : k = i + 1 := by omega
      subst k
      simp [gammaBasis_coeff, ballotNumber]
    · rw [ite_eq_right hk']
      exact gammaBasis_g_coeff_zero_of_large n k i (by omega)

@[simp] theorem ballotFaces_zero : ballotFaces (E := E) 0 = {∅} := by
  classical
  ext F
  simp only [mem_ballotFaces, Finset.mem_singleton, Finset.card_eq_zero]
  constructor
  · exact fun h => h.2
  · intro h
    subst F
    exact ⟨isBallotFace_empty, rfl⟩

theorem ballotFaces_card_eq_supportGVector (i : ℕ) :
    (ballotFaces (E := E) i).card = supportGVector (E := E) i := by
  by_cases hi : i ≤ Fintype.card E / 2
  · cases i with
    | zero => simp
    | succ i =>
      rw [supportGVector_succ_gamma i (by omega), ballotFaces_card_expansion]
      apply Finset.sum_congr rfl
      intro k _
      rw [gammaBasis_g_coeff_ballot]
  · rw [ballotFaces_empty_of_large i (by omega),
      supportGVector_eq_zero_of_large i (by omega), Finset.card_empty]

end ResearchMain.PreorderGamma.Macaulay
