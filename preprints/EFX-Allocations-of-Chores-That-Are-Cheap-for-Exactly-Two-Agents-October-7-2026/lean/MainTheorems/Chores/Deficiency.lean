import MainTheorems.Chores.BoundedAllocation
import MainTheorems.Chores.Counts
import Mathlib.Data.Finset.Max

namespace ResearchMain.Chores

open scoped BigOperators

variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]

def endpointAllowed (M : TwoCheapModel A E) (e : E) : Finset A :=
  {M.first e, M.second e}

def incidentEdges (M : TwoCheapModel A E) (U : Finset A) : Finset E :=
  Finset.univ.filter (fun e => M.first e ∈ U ∨ M.second e ∈ U)

noncomputable def deficiency (M : TwoCheapModel A E) (μ : ℝ) (U : Finset A) : ℝ :=
  μ * U.card - (incidentEdges M U).card

def MaxDeficient (M : TwoCheapModel A E) (μ : ℝ) (S : Finset A) : Prop :=
  ∀ U : Finset A, deficiency M μ U ≤ deficiency M μ S

def separatedAllowed (M : TwoCheapModel A E) (S : Finset A) (e : E) : Finset A :=
  if M.first e ∈ S ∨ M.second e ∈ S then endpointAllowed M e ∩ S
  else endpointAllowed M e ∪ S

omit [Fintype A] [Fintype E] [DecidableEq E] in
theorem mem_endpointAllowed (M : TwoCheapModel A E) (a : A) (e : E) :
    a ∈ endpointAllowed M e ↔ M.Cheap a e := by
  simp [endpointAllowed, TwoCheapModel.Cheap]

omit [Fintype A] [DecidableEq E] in
theorem mem_incidentEdges (M : TwoCheapModel A E) (U : Finset A) (e : E) :
    e ∈ incidentEdges M U ↔ M.first e ∈ U ∨ M.second e ∈ U := by
  simp [incidentEdges]

omit [Fintype A] [DecidableEq E] in
theorem incident_mono (M : TwoCheapModel A E) {U V : Finset A} (h : U ⊆ V) :
    incidentEdges M U ⊆ incidentEdges M V := by
  intro e he
  rw [mem_incidentEdges] at he ⊢
  exact he.elim (fun h' => Or.inl (h h')) (fun h' => Or.inr (h h'))

omit [Fintype A] in
theorem incident_union (M : TwoCheapModel A E) (U V : Finset A) :
    incidentEdges M (U ∪ V) = incidentEdges M U ∪ incidentEdges M V := by
  ext e
  simp only [mem_incidentEdges, Finset.mem_union]
  tauto

omit [DecidableEq E] in
theorem incident_univ (M : TwoCheapModel A E) : incidentEdges M Finset.univ = Finset.univ := by
  simp [incidentEdges]

omit [Fintype A] [DecidableEq E] in
theorem incident_empty (M : TwoCheapModel A E) : incidentEdges M ∅ = ∅ := by
  simp [incidentEdges]

omit [Fintype A] [DecidableEq E] in
theorem deficiency_empty (M : TwoCheapModel A E) (μ : ℝ) : deficiency M μ ∅ = 0 := by
  simp [deficiency, incident_empty]

omit [DecidableEq E] in
theorem deficiency_univ (M : TwoCheapModel A E) (μ : ℝ)
    (hμ : μ * Fintype.card A = Fintype.card E) : deficiency M μ Finset.univ = 0 := by
  simp [deficiency, incident_univ, hμ]

omit [DecidableEq E] in
theorem exists_max_deficient (M : TwoCheapModel A E) (μ : ℝ) :
    ∃ S : Finset A, MaxDeficient M μ S := by
  obtain ⟨S, _, hS⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset A))
    (deficiency M μ) ⟨∅, Finset.mem_univ _⟩
  exact ⟨S, fun U => hS U (Finset.mem_univ _)⟩

omit [DecidableEq E] in
theorem incident_compl_small (M : TwoCheapModel A E) {S : Finset A}
    (hS : Sᶜ.card ≤ 1) : incidentEdges M S = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro e
  rw [mem_incidentEdges]
  by_contra h
  push Not at h
  have hp : {M.first e, M.second e} ⊆ Sᶜ := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> simp_all
  have hc := Finset.card_le_card hp
  rw [Finset.card_pair (M.distinct e)] at hc
  omega

omit [DecidableEq E] in
theorem positive_deficiency_compl (M : TwoCheapModel A E) {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : μ * Fintype.card A = Fintype.card E) {S : Finset A}
    (hS : 0 < deficiency M μ S) : 2 ≤ Sᶜ.card := by
  by_contra h
  have hsmall : Sᶜ.card ≤ 1 := by omega
  rw [deficiency, incident_compl_small M hsmall, Finset.card_univ] at hS
  have hc : (S.card : ℝ) ≤ Fintype.card A := by exact_mod_cast Finset.card_le_univ S
  nlinarith

end ResearchMain.Chores
