import MainTheorems.Chores.EqualCounts

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

def IsolatedPair (M : TwoCheapModel A E) (a b : A) : Prop :=
  ∀ e, M.Cheap a e ∨ M.Cheap b e → M.Cheap a e ∧ M.Cheap b e

omit [Fintype E] [DecidableEq A] [DecidableEq E] in
theorem pair_endpoints (M : TwoCheapModel A E) {a b : A} {e : E} (hab : a ≠ b)
    (ha : M.Cheap a e) (hb : M.Cheap b e) :
    (M.first e = a ∧ M.second e = b) ∨ (M.first e = b ∧ M.second e = a) := by
  unfold TwoCheapModel.Cheap at ha hb
  have hd := M.distinct e
  aesop

omit [DecidableEq E] in
theorem isolated_incident_disjoint (M : TwoCheapModel A E) {a b : A} (hab : a ≠ b)
    (hiso : IsolatedPair M a b) {U : Finset A} (hU : Disjoint ({a, b} : Finset A) U) :
    Disjoint (incidentEdges M {a, b}) (incidentEdges M U) := by
  rw [Finset.disjoint_left] at hU ⊢
  intro e heP heU
  have hcheap : M.Cheap a e ∨ M.Cheap b e := by
    rw [mem_incidentEdges] at heP
    simp only [Finset.mem_insert, Finset.mem_singleton] at heP
    unfold TwoCheapModel.Cheap
    aesop
  obtain ⟨ha, hb⟩ := hiso e hcheap
  obtain h | h := pair_endpoints M hab ha hb
  · rw [mem_incidentEdges, h.1, h.2] at heU
    rcases heU with h | h
    · exact hU (by simp) h
    · exact hU (by simp) h
  · rw [mem_incidentEdges, h.1, h.2] at heU
    rcases heU with h | h
    · exact hU (by simp) h
    · exact hU (by simp) h

theorem isolated_density (M : TwoCheapModel A E) {a b : A} (hab : a ≠ b)
    (hiso : IsolatedPair M a b) {μ : ℝ} (hmax : MaxDeficient M μ {a, b})
    {U : Finset A} (hU : Disjoint ({a, b} : Finset A) U) :
    μ * U.card ≤ (incidentEdges M U).card := by
  have ht := hmax ({a, b} ∪ U)
  rw [deficiency, deficiency, incident_union,
    Finset.card_union_of_disjoint hU,
    Finset.card_union_of_disjoint (isolated_incident_disjoint M hab hiso hU)] at ht
  push_cast at ht
  linarith only [ht]

omit [DecidableEq E] in
theorem isolated_pair_card_bound (M : TwoCheapModel A E) {a b : A} (hab : a ≠ b)
    {μ : ℝ} (hmax : MaxDeficient M μ {a, b}) :
    ((incidentEdges M {a, b}).card : ℝ) ≤ 2 * μ := by
  have ht := hmax ∅
  rw [deficiency_empty, deficiency, Finset.card_pair hab] at ht
  norm_num at ht
  linarith only [ht]

end ResearchMain.Chores
