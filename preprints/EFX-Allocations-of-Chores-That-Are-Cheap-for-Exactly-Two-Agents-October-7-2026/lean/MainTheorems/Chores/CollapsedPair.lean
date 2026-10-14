import MainTheorems.Chores.IsolatedPair

namespace ResearchMain.Chores

open scoped BigOperators

variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]

def collapsedAllowed (M : TwoCheapModel A E) (a b : A) (e : E) : Finset A :=
  if e ∈ incidentEdges M {a, b} then {a} else insert a (endpointAllowed M e)

def collapsedCapacity (a b : A) (q T : ℕ) (c : A) : ℕ :=
  if c = a then T else if c = b then 0 else q

omit [Fintype A] [Fintype E] [DecidableEq E] in
theorem collapsed_capacity_sum {a b : A} (q T : ℕ) (U : Finset A) :
    (∑ c ∈ U, collapsedCapacity a b q T c) =
      (if a ∈ U then T else 0) + q * (U \ {a, b}).card := by
  have hA : U.filter (fun c => c = a) = if a ∈ U then {a} else ∅ := by
    ext c
    by_cases ha : a ∈ U <;> simp [ha] <;> aesop
  have hW : (U.filter (fun c => c ≠ a)).filter (fun c => c ≠ b) = U \ {a, b} := by
    ext c
    simp [not_or, and_assoc]
  unfold collapsedCapacity
  rw [Finset.sum_ite]
  have hsecond : (∑ c ∈ U.filter (fun c => ¬c = a), if c = b then 0 else q) =
      q * (U \ {a, b}).card := by
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul]
    rw [hW]
    exact Nat.mul_comm _ _
  rw [hsecond, hA]
  by_cases ha : a ∈ U <;> simp [ha]

omit [Fintype A] [Fintype E] [DecidableEq E] in
theorem pair_union_outside (a b : A) (U : Finset A) :
    ({a, b} : Finset A) ∪ (U \ {a, b}) = {a, b} ∪ U := by
  ext c
  simp

omit [Fintype E] [DecidableEq E] in
theorem pair_outside_card {a b : A} (hab : a ≠ b) (U : Finset A) :
    ({a, b} ∪ U)ᶜ.card + (U \ {a, b}).card + 2 = Fintype.card A := by
  have hd : Disjoint ({a, b} : Finset A) (U \ {a, b}) := Finset.disjoint_sdiff
  have hu : ({a, b} ∪ U).card = 2 + (U \ {a, b}).card := by
    rw [← pair_union_outside a b U, Finset.card_union_of_disjoint hd, Finset.card_pair hab]
  have ht := Finset.card_compl_add_card ({a, b} ∪ U)
  rw [hu] at ht
  omega

omit [Fintype A] in
theorem collapsed_contains_high (M : TwoCheapModel A E) (a b : A) (e : E) :
    a ∈ collapsedAllowed M a b e := by
  unfold collapsedAllowed
  split_ifs <;> simp

omit [Fintype A] in
theorem collapsed_endpoint (M : TwoCheapModel A E) {a b c : A} {e : E}
    (he : e ∉ incidentEdges M {a, b}) (hc : M.Cheap c e) :
    c ∈ collapsedAllowed M a b e := by
  rw [collapsedAllowed, ite_eq_right he]
  exact Finset.mem_insert_of_mem ((mem_endpointAllowed M c e).mpr hc)

omit [Fintype A] in
theorem collapsed_outside_incident (M : TwoCheapModel A E) {a b : A} (hab : a ≠ b)
    (hiso : IsolatedPair M a b) (U : Finset A) :
    incidentEdges M (U \ {a, b}) ⊆ incidentAllowed (collapsedAllowed M a b) U := by
  have hd : Disjoint ({a, b} : Finset A) (U \ {a, b}) := Finset.disjoint_sdiff
  have hdis := isolated_incident_disjoint M hab hiso hd
  rw [Finset.disjoint_left] at hdis
  intro e he
  have hn : e ∉ incidentEdges M {a, b} := fun h => hdis h he
  rw [mem_incidentEdges] at he
  simp only [incidentAllowed, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases he with h | h
  · exact ⟨M.first e, (Finset.mem_sdiff.mp h).1, collapsed_endpoint M hn (Or.inl rfl)⟩
  · exact ⟨M.second e, (Finset.mem_sdiff.mp h).1, collapsed_endpoint M hn (Or.inr rfl)⟩

end ResearchMain.Chores
