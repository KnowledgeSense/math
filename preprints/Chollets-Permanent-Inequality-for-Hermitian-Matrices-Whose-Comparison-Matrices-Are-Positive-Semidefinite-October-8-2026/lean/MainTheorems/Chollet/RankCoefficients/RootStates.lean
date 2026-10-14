import MainTheorems.Chollet.RankCoefficients.LinearAction

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

variable {I : Type*} [Fintype I] [DecidableEq I]

def RootedPartition.stateFactor (p : RootedPartition I) (a : Finset (Finset I))
    (t : Finset I) : SquareFree I := if t ∈ a then monomial t else rooted t (p.phase t)

def RootedPartition.statePolynomial (p : RootedPartition I) (a : Finset (Finset I)) :
    SquareFree I := monomial p.closed * ∏ t ∈ p.parts, p.stateFactor a t

omit [Fintype I] in
@[simp] theorem RootedPartition.state_empty (p : RootedPartition I) :
    p.statePolynomial ∅ = p.polynomial := by
  simp [RootedPartition.statePolynomial, RootedPartition.stateFactor, RootedPartition.polynomial]

omit [Fintype I] in
theorem RootedPartition.state_part (p : RootedPartition I) (a : Finset (Finset I))
    (t : Finset I) (ht : t ∈ p.parts) :
    p.statePolynomial a = p.stateFactor a t * monomial p.closed *
      ∏ u ∈ p.parts.erase t, p.stateFactor a u := by
  unfold RootedPartition.statePolynomial
  rw [← Finset.mul_prod_erase p.parts (p.stateFactor a) ht]
  ring

omit [Fintype I] in
theorem RootedPartition.state_insert (p : RootedPartition I) (a : Finset (Finset I))
    (t : Finset I) (ht : t ∈ p.parts) :
    p.statePolynomial (insert t a) = monomial t * monomial p.closed *
      ∏ u ∈ p.parts.erase t, p.stateFactor a u := by
  rw [p.state_part (insert t a) t ht]
  have he : (∏ u ∈ p.parts.erase t, p.stateFactor (insert t a) u) =
      ∏ u ∈ p.parts.erase t, p.stateFactor a u := by
    apply Finset.prod_congr rfl
    intro u hu
    have hut := (Finset.mem_erase.mp hu).1
    simp only [RootedPartition.stateFactor, Finset.mem_insert, hut, false_or]
  rw [he]
  simp only [RootedPartition.stateFactor, Finset.mem_insert_self, ite_true]

omit [Fintype I] in
theorem RootedPartition.variable_state_closed (p : RootedPartition I)
    (a : Finset (Finset I)) (i : I) (hi : i ∈ p.closed) :
    rowVariable i * p.statePolynomial a = 0 := by
  unfold RootedPartition.statePolynomial
  rw [← mul_assoc, variable_monomial_zero p.closed hi, zero_mul]

omit [Fintype I] in
theorem RootedPartition.variable_state (p : RootedPartition I) (a : Finset (Finset I))
    (t : Finset I) (ht : t ∈ p.parts) (i : I) (hi : i ∈ t) :
    rowVariable i * p.statePolynomial a =
      if t ∈ a then 0 else scalar (p.phase t i) * p.statePolynomial (insert t a) := by
  rw [p.state_part a t ht]
  by_cases hta : t ∈ a
  · rw [ite_eq_left hta]
    simp only [RootedPartition.stateFactor, ite_eq_left hta]
    calc
      rowVariable i * (monomial t * monomial p.closed *
          ∏ u ∈ p.parts.erase t, p.stateFactor a u) =
        (rowVariable i * monomial t) * monomial p.closed *
          ∏ u ∈ p.parts.erase t, p.stateFactor a u := by ring
      _ = 0 := by rw [variable_monomial_zero t hi]; ring
  · rw [ite_eq_right hta, p.state_insert a t ht]
    simp only [RootedPartition.stateFactor, ite_eq_right hta]
    calc
      rowVariable i * (rooted t (p.phase t) * monomial p.closed *
          ∏ u ∈ p.parts.erase t, p.stateFactor a u) =
        (rowVariable i * rooted t (p.phase t)) * monomial p.closed *
          ∏ u ∈ p.parts.erase t, p.stateFactor a u := by ring
      _ = _ := by
        rw [variable_rooted t (p.phase t) hi]
        simp only [RootedPartition.stateFactor]
        ring

theorem RootedPartition.state_all (p : RootedPartition I) :
    p.statePolynomial p.parts = monomial (Finset.univ : Finset I) := by
  have he : (∏ t ∈ p.parts, p.stateFactor p.parts t) = ∏ t ∈ p.parts, monomial t := by
    apply Finset.prod_congr rfl
    intro t ht
    rw [RootedPartition.stateFactor, ite_eq_left ht]
  have hp : Set.PairwiseDisjoint (↑p.parts) (id : Finset I → Finset I) := by
    intro s hs t ht hst
    exact p.disjoint s hs t ht hst
  have hu : monomial (p.parts.biUnion id) = ∏ t ∈ p.parts, monomial t := by
    unfold monomial
    exact Finset.prod_biUnion hp
  unfold RootedPartition.statePolynomial
  rw [he, ← hu, ← monomial_union _ _ p.closed_disjoint_union, p.cover_eq]

end ResearchMain.Chollet.RankCoefficients

