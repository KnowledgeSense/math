import MainTheorems.Chollet.RankCoefficients.Partition

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

variable {I : Type*} [Fintype I] [DecidableEq I]

def linearForm (x : I → ℂ) : SquareFree I := ∑ i, scalar (x i) * rowVariable i

def RootedPartition.closedPolynomial (p : RootedPartition I) (s : Finset I) : SquareFree I :=
  monomial s * monomial p.closed * ∏ t ∈ p.parts.erase s, rooted t (p.phase t)

omit [Fintype I] in
theorem RootedPartition.variable_closed (p : RootedPartition I) (i : I)
    (hi : i ∈ p.closed) : rowVariable i * p.polynomial = 0 := by
  unfold RootedPartition.polynomial
  rw [← mul_assoc, variable_monomial_zero p.closed hi, zero_mul]

omit [Fintype I] in
theorem RootedPartition.variable_open (p : RootedPartition I) (s : Finset I)
    (hs : s ∈ p.parts) (i : I) (hi : i ∈ s) :
    rowVariable i * p.polynomial = scalar (p.phase s i) * p.closedPolynomial s := by
  rw [p.polynomial_part s hs]
  unfold RootedPartition.closedPolynomial
  calc
    rowVariable i * (rooted s (p.phase s) * monomial p.closed *
        ∏ t ∈ p.parts.erase s, rooted t (p.phase t)) =
      (rowVariable i * rooted s (p.phase s)) * monomial p.closed *
        ∏ t ∈ p.parts.erase s, rooted t (p.phase t) := by ring
    _ = _ := by rw [variable_rooted s (p.phase s) hi]; ring

theorem RootedPartition.cover_eq (p : RootedPartition I) :
    p.closed ∪ p.parts.biUnion id = Finset.univ := by
  ext i
  simp only [Finset.mem_union, Finset.mem_biUnion, id_eq, Finset.mem_univ, iff_true]
  exact p.cover i

omit [Fintype I] in
theorem RootedPartition.closed_disjoint_union (p : RootedPartition I) :
    Disjoint p.closed (p.parts.biUnion id) := by
  apply Finset.disjoint_left.mpr
  intro i hic hiu
  obtain ⟨s, hs, his⟩ := Finset.mem_biUnion.mp hiu
  exact Finset.disjoint_left.mp (p.closed_disjoint s hs) hic his

theorem RootedPartition.linear_action (p : RootedPartition I) (x : I → ℂ) :
    linearForm x * p.polynomial =
      ∑ s ∈ p.parts, scalar (∑ i ∈ s, p.phase s i * x i) * p.closedPolynomial s := by
  have hpair : Set.PairwiseDisjoint (↑p.parts) (id : Finset I → Finset I) := by
    intro s hs t ht hst
    exact p.disjoint s hs t ht hst
  have hclosed : (∑ i ∈ p.closed, scalar (x i) * (rowVariable i * p.polynomial)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [p.variable_closed i hi, mul_zero]
  calc
    linearForm x * p.polynomial =
        ∑ i, scalar (x i) * (rowVariable i * p.polynomial) := by
      unfold linearForm
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ s ∈ p.parts, ∑ i ∈ s, scalar (x i) * (rowVariable i * p.polynomial) := by
      rw [← p.cover_eq, Finset.sum_union p.closed_disjoint_union, hclosed, zero_add,
        Finset.sum_biUnion hpair]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [scalar_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [p.variable_open s hs i hi]
      rw [scalar_mul]
      ring

end ResearchMain.Chollet.RankCoefficients

