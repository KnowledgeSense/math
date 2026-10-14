import Dowling.GainPartitionMergeRoots
import Dowling.GainActionAlgebra

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

theorem filter_joint (p : GainPartition G n) (i r : Fin n) (a : G)
    (hi : p.code i = some (r,a)) :
    {x ∈ p.solutionSet | x i = none} = {x ∈ p.solutionSet | x r = none} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  apply and_congr_right
  intro hx
  rw [((p.mem_solutionSet x).mp hx).2 i r a hi, gainAct_eq_none_iff]

theorem filter_link_nonzero (p : GainPartition G n) (i j r s : Fin n) (a b g : G)
    (hi : p.code i = some (r,a)) (hj : p.code j = some (s,b)) :
    {x ∈ p.solutionSet | x j = gainAct G (x i) g} =
      {x ∈ p.solutionSet | x s = gainAct G (x r) (a*g*b⁻¹)} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  apply and_congr_right
  intro hx
  have he := ((p.mem_solutionSet x).mp hx).2
  rw [he i r a hi, he j s b hj, gainAct_mul, gainAct_compare]

theorem filter_link_zero_tail (p : GainPartition G n) (i j s : Fin n) (b g : G)
    (hi : p.code i = none) (hj : p.code j = some (s,b)) :
    {x ∈ p.solutionSet | x j = gainAct G (x i) g} =
      {x ∈ p.solutionSet | x s = none} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  apply and_congr_right
  intro hx
  have he := (p.mem_solutionSet x).mp hx
  rw [he.1 i hi, gainAct_none, he.2 j s b hj, gainAct_eq_none_iff]

theorem filter_link_zero_head (p : GainPartition G n) (i j r : Fin n) (a g : G)
    (hi : p.code i = some (r,a)) (hj : p.code j = none) :
    {x ∈ p.solutionSet | x j = gainAct G (x i) g} =
      {x ∈ p.solutionSet | x r = none} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  apply and_congr_right
  intro hx
  have he := (p.mem_solutionSet x).mp hx
  rw [he.1 j hj, he.2 i r a hi, gainAct_mul, eq_comm, gainAct_eq_none_iff]

theorem filter_same_root (p : GainPartition G n) (r : Fin n) (g : G) (hg : g ≠ 1) :
    {x ∈ p.solutionSet | x r = gainAct G (x r) g} =
      {x ∈ p.solutionSet | x r = none} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  apply and_congr_right
  intro _
  rw [eq_comm, gainAct_fixed_iff _ _ hg]

theorem filter_reverse_roots (p : GainPartition G n) (r s : Fin n) (g : G) :
    {x ∈ p.solutionSet | x s = gainAct G (x r) g} =
      {x ∈ p.solutionSet | x r = gainAct G (x s) g⁻¹} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  exact and_congr_right (fun _ => gainAct_reverse (x r) (x s) g)

end Dowling.GainPartition
