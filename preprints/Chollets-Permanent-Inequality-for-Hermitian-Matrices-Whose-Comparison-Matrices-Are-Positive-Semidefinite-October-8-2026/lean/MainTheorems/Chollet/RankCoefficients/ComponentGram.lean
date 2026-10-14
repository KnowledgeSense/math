import MainTheorems.Chollet.RankCoefficients.ColumnContraction
import MainTheorems.Chollet.RankCoefficients.DiagonalCoefficients
import MainTheorems.Chollet.RankCoefficients.NormalizedMass
import MainTheorems.Chollet.RankCoefficients.BoundaryCases

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

variable {I : Type*} [Fintype I] [DecidableEq I]

def RootedPartition.mass (p : RootedPartition I) (d : I → ℝ) (t : p.parts) : ℝ :=
  ∑ i ∈ t.val, d i

def RootedPartition.diagonalColumns (p : RootedPartition I) (d : I → ℝ) :
    Matrix p.parts I ℂ := fun t i =>
  if i ∈ t.val then p.phase t.val i * (Real.sqrt (d i) : ℂ) else 0

omit [Fintype I] in
theorem RootedPartition.contraction_diagonal (p : RootedPartition I) (d : I → ℝ)
    (t : p.parts) (j : I) :
    p.contraction (fun i => (Matrix.diagonal (fun u => (Real.sqrt (d u) : ℂ))) i j) t =
      p.diagonalColumns d t j := by
  simp [RootedPartition.contraction, RootedPartition.diagonalColumns, Matrix.diagonal_apply,
    eq_comm]

theorem unit_outer (c : ℂ) (hc : ‖c‖ = 1) : c * star c = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
  norm_num

theorem RootedPartition.diagonalColumns_gram (p : RootedPartition I) (d : I → ℝ)
    (hd : ∀ i, 0 ≤ d i) :
    p.diagonalColumns d * (p.diagonalColumns d).conjTranspose =
      Matrix.diagonal (fun t => (p.mass d t : ℂ)) := by
  funext t u
  rw [Matrix.mul_apply]
  by_cases htu : t = u
  · subst u
    rw [Matrix.diagonal_apply_eq]
    have he : ∀ i, p.diagonalColumns d t i *
        star (p.diagonalColumns d t i) = if i ∈ t.val then (d i : ℂ) else 0 := by
      intro i
      by_cases hi : i ∈ t.val
      · rw [RootedPartition.diagonalColumns, ite_eq_left hi]
        have hs : (Real.sqrt (d i) : ℂ) ^ 2 = (d i : ℂ) := by
          norm_cast
          exact Real.sq_sqrt (hd i)
        simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
        calc
          _ = (p.phase t.val i * star (p.phase t.val i)) *
              (Real.sqrt (d i) : ℂ) ^ 2 := by
                simp only [Complex.star_def]
                ring
          _ = _ := by
            rw [unit_outer _ (p.unit t.val t.property i hi), hs, one_mul, ite_eq_left hi]
      · simp only [RootedPartition.diagonalColumns, ite_eq_right hi, star_zero, zero_mul]
    simp only [Matrix.conjTranspose_apply, he]
    simp [RootedPartition.mass, ← Complex.ofReal_sum]
  · rw [Matrix.diagonal_apply_ne _ htu]
    apply Finset.sum_eq_zero
    intro i _
    have hdis := p.disjoint t.val t.property u.val u.property
      (fun h => htu (Subtype.ext h))
    by_cases hi : i ∈ t.val
    · have hui : i ∉ u.val := Finset.disjoint_left.mp hdis hi
      simp only [Matrix.conjTranspose_apply, RootedPartition.diagonalColumns,
        ite_eq_right hui, star_zero, mul_zero]
    · simp only [RootedPartition.diagonalColumns, ite_eq_right hi, zero_mul]

theorem RootedPartition.contraction_mass (p : RootedPartition I) (a : ℝ)
    (d : I → ℝ) (z : I → ℂ) (ha : 0 < a) (hd : ∀ i, ‖z i‖ ≤ d i)
    (hm : ∑ i, ‖z i‖ ≤ a) :
    ∑ t : p.parts, ‖p.contraction (normalizedBorder a z) t‖ ^ 2 / p.mass d t ≤ 1 := by
  have hp : Set.PairwiseDisjoint (↑p.parts) (fun t : Finset I => t) := p.disjoint
  have h := componentRatio_total p.parts (fun t => t) hp a d z p.phase ha hd
    (fun t ht i hi => (p.unit t ht i hi).le) hm
  simp only [RootedPartition.contraction, RootedPartition.mass,
    normalized_componentRatio _ _ _ _ _ ha]
  rw [← Finset.sum_subtype p.parts (fun _ => Iff.rfl)
    (fun t => componentRatio a d z (p.phase t) t)]
  exact h

omit [Fintype I] [DecidableEq I] in
theorem RootedPartition.zero_mass_contraction (p : RootedPartition I) (a : ℝ)
    (d : I → ℝ) (z : I → ℂ) (hd : ∀ i, ‖z i‖ ≤ d i)
    (t : p.parts) (ht : p.mass d t = 0) :
    p.contraction (normalizedBorder a z) t = 0 := by
  rw [RootedPartition.contraction, normalized_phase_sum]
  rw [component_zero_mass d z (p.phase t.val) t.val (fun i _ => hd i) ht, zero_div]

theorem RootedPartition.diagonal_coefficient_bound (p : RootedPartition I) (a : ℝ)
    (d : I → ℝ) (z : I → ℂ) (ha : 0 < a) (hd : ∀ i, ‖z i‖ ≤ d i)
    (hm : ∑ i, ‖z i‖ ≤ a) (k : ℕ) (hk : 1 ≤ k) :
    rankCoefficient (Matrix.diagonal (fun t => (p.mass d t : ℂ)))
        (p.contraction (normalizedBorder a z)) k ≤
      rankCoefficient (Matrix.diagonal (fun t => (p.mass d t : ℂ)))
        (p.contraction (normalizedBorder a z)) 1 ∧
    rankCoefficient (Matrix.diagonal (fun t => (p.mass d t : ℂ)))
        (p.contraction (normalizedBorder a z)) 1 ≤
      rankCoefficient (Matrix.diagonal (fun t => (p.mass d t : ℂ)))
        (p.contraction (normalizedBorder a z)) 0 := by
  have hD : ∀ t : p.parts, 0 ≤ p.mass d t := fun t =>
    Finset.sum_nonneg (fun i _ => (norm_nonneg _).trans (hd i))
  by_cases hp : ∀ t : p.parts, 0 < p.mass d t
  · exact rankCoefficient_diagonal_bound _ _ hp (p.contraction_mass a d z ha hd hm) k hk
  · push Not at hp
    obtain ⟨t, ht⟩ := hp
    have hz : p.mass d t = 0 := le_antisymm ht (hD t)
    have hx := p.zero_mass_contraction a d z hd t hz
    rw [rankCoefficient_diagonal_zero _ _ t hz hx k,
      rankCoefficient_diagonal_zero _ _ t hz hx 1,
      rankCoefficient_diagonal_zero _ _ t hz hx 0]
    exact ⟨le_rfl, le_rfl⟩

end ResearchMain.Chollet.RankCoefficients

