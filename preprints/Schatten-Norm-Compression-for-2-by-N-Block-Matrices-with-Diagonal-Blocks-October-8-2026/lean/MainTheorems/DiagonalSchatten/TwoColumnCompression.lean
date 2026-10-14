import MainTheorems.DiagonalSchatten.SignedTwoColumnCompression
import MainTheorems.DiagonalSchatten.ExponentContinuity

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise Topology

theorem continuousOn_compressionFunctional_exponent (B : Matrix (Fin 2) (Fin 2) ℝ) :
    ContinuousOn (fun p : ℝ => compressionFunctional p B) (Set.Ioi 0) := by
  change ContinuousOn (fun p : ℝ => schattenPower p (complexifyRows (realEntryRoot p B))) _
  apply continuousOn_twoRowPower_exponent
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  change ContinuousOn (fun p : ℝ => ((B i j ^ (1 / p) : ℝ) : ℂ)) (Set.Ioi 0)
  apply Complex.continuous_ofReal.comp_continuousOn
  exact continuousOn_const.rpow
    (continuousOn_const.div continuousOn_id (fun p hp => (show 0 < p from hp).ne'))
    (fun p hp => Or.inr (one_div_pos.mpr hp))

theorem nonnegative_half_power_square {x : ℝ} (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
  rw [← Real.rpow_mul_natCast hx ((1 : ℝ) / 2) 2]
  norm_num

theorem compressionFunctional_two_nonnegative (B : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : ∀ i j, 0 ≤ B i j) : compressionFunctional 2 B = ∑ j, ∑ i, B i j := by
  rw [compressionFunctional_eq_realEntryRoot, schattenPower_two]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  simp only [complexifyRows, realEntryRoot, Matrix.of_apply, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  exact nonnegative_half_power_square (hB i j)

theorem compressionFunctional_one_subadditive (B C : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j) :
    compressionFunctional 1 (B + C) ≤ compressionFunctional 1 B + compressionFunctional 1 C := by
  have hl : ContinuousAt (fun p : ℝ => compressionFunctional p (B + C)) 1 :=
    (continuousOn_compressionFunctional_exponent (B + C)).continuousAt
      (isOpen_Ioi.mem_nhds (by norm_num))
  have hr : ContinuousAt (fun p : ℝ => compressionFunctional p B + compressionFunctional p C) 1 :=
    ((continuousOn_compressionFunctional_exponent B).continuousAt
      (isOpen_Ioi.mem_nhds (by norm_num))).add
      ((continuousOn_compressionFunctional_exponent C).continuousAt
        (isOpen_Ioi.mem_nhds (by norm_num)))
  apply le_of_tendsto_of_tendsto (b := 𝓝[>] (1 : ℝ))
    (hl.tendsto.mono_left nhdsWithin_le_nhds)
    (hr.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds
      (isOpen_Iio.mem_nhds (by norm_num : (1 : ℝ) ∈ Set.Iio 2))] with p hp hp2
  exact compressionFunctional_two_column_subadditive hp hp2 B C hB hC

theorem two_column_compression_lower {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (B C : Matrix (Fin 2) (Fin 2) ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (hC : ∀ i j, 0 ≤ C i j) :
    compressionFunctional p (B + C) ≤ compressionFunctional p B + compressionFunctional p C := by
  rcases eq_or_lt_of_le hp with rfl | hp1
  · exact compressionFunctional_one_subadditive B C hB hC
  rcases eq_or_lt_of_le hp2 with hpEq | hpLt
  · subst p
    rw [compressionFunctional_two_nonnegative B hB, compressionFunctional_two_nonnegative C hC,
      compressionFunctional_two_nonnegative (B + C) (fun i j => add_nonneg (hB i j) (hC i j))]
    simp only [Matrix.add_apply, Finset.sum_add_distrib]
    exact le_rfl
  · exact compressionFunctional_two_column_subadditive hp1 hpLt B C hB hC

theorem two_column_compression_upper {p : ℝ} (hp : 2 ≤ p)
    (B C : Matrix (Fin 2) (Fin 2) ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (hC : ∀ i j, 0 ≤ C i j) :
    compressionFunctional p B + compressionFunctional p C ≤ compressionFunctional p (B + C) := by
  rcases eq_or_lt_of_le hp with rfl | hp2
  · rw [compressionFunctional_two_nonnegative B hB, compressionFunctional_two_nonnegative C hC,
      compressionFunctional_two_nonnegative (B + C) (fun i j => add_nonneg (hB i j) (hC i j))]
    simp only [Matrix.add_apply, Finset.sum_add_distrib]
    exact le_rfl
  · exact compressionFunctional_two_column_superadditive hp2 B C hB hC

end

end ResearchMain.DiagonalSchatten
