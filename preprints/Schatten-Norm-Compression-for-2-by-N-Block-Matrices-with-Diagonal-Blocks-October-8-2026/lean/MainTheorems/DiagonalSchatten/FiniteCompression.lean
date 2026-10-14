import MainTheorems.DiagonalSchatten.FiniteSignedCompression
import MainTheorems.DiagonalSchatten.TwoColumnCompression

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise Topology

variable {J : Type*} [Fintype J] [DecidableEq J]

def paddedRows (X : Matrix (Fin 2) J ℝ) : Matrix (Fin 2) (J ⊕ Fin 2) ℝ :=
  fun i j => Sum.elim (X i) (fun _ => 0) j

omit [DecidableEq J] in
theorem paddedRows_gram (X : Matrix (Fin 2) J ℝ) :
    gramFirst (paddedRows X) = gramFirst X ∧
      gramSecond (paddedRows X) = gramSecond X ∧
      gramCross (paddedRows X) = gramCross X := by
  simp [gramFirst, gramSecond, gramCross, paddedRows, Fintype.sum_sum_type]

omit [Fintype J] [DecidableEq J] in
theorem paddedRows_entryRoot {p : ℝ} (hp : 0 < p) (B : Matrix (Fin 2) J ℝ) :
    realEntryRoot p (paddedRows B) = paddedRows (realEntryRoot p B) := by
  ext i j
  cases j with
  | inl j => rfl
  | inr j =>
      change (0 : ℝ) ^ (1 / p) = 0
      exact Real.zero_rpow (one_div_ne_zero hp.ne')

theorem compressionFunctional_paddedRows {p : ℝ} (hp : 0 < p) (B : Matrix (Fin 2) J ℝ) :
    compressionFunctional p (paddedRows B) = compressionFunctional p B := by
  rw [compressionFunctional_eq_realEntryRoot, compressionFunctional_eq_realEntryRoot,
    paddedRows_entryRoot hp, schattenPower_complexify hp, schattenPower_complexify hp]
  obtain ⟨h0, h1, h2⟩ := paddedRows_gram (realEntryRoot p B)
  simp only [realGramPlus, realGramMinus, h0, h1, h2]

omit [Fintype J] [DecidableEq J] in
theorem paddedRows_add (B C : Matrix (Fin 2) J ℝ) :
    paddedRows (B + C) = paddedRows B + paddedRows C := by
  ext i j
  cases j <;> simp [paddedRows]

omit [Fintype J] [DecidableEq J] in
theorem paddedRows_nonnegative (B : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 ≤ B i j) :
    ∀ i j, 0 ≤ paddedRows B i j := by
  intro i j
  cases j with
  | inl j => exact hB i j
  | inr j => exact le_rfl

theorem compressionFunctional_finite_subadditive {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (B C : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j) :
    compressionFunctional p (B + C) ≤ compressionFunctional p B + compressionFunctional p C := by
  have hp0 : 0 < p := by linarith
  have h := compressionFunctional_nontrivial_subadditive hp hp2 (paddedRows B) (paddedRows C)
    (paddedRows_nonnegative B hB) (paddedRows_nonnegative C hC)
  rw [← paddedRows_add, compressionFunctional_paddedRows hp0,
    compressionFunctional_paddedRows hp0, compressionFunctional_paddedRows hp0] at h
  exact h

theorem compressionFunctional_finite_superadditive {p : ℝ} (hp : 2 < p) (hp4 : p < 4)
    (B C : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j) :
    compressionFunctional p B + compressionFunctional p C ≤ compressionFunctional p (B + C) := by
  have hp0 : 0 < p := by linarith
  have h := compressionFunctional_nontrivial_superadditive hp hp4 (paddedRows B) (paddedRows C)
    (paddedRows_nonnegative B hB) (paddedRows_nonnegative C hC)
  rw [← paddedRows_add, compressionFunctional_paddedRows hp0,
    compressionFunctional_paddedRows hp0, compressionFunctional_paddedRows hp0] at h
  exact h

theorem finite_compression_exponent_continuous (B : Matrix (Fin 2) J ℝ) :
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

theorem finite_compression_two (B : Matrix (Fin 2) J ℝ)
    (hB : ∀ i j, 0 ≤ B i j) : compressionFunctional 2 B = ∑ j, ∑ i, B i j := by
  rw [compressionFunctional_eq_realEntryRoot, schattenPower_two]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  simp only [complexifyRows, realEntryRoot, Matrix.of_apply, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  exact nonnegative_half_power_square (hB i j)

theorem finite_compression_one_subadditive (B C : Matrix (Fin 2) J ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j) :
    compressionFunctional 1 (B + C) ≤ compressionFunctional 1 B + compressionFunctional 1 C := by
  have hl : ContinuousAt (fun p : ℝ => compressionFunctional p (B + C)) 1 :=
    (finite_compression_exponent_continuous (B + C)).continuousAt
      (isOpen_Ioi.mem_nhds (by norm_num))
  have hr : ContinuousAt (fun p : ℝ => compressionFunctional p B + compressionFunctional p C) 1 :=
    ((finite_compression_exponent_continuous B).continuousAt
      (isOpen_Ioi.mem_nhds (by norm_num))).add
      ((finite_compression_exponent_continuous C).continuousAt
        (isOpen_Ioi.mem_nhds (by norm_num)))
  apply le_of_tendsto_of_tendsto (b := 𝓝[>] (1 : ℝ))
    (hl.tendsto.mono_left nhdsWithin_le_nhds)
    (hr.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds
      (isOpen_Iio.mem_nhds (by norm_num : (1 : ℝ) ∈ Set.Iio 2))] with p hp hp2
  exact compressionFunctional_finite_subadditive hp hp2 B C hB hC

theorem finite_compression_lower {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (B C : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j) :
    compressionFunctional p (B + C) ≤ compressionFunctional p B + compressionFunctional p C := by
  rcases eq_or_lt_of_le hp with rfl | hp1
  · exact finite_compression_one_subadditive B C hB hC
  rcases eq_or_lt_of_le hp2 with hpEq | hpLt
  · subst p
    rw [finite_compression_two B hB, finite_compression_two C hC,
      finite_compression_two (B + C) (fun i j => add_nonneg (hB i j) (hC i j))]
    simp only [Matrix.add_apply, Finset.sum_add_distrib]
    exact le_rfl
  · exact compressionFunctional_finite_subadditive hp1 hpLt B C hB hC

theorem finite_compression_upper_below_four {p : ℝ} (hp : 2 ≤ p) (hp4 : p < 4)
    (B C : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j) :
    compressionFunctional p B + compressionFunctional p C ≤ compressionFunctional p (B + C) := by
  rcases eq_or_lt_of_le hp with rfl | hp2
  · rw [finite_compression_two B hB, finite_compression_two C hC,
      finite_compression_two (B + C) (fun i j => add_nonneg (hB i j) (hC i j))]
    simp only [Matrix.add_apply, Finset.sum_add_distrib]
    exact le_rfl
  · exact compressionFunctional_finite_superadditive hp2 hp4 B C hB hC

end

end ResearchMain.DiagonalSchatten
