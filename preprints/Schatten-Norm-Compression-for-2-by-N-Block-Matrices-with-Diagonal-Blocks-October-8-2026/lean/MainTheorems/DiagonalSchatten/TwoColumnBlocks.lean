import MainTheorems.DiagonalSchatten.TwoColumnCompression

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators

variable {D : Type*} [Fintype D] [DecidableEq D]

omit [Fintype D] in
theorem two_column_compression_sum_lower {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (s : Finset D) (B : D → Matrix (Fin 2) (Fin 2) ℝ)
    (hB : ∀ d ∈ s, ∀ i j, 0 ≤ B d i j) :
    compressionFunctional p (∑ d ∈ s, B d) ≤ ∑ d ∈ s, compressionFunctional p (B d) := by
  have hp0 : 0 < p := by linarith
  revert hB
  induction s using Finset.induction_on with
  | empty => intro _; simp [compressionFunctional_zero hp0]
  | @insert d s hd ih =>
      intro hB
      rw [Finset.sum_insert hd, Finset.sum_insert hd]
      have hs : ∀ e ∈ s, ∀ i j, 0 ≤ B e i j :=
        fun e he => hB e (Finset.mem_insert_of_mem he)
      have hsum : ∀ i j, 0 ≤ (∑ e ∈ s, B e) i j := by
        intro i j
        simp only [Matrix.sum_apply]
        exact Finset.sum_nonneg fun e he => hs e he i j
      have hstep := two_column_compression_lower hp hp2 (B d) (∑ e ∈ s, B e)
        (hB d (Finset.mem_insert_self _ _)) hsum
      have hrec := ih hs
      linarith only [hstep, hrec]

omit [Fintype D] in
theorem two_column_compression_sum_upper {p : ℝ} (hp : 2 ≤ p)
    (s : Finset D) (B : D → Matrix (Fin 2) (Fin 2) ℝ)
    (hB : ∀ d ∈ s, ∀ i j, 0 ≤ B d i j) :
    (∑ d ∈ s, compressionFunctional p (B d)) ≤ compressionFunctional p (∑ d ∈ s, B d) := by
  have hp0 : 0 < p := by linarith
  revert hB
  induction s using Finset.induction_on with
  | empty => intro _; simp [compressionFunctional_zero hp0]
  | @insert d s hd ih =>
      intro hB
      rw [Finset.sum_insert hd, Finset.sum_insert hd]
      have hs : ∀ e ∈ s, ∀ i j, 0 ≤ B e i j :=
        fun e he => hB e (Finset.mem_insert_of_mem he)
      have hsum : ∀ i j, 0 ≤ (∑ e ∈ s, B e) i j := by
        intro i j
        simp only [Matrix.sum_apply]
        exact Finset.sum_nonneg fun e he => hs e he i j
      have hstep := two_column_compression_upper hp (B d) (∑ e ∈ s, B e)
        (hB d (Finset.mem_insert_self _ _)) hsum
      have hrec := ih hs
      linarith only [hstep, hrec]

theorem two_column_diagonal_block_power_lower {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (z : Fin 2 → Fin 2 → D → ℂ) :
    schattenPower p (compression p z) ≤ schattenPower p (diagonalBlockMatrix z) := by
  have hp0 : 0 < p := by linarith
  rw [compression_eq_entryRoot_sum, diagonalBlockMatrix_schattenPower]
  let W : D → Matrix (Fin 2) (Fin 2) ℂ := fun d => Matrix.of (fun i j => z i j d)
  change compressionFunctional p
    (∑ d, entryPowers p (W d)) ≤ ∑ d, schattenPower p (W d)
  exact (two_column_compression_sum_lower hp hp2 Finset.univ
    (fun d => entryPowers p (W d))
    (fun d _ => entryPowers_nonnegative p _)).trans
    (Finset.sum_le_sum fun d _ => by
      rw [compressionFunctional_entryPowers hp0]
      exact phaseRemoval_power_lower hp0 hp2 _)

theorem two_column_diagonal_block_power_upper {p : ℝ} (hp : 2 ≤ p)
    (z : Fin 2 → Fin 2 → D → ℂ) :
    schattenPower p (diagonalBlockMatrix z) ≤ schattenPower p (compression p z) := by
  have hp0 : 0 < p := by linarith
  rw [compression_eq_entryRoot_sum, diagonalBlockMatrix_schattenPower]
  let W : D → Matrix (Fin 2) (Fin 2) ℂ := fun d => Matrix.of (fun i j => z i j d)
  change (∑ d, schattenPower p (W d)) ≤ compressionFunctional p
    (∑ d, entryPowers p (W d))
  exact (Finset.sum_le_sum fun d _ => by
    rw [compressionFunctional_entryPowers hp0]
    exact phaseRemoval_power_upper hp _).trans
    (two_column_compression_sum_upper hp Finset.univ
      (fun d => entryPowers p (W d))
      (fun d _ => entryPowers_nonnegative p _))

theorem two_column_diagonal_block_lower {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (z : Fin 2 → Fin 2 → D → ℂ) :
    schattenNorm p (compression p z) ≤ schattenNorm p (diagonalBlockMatrix z) := by
  unfold schattenNorm
  exact Real.rpow_le_rpow (schattenPower_nonneg p _)
    (two_column_diagonal_block_power_lower hp hp2 z) (by positivity)

theorem two_column_diagonal_block_upper {p : ℝ} (hp : 2 ≤ p)
    (z : Fin 2 → Fin 2 → D → ℂ) :
    schattenNorm p (diagonalBlockMatrix z) ≤ schattenNorm p (compression p z) := by
  unfold schattenNorm
  exact Real.rpow_le_rpow (schattenPower_nonneg p _)
    (two_column_diagonal_block_power_upper hp z) (by positivity)

end

end ResearchMain.DiagonalSchatten
