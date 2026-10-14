import MainTheorems.DiagonalSchatten.FiniteCompression
import MainTheorems.DiagonalSchatten.FourthPower

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators

variable {J D : Type*} [Fintype J] [Fintype D] [DecidableEq J] [DecidableEq D]

omit [Fintype D] in
theorem finite_compression_sum_lower {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (s : Finset D) (B : D → Matrix (Fin 2) J ℝ)
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
      have hstep := finite_compression_lower hp hp2 (B d) (∑ e ∈ s, B e)
        (hB d (Finset.mem_insert_self _ _)) hsum
      have hrec := ih hs
      linarith only [hstep, hrec]

omit [Fintype D] in
theorem finite_compression_sum_upper_below_four {p : ℝ} (hp : 2 ≤ p) (hp4 : p < 4)
    (s : Finset D) (B : D → Matrix (Fin 2) J ℝ)
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
      have hstep := finite_compression_upper_below_four hp hp4 (B d) (∑ e ∈ s, B e)
        (hB d (Finset.mem_insert_self _ _)) hsum
      have hrec := ih hs
      linarith only [hstep, hrec]

theorem finite_diagonal_block_power_lower {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (z : Fin 2 → J → D → ℂ) :
    schattenPower p (compression p z) ≤ schattenPower p (diagonalBlockMatrix z) := by
  have hp0 : 0 < p := by linarith
  rw [compression_eq_entryRoot_sum, diagonalBlockMatrix_schattenPower]
  let W : D → Matrix (Fin 2) J ℂ := fun d => Matrix.of (fun i j => z i j d)
  change compressionFunctional p
    (∑ d, entryPowers p (W d)) ≤ ∑ d, schattenPower p (W d)
  exact (finite_compression_sum_lower hp hp2 Finset.univ
    (fun d => entryPowers p (W d))
    (fun d _ => entryPowers_nonnegative p _)).trans
    (Finset.sum_le_sum fun d _ => by
      rw [compressionFunctional_entryPowers hp0]
      exact phaseRemoval_power_lower hp0 hp2 _)

theorem finite_diagonal_block_power_upper_below_four {p : ℝ} (hp : 2 ≤ p) (hp4 : p < 4)
    (z : Fin 2 → J → D → ℂ) :
    schattenPower p (diagonalBlockMatrix z) ≤ schattenPower p (compression p z) := by
  have hp0 : 0 < p := by linarith
  rw [compression_eq_entryRoot_sum, diagonalBlockMatrix_schattenPower]
  let W : D → Matrix (Fin 2) J ℂ := fun d => Matrix.of (fun i j => z i j d)
  change (∑ d, schattenPower p (W d)) ≤ compressionFunctional p
    (∑ d, entryPowers p (W d))
  exact (Finset.sum_le_sum fun d _ => by
    rw [compressionFunctional_entryPowers hp0]
    exact phaseRemoval_power_upper hp _).trans
    (finite_compression_sum_upper_below_four hp hp4 Finset.univ
      (fun d => entryPowers p (W d))
      (fun d _ => entryPowers_nonnegative p _))

theorem finite_diagonal_block_lower {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (z : Fin 2 → J → D → ℂ) :
    schattenNorm p (compression p z) ≤ schattenNorm p (diagonalBlockMatrix z) := by
  unfold schattenNorm
  exact Real.rpow_le_rpow (schattenPower_nonneg p _)
    (finite_diagonal_block_power_lower hp hp2 z) (by positivity)

theorem finite_diagonal_block_upper_below_four {p : ℝ} (hp : 2 ≤ p) (hp4 : p < 4)
    (z : Fin 2 → J → D → ℂ) :
    schattenNorm p (diagonalBlockMatrix z) ≤ schattenNorm p (compression p z) := by
  unfold schattenNorm
  exact Real.rpow_le_rpow (schattenPower_nonneg p _)
    (finite_diagonal_block_power_upper_below_four hp hp4 z) (by positivity)

theorem finite_diagonal_block_power_upper_to_four {p : ℝ} (hp : 2 ≤ p) (hp4 : p ≤ 4)
    (z : Fin 2 → J → D → ℂ) :
    schattenPower p (diagonalBlockMatrix z) ≤ schattenPower p (compression p z) := by
  rcases eq_or_lt_of_le hp4 with h | h
  · subst p
    exact diagonal_compression_four_power z
  · exact finite_diagonal_block_power_upper_below_four hp h z

theorem finite_diagonal_block_upper_to_four {p : ℝ} (hp : 2 ≤ p) (hp4 : p ≤ 4)
    (z : Fin 2 → J → D → ℂ) :
    schattenNorm p (diagonalBlockMatrix z) ≤ schattenNorm p (compression p z) := by
  unfold schattenNorm
  exact Real.rpow_le_rpow (schattenPower_nonneg p _)
    (finite_diagonal_block_power_upper_to_four hp hp4 z) (by positivity)

end

end ResearchMain.DiagonalSchatten
