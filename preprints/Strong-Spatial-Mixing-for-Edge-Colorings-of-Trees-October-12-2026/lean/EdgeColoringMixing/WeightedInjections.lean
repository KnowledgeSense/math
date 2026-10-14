import EdgeColoringMixing.FiniteProbability
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-! Weighted injections use the exact product weights of the release. -/
namespace EdgeColoringMixing
open Finset

/-- The finite sample space of injections of rows into colors. -/
abbrev Injection (d q : ℕ) := Fin d ↪ Fin q

namespace WeightedInjection

variable {d q : ℕ}

noncomputable def weight (W : Fin d → Fin q → ℝ) (σ : Injection d q) : ℝ :=
  ∏ i, W i (σ i)

noncomputable def partition (W : Fin d → Fin q → ℝ) : ℝ :=
  ∑ σ : Injection d q, weight W σ

/-- Entry bounds and the exact row-surplus condition from the paper. -/
structure RowSurplus (W : Fin d → Fin q → ℝ) (s : ℝ) : Prop where
  positive : 0 < s
  nonneg : ∀ i c, 0 ≤ W i c
  le_one : ∀ i c, W i c ≤ 1
  row_mass : ∀ i, (d : ℝ) + s ≤ ∑ c, W i c

theorem weight_nonneg (W : Fin d → Fin q → ℝ) (hW : ∀ i c, 0 ≤ W i c)
    (σ : Injection d q) : 0 ≤ weight W σ :=
  Finset.prod_nonneg (fun i _ => hW i (σ i))

theorem partition_nonneg (W : Fin d → Fin q → ℝ) (hW : ∀ i c, 0 ≤ W i c) :
    0 ≤ partition W :=
  Finset.sum_nonneg (fun σ _ => weight_nonneg W hW σ)

/-- Surplus supplies a genuine injection of positive weight, by finite Hall marriage. -/
theorem exists_positive_weight (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) : ∃ σ : Injection d q, 0 < weight W σ := by
  classical
  let support : Fin d → Finset (Fin q) := fun i => univ.filter (fun c => 0 < W i c)
  have hcard (i : Fin d) : d ≤ (support i).card := by
    have hmass : ∑ c, W i c ≤ ((support i).card : ℝ) := by
      calc
        ∑ c, W i c = ∑ c ∈ support i, W i c := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro c _ hc
          have : ¬0 < W i c := by simpa [support] using hc
          exact le_antisymm (le_of_not_gt this) (hW.nonneg i c)
        _ ≤ ∑ _c ∈ support i, (1 : ℝ) :=
          Finset.sum_le_sum (fun c _ => hW.le_one i c)
        _ = ((support i).card : ℝ) := by simp
    have : (d : ℝ) ≤ ((support i).card : ℝ) :=
      le_trans (le_add_of_nonneg_right hW.positive.le) ((hW.row_mass i).trans hmass)
    exact_mod_cast this
  have hhall (S : Finset (Fin d)) : S.card ≤ (S.biUnion support).card := by
    by_cases hS : S.Nonempty
    · obtain ⟨i, hi⟩ := hS
      calc
        S.card ≤ d := by simpa using Finset.card_le_univ S
        _ ≤ (support i).card := hcard i
        _ ≤ (S.biUnion support).card := Finset.card_le_card (Finset.subset_biUnion_of_mem _ hi)
    · simp [Finset.not_nonempty_iff_eq_empty.mp hS]
  obtain ⟨f, hf, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' support).mp hhall
  refine ⟨⟨f, hf⟩, Finset.prod_pos fun i _ => ?_⟩
  simpa [support] using hmem i

/-- The normalizing constant is strictly positive; this is not assumed from the surplus. -/
theorem partition_pos (W : Fin d → Fin q → ℝ) {s : ℝ} (hW : RowSurplus W s) :
    0 < partition W := by
  obtain ⟨σ, hσ⟩ := exists_positive_weight W hW
  exact hσ.trans_le (Finset.single_le_sum (fun τ _ => weight_nonneg W hW.nonneg τ)
    (Finset.mem_univ σ))

/-- The actual normalized weighted-injection measure. -/
noncomputable def law (W : Fin d → Fin q → ℝ) (hW : ∀ i c, 0 ≤ W i c)
    (hZ : 0 < partition W) : FiniteLaw (Injection d q) where
  mass σ := weight W σ / partition W
  nonneg σ := div_nonneg (weight_nonneg W hW σ) hZ.le
  sum_one := by rw [← Finset.sum_div]; exact div_self hZ.ne'

/-- The indicator of a cell being occupied by the injection. -/
noncomputable def cell (i : Fin d) (c : Fin q) (σ : Injection d q) : ℝ :=
  if σ i = c then 1 else 0

noncomputable def mean (μ : FiniteLaw (Injection d q)) (i : Fin d) (c : Fin q) : ℝ :=
  μ.expectation (cell i c)

noncomputable def covariance (μ : FiniteLaw (Injection d q)) :
    Matrix (Fin d × Fin q) (Fin d × Fin q) ℝ :=
  fun x y => μ.covariance (cell x.1 x.2) (cell y.1 y.2)

@[simp] theorem cell_nonneg (i : Fin d) (c : Fin q) (σ : Injection d q) :
    0 ≤ cell i c σ := by simp [cell]; split <;> norm_num

@[simp] theorem cell_le_one (i : Fin d) (c : Fin q) (σ : Injection d q) :
    cell i c σ ≤ 1 := by simp [cell]; split <;> norm_num

@[simp] theorem cell_sq (i : Fin d) (c : Fin q) (σ : Injection d q) :
    cell i c σ ^ 2 = cell i c σ := by simp [cell]

@[simp] theorem row_sum (i : Fin d) (σ : Injection d q) :
    ∑ c, cell i c σ = 1 := by simp [cell]

theorem mean_nonneg (μ : FiniteLaw (Injection d q)) (i : Fin d) (c : Fin q) :
    0 ≤ mean μ i c := μ.expectation_nonneg (cell_nonneg i c)

theorem mean_le_one (μ : FiniteLaw (Injection d q)) (i : Fin d) (c : Fin q) :
    mean μ i c ≤ 1 := by
  exact (μ.expectation_mono (cell_le_one i c)).trans_eq (μ.expectation_const 1)

@[simp] theorem mean_row_sum (μ : FiniteLaw (Injection d q)) (i : Fin d) :
    ∑ c, mean μ i c = 1 := by
  simp only [mean]
  rw [← FiniteLaw.expectation_sum]
  simp

theorem cell_mul_same_color {i j : Fin d} (hij : i ≠ j) (c : Fin q)
    (σ : Injection d q) : cell i c σ * cell j c σ = 0 := by
  unfold cell
  split_ifs with hi hj
  · exact False.elim (hij (σ.injective (hi.trans hj.symm)))
  all_goals ring

theorem cell_mul_same_row (i : Fin d) {c b : Fin q} (hcb : c ≠ b)
    (σ : Injection d q) : cell i c σ * cell i b σ = 0 := by
  unfold cell
  split_ifs with hc hb
  · exact False.elim (hcb (hc.symm.trans hb))
  all_goals ring

/-- The negative same-color blocks are exact, before any estimates. -/
theorem covariance_same_color (μ : FiniteLaw (Injection d q)) {i j : Fin d}
    (hij : i ≠ j) (c : Fin q) :
    covariance μ (i, c) (j, c) = -(mean μ i c * mean μ j c) := by
  rw [covariance, FiniteLaw.covariance_eq_mixed_moment]
  simp [cell_mul_same_color hij, mean]

theorem covariance_same_row (μ : FiniteLaw (Injection d q)) (i : Fin d)
    {c b : Fin q} (hcb : c ≠ b) :
    covariance μ (i, c) (i, b) = -(mean μ i c * mean μ i b) := by
  rw [covariance, FiniteLaw.covariance_eq_mixed_moment]
  simp [cell_mul_same_row i hcb, mean]

theorem covariance_diagonal (μ : FiniteLaw (Injection d q)) (i : Fin d) (c : Fin q) :
    covariance μ (i, c) (i, c) = mean μ i c - mean μ i c ^ 2 := by
  rw [covariance, FiniteLaw.covariance_self, FiniteLaw.variance_eq_second_moment]
  simp [mean]

/-- Covariance is a sum of nonnegative weighted rank-one matrices. -/
theorem covariance_posSemidef (μ : FiniteLaw (Injection d q)) :
    (covariance μ).PosSemidef := by
  let v : Injection d q → (Fin d × Fin q) → ℝ :=
    fun σ x => cell x.1 x.2 σ - mean μ x.1 x.2
  have hrepr : covariance μ = ∑ σ, μ.mass σ • Matrix.vecMulVec (v σ) (v σ) := by
    ext x y
    simp [covariance, FiniteLaw.covariance, FiniteLaw.expectation, Matrix.vecMulVec,
      v, mean, Matrix.sum_apply]
  rw [hrepr]
  apply Matrix.posSemidef_sum
  intro σ _
  have h := Matrix.posSemidef_vecMulVec_self_star (v σ)
  exact (by simpa using h : (Matrix.vecMulVec (v σ) (v σ)).PosSemidef).smul (μ.nonneg σ)

/-- Every row has exactly one occupied cell, so its covariance row sum vanishes. -/
theorem covariance_row_sum (μ : FiniteLaw (Injection d q)) (x : Fin d × Fin q)
    (j : Fin d) : ∑ c, covariance μ x (j, c) = 0 := by
  simp only [covariance, FiniteLaw.covariance_eq_mixed_moment, Finset.sum_sub_distrib]
  rw [← FiniteLaw.expectation_sum, ← Finset.mul_sum]
  have hsum (σ : Injection d q) :
      ∑ c, cell x.1 x.2 σ * cell j c σ = cell x.1 x.2 σ := by
    rw [← Finset.mul_sum, row_sum, mul_one]
  simp only [hsum]
  change μ.expectation (cell x.1 x.2) - μ.expectation (cell x.1 x.2) *
    (∑ c, mean μ j c) = 0
  rw [mean_row_sum]
  ring

/-- Total mass of the mean vector is the number of rows. -/
theorem mean_total (μ : FiniteLaw (Injection d q)) :
    ∑ x : Fin d × Fin q, mean μ x.1 x.2 = d := by
  rw [Fintype.sum_prod_type]
  simp

theorem covariance_total (μ : FiniteLaw (Injection d q)) (x : Fin d × Fin q) :
    ∑ y, covariance μ x y = 0 := by
  rw [Fintype.sum_prod_type]
  simp [covariance_row_sum]

end WeightedInjection
end EdgeColoringMixing
