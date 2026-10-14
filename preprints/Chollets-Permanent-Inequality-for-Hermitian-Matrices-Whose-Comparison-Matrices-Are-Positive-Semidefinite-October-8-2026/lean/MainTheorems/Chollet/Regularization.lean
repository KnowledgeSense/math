import MainTheorems.Chollet.Comparison
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

namespace ResearchMain.Chollet

open Matrix Filter
open scoped Topology

variable {I : Type*} [Fintype I] [DecidableEq I]

def ComparisonPD (A : Matrix I I ℂ) : Prop := A.IsHermitian ∧ (comparison A).PosDef

def regularize (A : Matrix I I ℂ) (ε : ℝ) : Matrix I I ℂ :=
  A + diagonal (fun _ => (ε : ℂ))

omit [Fintype I] in
theorem ComparisonPD.toPSD {A : Matrix I I ℂ} (hA : ComparisonPD A) : ComparisonPSD A :=
  ⟨hA.1, hA.2.posSemidef⟩

omit [Fintype I] in
theorem regularize_comparison (A : Matrix I I ℂ) (ε : ℝ) :
    comparison (regularize A ε) = comparison A + diagonal (fun _ => ε) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [regularize, comparison, Complex.add_re]
  · simp [regularize, comparison, hij]

omit [Fintype I] in
theorem regularize_hermitian {A : Matrix I I ℂ} (hA : A.IsHermitian) (ε : ℝ) :
    (regularize A ε).IsHermitian := by
  apply hA.add
  apply isHermitian_diagonal_iff.mpr
  intro i
  simp [IsSelfAdjoint]

omit [Fintype I] in
theorem ComparisonPSD.regularize_positive {A : Matrix I I ℂ} (hA : ComparisonPSD A)
    (ε : ℝ) (hε : 0 < ε) : ComparisonPD (regularize A ε) := by
  refine ⟨regularize_hermitian hA.1 ε, ?_⟩
  rw [regularize_comparison]
  exact PosDef.posSemidef_add hA.2 (PosDef.diagonal (fun _ => hε))

theorem permanent_continuous : Continuous (fun A : Matrix I I ℂ => A.permanent) := by
  change Continuous (fun A : Matrix I I ℂ => ∑ π : Equiv.Perm I, ∏ i, A (π i) i)
  fun_prop

theorem squaredPermanent_continuous :
    Continuous (fun A : Matrix I I ℂ => (squaredEntries A).permanent) := by
  change Continuous (fun A : Matrix I I ℂ => ∑ π : Equiv.Perm I, ∏ i, ‖A (π i) i‖ ^ 2)
  fun_prop

omit [Fintype I] in
theorem regularize_continuous (A : Matrix I I ℂ) : Continuous (regularize A) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hij : i = j
  · simp only [regularize, Matrix.add_apply, diagonal_apply, hij, ite_true]
    fun_prop
  · simp only [regularize, Matrix.add_apply, diagonal_apply, hij, ite_false, add_zero]
    exact continuous_const

omit [Fintype I] in
theorem regularize_zero (A : Matrix I I ℂ) : regularize A 0 = A := by
  simp [regularize]

theorem square_bound_by_positive_approximation (A : Matrix I I ℂ) (hA : ComparisonPSD A)
    (hpositive : ∀ B : Matrix I I ℂ, ComparisonPD B →
      (squaredEntries B).permanent ≤ B.permanent.re ^ 2) :
    (squaredEntries A).permanent ≤ A.permanent.re ^ 2 := by
  have hc : Continuous (fun ε : ℝ =>
      (squaredEntries (regularize A ε)).permanent - (regularize A ε).permanent.re ^ 2) :=
    (squaredPermanent_continuous.comp (regularize_continuous A)).sub
      ((Complex.continuous_re.comp
        (permanent_continuous.comp (regularize_continuous A))).pow 2)
  have ht := hc.tendsto 0 |>.comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hle : ∀ n : ℕ,
      (squaredEntries (regularize A (1 / ((n : ℝ) + 1)))).permanent -
        (regularize A (1 / ((n : ℝ) + 1))).permanent.re ^ 2 ≤ 0 := by
    intro n
    apply sub_nonpos.mpr
    apply hpositive
    apply hA.regularize_positive
    positivity
  have h := le_of_tendsto ht (Eventually.of_forall hle)
  simpa only [regularize_zero, sub_nonpos] using h

end ResearchMain.Chollet
