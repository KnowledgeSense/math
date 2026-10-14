import MainTheorems.WishartBlocks.EigenvalueAssociation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace ResearchMain.WishartBlocks

open MeasureTheory
open scoped BigOperators ENNReal

theorem eigenvalueWeight_nonneg {n : ℕ} (α : ℝ) (lam : Fin n → ℝ) :
    0 ≤ eigenvalueWeight α lam := by
  apply chamberWeight_nonneg
  intro t ht
  exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le

theorem measurable_orderedPositive (n : ℕ) :
    MeasurableSet {lam : Fin n → ℝ | OrderedPositive lam} := by
  have hp : MeasurableSet {lam : Fin n → ℝ | ∀ i, 0 < lam i} := by
    simpa only [Set.ofPred_forall] using
      MeasurableSet.iInter (fun i : Fin n =>
        measurableSet_lt measurable_const (measurable_pi_apply i))
  have hm : MeasurableSet {lam : Fin n → ℝ | StrictMono lam} := by
    have hs (i j : Fin n) : MeasurableSet {lam : Fin n → ℝ | i < j → lam i < lam j} := by
      by_cases h : i < j
      · simpa only [h, true_implies] using
          measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)
      · simp only [h, false_implies, Set.ofPred_true, MeasurableSet.univ]
    simpa only [StrictMono, Set.ofPred_forall] using
      MeasurableSet.iInter (fun i : Fin n => MeasurableSet.iInter (fun j : Fin n => hs i j))
  exact hp.inter hm

theorem measurable_eigenvalueWeight {n : ℕ} (α : ℝ) :
    Measurable (eigenvalueWeight (n := n) α) := by
  classical
  change Measurable ({lam : Fin n → ℝ | OrderedPositive lam}.indicator
    (fun lam => (∏ i, lam i ^ ((α - n - 1) / 2) * Real.exp (-lam i / 2)) * gapProduct lam))
  apply Measurable.indicator _ (measurable_orderedPositive n)
  unfold gapProduct
  fun_prop

noncomputable def eigenvalueDensityLaw (n : ℕ) (c α : ℝ) : Measure (Fin n → ℝ) :=
  volume.withDensity (fun lam => ENNReal.ofReal (c * eigenvalueWeight α lam))

theorem eigenvalueDensityLaw_integral {n : ℕ} {c : ℝ} (hc : 0 ≤ c) (α : ℝ)
    (F : (Fin n → ℝ) → ℝ) :
    (∫ lam, F lam ∂eigenvalueDensityLaw n c α) =
      c * ∫ lam, eigenvalueWeight α lam * F lam := by
  unfold eigenvalueDensityLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun lam : Fin n → ℝ => ENNReal.ofReal (c * eigenvalueWeight α lam))
    ((measurable_const.mul (measurable_eigenvalueWeight α)).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) F]
  simp_rw [ENNReal.toReal_ofReal (mul_nonneg hc (eigenvalueWeight_nonneg α _)),
    smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

theorem eigenvalueDensityLaw_integrable_iff {n : ℕ} {c : ℝ} (hc : 0 < c) (α : ℝ)
    (F : (Fin n → ℝ) → ℝ) :
    Integrable F (eigenvalueDensityLaw n c α) ↔
      Integrable (fun lam => eigenvalueWeight α lam * F lam) := by
  unfold eigenvalueDensityLaw
  rw [integrable_withDensity_iff_integrable_smul₀'
    (f := fun lam : Fin n → ℝ => ENNReal.ofReal (c * eigenvalueWeight α lam))
    (g := F)
    ((measurable_const.mul (measurable_eigenvalueWeight α)).ennreal_ofReal.aemeasurable)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (mul_nonneg hc.le (eigenvalueWeight_nonneg α _)),
    smul_eq_mul, mul_assoc]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc.ne') _

theorem eigenvalueDensityLaw_association {n : ℕ} {c : ℝ} (hc : 0 < c) (α : ℝ)
    [IsProbabilityMeasure (eigenvalueDensityLaw n c α)]
    {F G : (Fin n → ℝ) → ℝ}
    (hcF : Continuous F) (hcG : Continuous G)
    (hF : ∀ lam, 0 ≤ F lam) (hG : ∀ lam, 0 ≤ G lam)
    (hmF : Monotone F) (hmG : Monotone G)
    (hiF : Integrable F (eigenvalueDensityLaw n c α))
    (hiG : Integrable G (eigenvalueDensityLaw n c α))
    (hiFG : Integrable (fun lam => F lam * G lam) (eigenvalueDensityLaw n c α)) :
    (∫ lam, F lam ∂eigenvalueDensityLaw n c α) *
        (∫ lam, G lam ∂eigenvalueDensityLaw n c α) ≤
      ∫ lam, F lam * G lam ∂eigenvalueDensityLaw n c α := by
  have hi1 : Integrable (fun _ : Fin n → ℝ => (1 : ℝ)) (eigenvalueDensityLaw n c α) :=
    integrable_const _
  have hiμ : Integrable (eigenvalueWeight (n := n) α) := by
    simpa only [mul_one] using (eigenvalueDensityLaw_integrable_iff hc α _).mp hi1
  have hn : c * (∫ lam : Fin n → ℝ, eigenvalueWeight α lam) = 1 := by
    have h := eigenvalueDensityLaw_integral (n := n) hc.le α (fun _ => (1 : ℝ))
    simpa only [mul_one, integral_const, probReal_univ, one_smul] using h.symm
  have h := eigenvalue_association α hcF hcG hF hG hmF hmG hiμ
    ((eigenvalueDensityLaw_integrable_iff hc α _).mp hiF)
    ((eigenvalueDensityLaw_integrable_iff hc α _).mp hiG)
    ((eigenvalueDensityLaw_integrable_iff hc α _).mp hiFG)
  simp only [eigenvalueDensityLaw_integral hc.le]
  calc
    _ = (c * c) * ((∫ lam, eigenvalueWeight α lam * F lam) *
        (∫ lam, eigenvalueWeight α lam * G lam)) := by ring
    _ ≤ (c * c) * ((∫ lam : Fin n → ℝ, eigenvalueWeight α lam) *
        (∫ lam, eigenvalueWeight α lam * (F lam * G lam))) :=
      mul_le_mul_of_nonneg_left h (mul_self_nonneg c)
    _ = (c * (∫ lam : Fin n → ℝ, eigenvalueWeight α lam)) *
        (c * ∫ lam, eigenvalueWeight α lam * (F lam * G lam)) := by ring
    _ = _ := by rw [hn, one_mul]

end ResearchMain.WishartBlocks
