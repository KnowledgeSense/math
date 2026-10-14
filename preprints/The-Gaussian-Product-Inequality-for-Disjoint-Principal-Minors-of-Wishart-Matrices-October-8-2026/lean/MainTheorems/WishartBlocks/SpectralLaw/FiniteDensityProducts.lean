import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity

namespace ResearchMain.WishartBlocks

open MeasureTheory
open scoped BigOperators ENNReal

theorem lintegral_fin_product {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ∫⁻ x : E 0 × ((i : Fin n) → E i.succ),
          f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i)
          ∂((μ 0).prod (Measure.pi fun i => μ i.succ)) := by
        rw [← (measurePreserving_piFinSuccAbove μ 0).symm.lintegral_comp_emb
          (MeasurableEquiv.measurableEmbedding _)]
        simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.prod_univ_succ, Fin.insertNth_zero]
        simp only [Fin.zero_succAbove]
        apply lintegral_congr
        intro x
        rfl
      _ = (∫⁻ x, f 0 x ∂μ 0) *
          ∏ i : Fin n, ∫⁻ x, f i.succ x ∂μ i.succ := by
        rw [lintegral_prod_mul (μ := μ 0) (ν := Measure.pi fun i : Fin n => μ i.succ)
          (f := f 0) (g := fun x : (i : Fin n) → E i.succ => ∏ i, f i.succ (x i))
          (hf 0).aemeasurable
          (Finset.measurable_prod _ fun i _ =>
            (hf i.succ).comp (measurable_pi_apply i)).aemeasurable]
        rw [ih _ (fun i => hf i.succ)]
      _ = _ := by rw [Fin.prod_univ_succ]

theorem lintegral_finite_product {I : Type*} [Fintype I]
    {E : I → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : I) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : I) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : (i : I) → E i, ∏ i, f i (x i) ∂Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  classical
  let e := (Fintype.equivFin I).symm
  rw [← (measurePreserving_piCongrLeft μ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_product _ (fun i => hf _)

theorem product_indicators {I : Type*} [Fintype I]
    {E : I → Type*} (s : (i : I) → Set (E i)) (f : (i : I) → E i → ℝ≥0∞)
    (x : (i : I) → E i) :
    (∏ i, (s i).indicator (f i) (x i)) =
      (Set.pi Set.univ s).indicator (fun y => ∏ i, f i (y i)) x := by
  classical
  by_cases hx : ∀ i, x i ∈ s i
  · rw [Set.indicator_of_mem (Set.mem_univ_pi.mpr hx)]
    apply Finset.prod_congr rfl
    intro i _
    exact Set.indicator_of_mem (hx i) _
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    rw [Set.indicator_of_notMem (by simpa only [Set.mem_univ_pi] using hx)]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

theorem pi_withDensity_finite {I : Type*} [Fintype I]
    {E : I → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    (μ : (i : I) → Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (f : (i : I) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  calc
    (∫⁻ x in Set.pi Set.univ s, ∏ i, f i (x i) ∂Measure.pi μ) =
        ∫⁻ x, ∏ i, (s i).indicator (f i) (x i) ∂Measure.pi μ := by
      simp_rw [product_indicators]
      exact (lintegral_indicator (MeasurableSet.univ_pi hs) _).symm
    _ = ∏ i, ∫⁻ x in s i, f i x ∂μ i := by
      rw [lintegral_finite_product _ (fun i => (hf i).indicator (hs i))]
      simp_rw [lintegral_indicator (hs _)]
    _ = ∏ i, (μ i).withDensity (f i) (s i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact (withDensity_apply _ (hs i)).symm

end ResearchMain.WishartBlocks
