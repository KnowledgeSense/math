import MainTheorems.WishartBlocks.DampedDifferentialUniqueness
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Topology.Algebra.ConstMulAction

namespace ResearchMain.WishartBlocks

open Filter MeasureTheory
open scoped Topology BigOperators SchwartzMap ContDiff

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def unitCutoff : ContDiffBump (0 : E) := ⟨1, 2, zero_lt_one, one_lt_two⟩

noncomputable def expandingCutoff (N : ℕ) (x : E) : ℝ :=
  (unitCutoff (E := E)) (((N : ℝ) + 1)⁻¹ • x)

theorem expandingCutoff_contDiff (N : ℕ) : ContDiff ℝ ∞ (expandingCutoff (E := E) N) :=
  (unitCutoff (E := E)).contDiff.comp (contDiff_const.smul contDiff_id)

theorem expandingCutoff_compact (N : ℕ) :
    HasCompactSupport (expandingCutoff (E := E) N) :=
  (unitCutoff (E := E)).hasCompactSupport.comp_smul (inv_ne_zero (by positivity))

theorem expandingCutoff_bounds (N : ℕ) (x : E) :
    0 ≤ expandingCutoff N x ∧ expandingCutoff N x ≤ 1 :=
  ⟨(unitCutoff (E := E)).nonneg, (unitCutoff (E := E)).le_one⟩

theorem expandingCutoff_eventually_one (x : E) :
    ∀ᶠ N : ℕ in atTop, expandingCutoff N =ᶠ[𝓝 x] 1 := by
  obtain ⟨M, hM⟩ := exists_nat_gt ‖x‖
  filter_upwards [eventually_ge_atTop M] with N hN
  have hc : 0 < (N : ℝ) + 1 := by positivity
  have hx : ((N : ℝ) + 1)⁻¹ • x ∈ Metric.ball 0 (unitCutoff (E := E)).rIn := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hc.le)]
    change ((N : ℝ) + 1)⁻¹ * ‖x‖ < 1
    rw [inv_mul_lt_iff₀ hc]
    have hMN : (M : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have h := (unitCutoff (E := E)).eventuallyEq_one_of_mem_ball hx
  exact ((by fun_prop : Continuous (fun y : E => ((N : ℝ) + 1)⁻¹ • y)).continuousAt).eventually h

theorem expandingCutoff_derivative_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ x : E,
      ‖iteratedFDeriv ℝ k (expandingCutoff N) x‖ ≤ C := by
  let φ : 𝓢(E, ℝ) := (unitCutoff (E := E)).hasCompactSupport.toSchwartzMap
    (unitCutoff (E := E)).contDiff
  have hφ : (φ : E → ℝ) = (unitCutoff (E := E)) := rfl
  obtain ⟨C, hC, hbound⟩ := φ.decay 0 k
  refine ⟨C, hC, ?_⟩
  intro N x
  have hc : 0 ≤ ((N : ℝ) + 1)⁻¹ := by positivity
  have hc1 : ((N : ℝ) + 1)⁻¹ ≤ 1 := by
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    exact (inv_le_one₀ (by positivity)).mpr (by linarith)
  unfold expandingCutoff
  rw [iteratedFDeriv_comp_const_smul _ (unitCutoff (E := E)).contDiff, norm_smul,
    Real.norm_of_nonneg (pow_nonneg hc k)]
  calc
    _ ≤ 1 * ‖iteratedFDeriv ℝ k (unitCutoff (E := E)) (((N : ℝ) + 1)⁻¹ • x)‖ := by
      gcongr
      exact pow_le_one₀ hc hc1
    _ ≤ C := by simpa only [pow_zero, one_mul, hφ] using hbound (((N : ℝ) + 1)⁻¹ • x)

omit [FiniteDimensional ℝ E] in
theorem functionDirections_contDiff {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (L : List E) :
    ContDiff ℝ ∞ (functionDirections L f) := by
  induction L with
  | nil => exact hf
  | cons u L ih =>
      have he : functionDirections (u :: L) f =
          fun x => fderiv ℝ (functionDirections L f) x u := by
        funext x
        exact (ih.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv
      rw [he]
      exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

omit [FiniteDimensional ℝ E] in
theorem functionDirections_iteratedFDeriv {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (L : List E) (x : E) :
    functionDirections L f x =
      iteratedFDeriv ℝ L.length f x (fun i => L.get i) := by
  induction L generalizing x with
  | nil => simp [functionDirections]
  | cons u L ih =>
      have he : functionDirections L f =
          fun y => iteratedFDeriv ℝ L.length f y (fun i => L.get i) := funext ih
      have hD : DifferentiableAt ℝ (iteratedFDeriv ℝ L.length f) x :=
        hf.contDiffAt.differentiableAt_iteratedFDeriv
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl L.length)
      change lineDeriv ℝ (functionDirections L f) x u = _
      rw [he, (hD.continuousMultilinear_apply_const _).lineDeriv_eq_fderiv]
      have hm : Fin.tail (fun i : Fin (L.length + 1) => (u :: L).get i) =
          fun i => L.get i := by
        funext i
        simp [Fin.tail_def]
      have h := hD.iteratedFDeriv_succ_apply_left'
        (m := fun i : Fin (L.length + 1) => (u :: L).get i)
      simpa only [List.length_cons, hm, List.get_cons_zero] using h.symm

omit [FiniteDimensional ℝ E] in
theorem functionDirections_norm {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (L : List E) (x : E) :
    ‖functionDirections L f x‖ ≤
      ‖iteratedFDeriv ℝ L.length f x‖ * ∏ i : Fin L.length, ‖L.get i‖ := by
  rw [functionDirections_iteratedFDeriv hf]
  exact (iteratedFDeriv ℝ L.length f x).le_opNorm _

omit [FiniteDimensional ℝ E] in
theorem functionDirections_eventuallyEq {f g : E → ℂ} {x : E}
    (h : f =ᶠ[𝓝 x] g) (L : List E) :
    functionDirections L f =ᶠ[𝓝 x] functionDirections L g := by
  induction L with
  | nil => exact h
  | cons u L ih =>
      filter_upwards [eventually_eventuallyEq_nhds.mpr ih] with y hy
      exact hy.lineDeriv_eq

noncomputable def compactApproximation (N : ℕ) (f : E → ℂ) (x : E) : ℂ :=
  expandingCutoff N x • f x

theorem compactApproximation_contDiff (N : ℕ) {f : E → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (compactApproximation N f) :=
  (expandingCutoff_contDiff N).smul hf

theorem compactApproximation_compact (N : ℕ) (f : E → ℂ) :
    HasCompactSupport (compactApproximation N f) :=
  (expandingCutoff_compact N).smul_right

theorem compactApproximation_eventuallyEq (f : E → ℂ) (x : E) :
    ∀ᶠ N : ℕ in atTop, compactApproximation N f =ᶠ[𝓝 x] f := by
  filter_upwards [expandingCutoff_eventually_one x] with N hN
  filter_upwards [hN] with y hy
  simp only [compactApproximation, hy, Pi.one_apply, one_smul]

theorem compactApproximation_directions_tendsto (f : E → ℂ) (L : List E) (x : E) :
    Tendsto (fun N : ℕ => functionDirections L (compactApproximation N f) x)
      atTop (𝓝 (functionDirections L f x)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [compactApproximation_eventuallyEq f x] with N hN
  exact (functionDirections_eventuallyEq hN L).eq_of_nhds.symm

theorem compactApproximation_jet_bound {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (C : ℕ → ℝ) (hC : ∀ k N (x : E), ‖iteratedFDeriv ℝ k (expandingCutoff N) x‖ ≤ C k)
    (N n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (compactApproximation N f) x‖ ≤
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * C k *
        ‖iteratedFDeriv ℝ (n - k) f x‖ := by
  apply (norm_iteratedFDeriv_smul_le (expandingCutoff_contDiff N) hf x (by simp)).trans
  apply Finset.sum_le_sum
  intro k _
  gcongr
  exact hC k N x

end
end ResearchMain.WishartBlocks
