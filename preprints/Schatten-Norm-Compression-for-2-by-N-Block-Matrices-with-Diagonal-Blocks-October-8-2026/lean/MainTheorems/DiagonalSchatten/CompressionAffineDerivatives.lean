import MainTheorems.DiagonalSchatten.TwoColumnHessianSigns
import MainTheorems.DiagonalSchatten.FiniteExceptions
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise Topology

variable {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]

omit [DecidableEq J] [Nonempty J] in
theorem affineArray_hasDerivAt (B E : Matrix (Fin 2) J ℝ) (t : ℝ) :
    HasDerivAt (affineArray B E) E t := by
  change HasDerivAt (fun x : ℝ => B + x • E) E t
  convert! (hasDerivAt_const t B).add ((hasDerivAt_id t).smul_const E) using 1
  simp

omit [Fintype J] [DecidableEq J] [Nonempty J] in
theorem affineArray_positive_segment (B C : Matrix (Fin 2) J ℝ)
    (hB : ∀ i j, 0 < B i j) (hC : ∀ i j, 0 < C i j) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    ∀ i j, 0 < affineArray B (C - B) t i j := by
  intro i j
  change 0 < B i j + t * (C i j - B i j)
  have h1 : 0 ≤ 1 - t := by linarith [ht.2]
  by_cases h : t = 0
  · simpa [h] using hB i j
  · have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    have he := add_pos_of_nonneg_of_pos (mul_nonneg h1 (hB i j).le) (mul_pos ht0 (hC i j))
    nlinarith [he]

theorem contDiffAt_compressionFunctional_affine {p : ℝ} (hp : 1 < p)
    (B E : Matrix (Fin 2) J ℝ) (t : ℝ)
    (hB : ∀ i j, 0 < affineArray B E t i j) :
    ContDiffAt ℝ 1 (fun x => compressionFunctional p (affineArray B E x)) t := by
  exact (contDiffAt_compressionFunctional hp _ hB).comp t
    (show ContDiffAt ℝ 1 (affineArray B E) t by
      change ContDiffAt ℝ 1 (fun x : ℝ => B + x • E) t
      fun_prop)

theorem compressionFunctional_affine_deriv {p : ℝ} (hp : 1 < p)
    (B E : Matrix (Fin 2) J ℝ) (t : ℝ)
    (hB : ∀ i j, 0 < affineArray B E t i j) :
    deriv (fun x => compressionFunctional p (affineArray B E x)) t =
      fderiv ℝ (compressionFunctional p) (affineArray B E t) E := by
  have hd := (contDiffAt_compressionFunctional hp _ hB).differentiableAt (by norm_num)
  exact (hd.hasFDerivAt.comp_hasDerivAt t (affineArray_hasDerivAt B E t)).deriv

theorem compressionFunctional_affine_second_deriv {p : ℝ} (hp : 1 < p)
    (B E : Matrix (Fin 2) J ℝ) (t : ℝ)
    (hB : ∀ i j, 0 < affineArray B E t i j)
    (hdet : 0 < gramFirst (realEntryRoot p (affineArray B E t)) *
        gramSecond (realEntryRoot p (affineArray B E t)) -
      gramCross (realEntryRoot p (affineArray B E t)) ^ 2) :
    HasDerivAt (deriv (fun x => compressionFunctional p (affineArray B E x)))
      (compressionHessian p (affineArray B E t) E E) t := by
  have h2 := contDiffAt_compressionFunctional_fullRank (n := 2) (by linarith : 0 < p)
    (affineArray B E t) hB hdet
  have hD := (h2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hAlong := hD.hasFDerivAt.comp_hasDerivAt t (affineArray_hasDerivAt B E t)
  have hscalar := hAlong.clm_apply (hasDerivAt_const t E)
  have hlocal : ∀ᶠ x in 𝓝 t, ∀ i j, 0 < affineArray B E x i j :=
    (affineArray_hasDerivAt B E t).continuousAt.eventually (positive_arrays_open.mem_nhds hB)
  apply (show HasDerivAt (fun x =>
      fderiv ℝ (compressionFunctional p) (affineArray B E x) E)
      (compressionHessian p (affineArray B E t) E E) t by
    convert! hscalar using 1
    simp only [map_zero, add_zero, compressionHessian, Function.comp_def]
    rfl
    ).congr_of_eventuallyEq
  filter_upwards [hlocal] with x hx
  exact compressionFunctional_affine_deriv hp B E x hx

theorem compression_affine_convex_fullRank_start {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (B C : Matrix (Fin 2) (Fin 2) ℝ) (hB : ∀ i j, 0 < B i j)
    (hC : ∀ i j, 0 < C i j) (hminor : rowMinor B 0 1 ≠ 0) :
    ConvexOn ℝ (Set.Icc 0 1) (fun t => compressionFunctional p (affineArray B (C - B) t)) := by
  obtain ⟨s, _, hs⟩ := finite_rank_loss (by linarith : 0 < p) B (C - B) hminor
  apply convexOn_of_second_deriv_nonneg_off_finset s
  · exact ((continuous_compressionFunctional (by linarith : 0 < p)).comp
      (by unfold affineArray; fun_prop)).continuousOn
  · intro t ht
    exact (contDiffAt_compressionFunctional_affine hp B (C - B) t
      (affineArray_positive_segment B C hB hC ht)).differentiableAt (by norm_num)
  · intro t ht
    exact (contDiffAt_compressionFunctional_affine hp B (C - B) t
      (affineArray_positive_segment B C hB hC ht)).derivWithin (m := 0) (by norm_num)
      |>.continuousAt.continuousWithinAt
  · intro t ht hts
    have hpos := affineArray_positive_segment B C hB hC (Set.Ioo_subset_Icc_self ht)
    have hroot : (realEntryRoot p (affineArray B (C - B) t)).det ≠ 0 := by
      intro hz
      apply hts
      apply hs t hpos
      rw [twoByTwo_gramDet_eq_det_sq, hz, zero_pow (by decide)]
    have hgram : 0 < gramFirst (realEntryRoot p (affineArray B (C - B) t)) *
        gramSecond (realEntryRoot p (affineArray B (C - B) t)) -
      gramCross (realEntryRoot p (affineArray B (C - B) t)) ^ 2 := by
      rw [twoByTwo_gramDet_eq_det_sq]
      exact sq_pos_of_ne_zero hroot
    exact (compressionFunctional_affine_second_deriv hp B (C - B) t hpos hgram).differentiableAt
  · intro t ht hts
    have hpos := affineArray_positive_segment B C hB hC (Set.Ioo_subset_Icc_self ht)
    have hroot : (realEntryRoot p (affineArray B (C - B) t)).det ≠ 0 := by
      intro hz
      apply hts
      apply hs t hpos
      rw [twoByTwo_gramDet_eq_det_sq, hz, zero_pow (by decide)]
    have hgram : 0 < gramFirst (realEntryRoot p (affineArray B (C - B) t)) *
        gramSecond (realEntryRoot p (affineArray B (C - B) t)) -
      gramCross (realEntryRoot p (affineArray B (C - B) t)) ^ 2 := by
      rw [twoByTwo_gramDet_eq_det_sq]
      exact sq_pos_of_ne_zero hroot
    rw [(compressionFunctional_affine_second_deriv hp B (C - B) t hpos hgram).deriv]
    exact two_column_compressionHessian_nonneg hp hp2 _ _ hpos hroot

end

end ResearchMain.DiagonalSchatten
