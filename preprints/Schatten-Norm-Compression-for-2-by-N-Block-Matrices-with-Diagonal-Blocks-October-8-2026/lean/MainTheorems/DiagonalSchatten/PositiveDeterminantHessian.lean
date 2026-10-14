import MainTheorems.DiagonalSchatten.ChartHessianKernel
import MainTheorems.DiagonalSchatten.HessianHomogeneity

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped Matrix.Norms.Elementwise

theorem realEntryPowers_realEntryRoot {J : Type*} {p : ℝ} (hp : p ≠ 0)
    (B : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 ≤ B i j) :
    realEntryPowers p (realEntryRoot p B) = B := by
  ext i j
  change (B i j ^ (1 / p)) ^ p = B i j
  rw [← Real.rpow_mul (hB i j), one_div_mul_cancel hp, Real.rpow_one]

theorem positive_determinant_compressionHessian_kernel {p : ℝ}
    (hp : 1 < p) (hp2 : p ≠ 2) (B : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : ∀ i j, 0 < B i j) (hdet : 0 < (realEntryRoot p B).det)
    (E : Matrix (Fin 2) (Fin 2) ℝ) (hE : compressionHessian p B E = 0) :
    ∃ r : ℝ, E = r • B := by
  let M := realEntryRoot p B
  have hM : ∀ i j, 0 < M i j := fun i j => Real.rpow_pos_of_pos (hB i j) _
  obtain ⟨L, t, w, h, hL, ht, hw, hh, hh1, he⟩ := positive_two_by_two_rationalSVD M hM hdet
  have hcore : ∀ i j, 0 < rationalSVDCore t w h i j := by
    intro i j
    have hm := hM i j
    rw [he] at hm
    exact pos_of_mul_pos_right hm hL.le
  let A := rationalSVDPowers p h t w
  let s := L ^ p
  have hs : 0 < s := Real.rpow_pos_of_pos hL _
  have hA : ∀ i j, 0 < A i j := rationalSVDPowers_positive hcore
  have hroot : realEntryRoot p A = rationalSVDCore t w h :=
    realEntryRoot_realEntryPowers (by linarith : p ≠ 0) _ (fun i j => (hcore i j).le)
  have hAdet : 0 < gramFirst (realEntryRoot p A) * gramSecond (realEntryRoot p A) -
      gramCross (realEntryRoot p A) ^ 2 := by
    rw [hroot, rationalSVDCore_gramDet]
    positivity
  have hscale : B = s • A := by
    rw [← realEntryPowers_realEntryRoot (by linarith : p ≠ 0) B
      (fun i j => (hB i j).le)]
    change realEntryPowers p M = s • A
    rw [he]
    ext i j
    change (L * rationalSVDCore t w h i j) ^ p = L ^ p * rationalSVDCore t w h i j ^ p
    exact Real.mul_rpow hL.le (hcore i j).le
  have hHs := compressionHessian_scale hp hs A E hA hAdet
  rw [← hscale, hE, smul_zero] at hHs
  obtain ⟨r, hr⟩ := chart_compressionHessian_kernel_radial hp hp2 hh hh1 ht hw hcore E hHs.symm
  refine ⟨r / s, ?_⟩
  rw [hr, hscale, smul_smul]
  congr 1
  exact (div_mul_cancel₀ r hs.ne').symm

end

end ResearchMain.DiagonalSchatten
