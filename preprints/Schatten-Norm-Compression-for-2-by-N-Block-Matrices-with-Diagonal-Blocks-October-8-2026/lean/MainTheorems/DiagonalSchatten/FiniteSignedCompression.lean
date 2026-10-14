import MainTheorems.DiagonalSchatten.FiniteSecondVariation
import MainTheorems.DiagonalSchatten.CompressionAffineDerivatives

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise Topology

variable {J : Type*} [Fintype J] [DecidableEq J] [Nontrivial J]

theorem finite_signed_compression_affine_convex {p : ℝ} (hp : 1 < p) (s : ℝ)
    (hcurv : ∀ (Y V : Matrix (Fin 2) J ℝ), (∀ i j, 0 < Y i j) →
      0 < gramFirst (realEntryRoot p Y) * gramSecond (realEntryRoot p Y) -
        gramCross (realEntryRoot p Y) ^ 2 → 0 ≤ s * compressionHessian p Y V V)
    (B C : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 < B i j)
    (hC : ∀ i j, 0 < C i j) {j k : J} (hminor : rowMinor B j k ≠ 0) :
    ConvexOn ℝ (Set.Icc 0 1)
      (fun t => s * compressionFunctional p (affineArray B (C - B) t)) := by
  obtain ⟨exceptions, _, hs⟩ := finite_rank_loss (by linarith : 0 < p) B (C - B) hminor
  have hC1 (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
      ContDiffAt ℝ 1 (fun x => s * compressionFunctional p (affineArray B (C - B) x)) t :=
    contDiffAt_const.mul (contDiffAt_compressionFunctional_affine hp B (C - B) t
      (affineArray_positive_segment B C hB hC ht))
  have hgram (t : ℝ) (ht : t ∈ Set.Ioo 0 1) (hts : t ∉ exceptions) :
      0 < gramFirst (realEntryRoot p (affineArray B (C - B) t)) *
        gramSecond (realEntryRoot p (affineArray B (C - B) t)) -
        gramCross (realEntryRoot p (affineArray B (C - B) t)) ^ 2 := by
    have hnonneg := areaVector_norm_sq (realEntryRoot p (affineArray B (C - B) t))
    have hne : gramFirst (realEntryRoot p (affineArray B (C - B) t)) *
        gramSecond (realEntryRoot p (affineArray B (C - B) t)) -
        gramCross (realEntryRoot p (affineArray B (C - B) t)) ^ 2 ≠ 0 := by
      intro hz
      exact hts (hs t (affineArray_positive_segment B C hB hC
        (Set.Ioo_subset_Icc_self ht)) hz)
    have hge : 0 ≤ gramFirst (realEntryRoot p (affineArray B (C - B) t)) *
        gramSecond (realEntryRoot p (affineArray B (C - B) t)) -
        gramCross (realEntryRoot p (affineArray B (C - B) t)) ^ 2 := by
      nlinarith [sq_nonneg ‖areaVector (realEntryRoot p (affineArray B (C - B) t))‖]
    exact lt_of_le_of_ne hge hne.symm
  have hD2 (t : ℝ) (ht : t ∈ Set.Ioo 0 1) (hts : t ∉ exceptions) :
      HasDerivAt (deriv (fun x => s * compressionFunctional p (affineArray B (C - B) x)))
        (s * compressionHessian p (affineArray B (C - B) t) (C - B) (C - B)) t := by
    rw [deriv_const_mul_field']
    exact (compressionFunctional_affine_second_deriv hp B (C - B) t
      (affineArray_positive_segment B C hB hC (Set.Ioo_subset_Icc_self ht))
      (hgram t ht hts)).const_mul s
  apply convexOn_of_second_deriv_nonneg_off_finset exceptions
  · exact ((continuous_compressionFunctional (by linarith : 0 < p)).comp
      (by unfold affineArray; fun_prop)).const_mul s |>.continuousOn
  · intro t ht
    exact (hC1 t ht).differentiableAt (by norm_num)
  · intro t ht
    exact ((hC1 t ht).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  · intro t ht hts
    exact (hD2 t ht hts).differentiableAt
  · intro t ht hts
    rw [(hD2 t ht hts).deriv]
    exact hcurv _ _ (affineArray_positive_segment B C hB hC (Set.Ioo_subset_Icc_self ht))
      (hgram t ht hts)

theorem finite_signed_compression_weighted_fullRank {p : ℝ} (hp : 1 < p) (s : ℝ)
    (hcurv : ∀ (Y V : Matrix (Fin 2) J ℝ), (∀ i j, 0 < Y i j) →
      0 < gramFirst (realEntryRoot p Y) * gramSecond (realEntryRoot p Y) -
        gramCross (realEntryRoot p Y) ^ 2 → 0 ≤ s * compressionHessian p Y V V)
    (B C : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 < B i j)
    (hC : ∀ i j, 0 < C i j) {j k : J} (hminor : rowMinor B j k ≠ 0)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    s * compressionFunctional p (a • B + b • C) ≤
      a * (s * compressionFunctional p B) + b * (s * compressionFunctional p C) := by
  have hc := finite_signed_compression_affine_convex hp s hcurv B C hB hC hminor
  have he := hc.2 (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1) ha hb hab
  have hsum : affineArray B (C - B) b = a • B + b • C := by
    ext i j
    change B i j + b * (C i j - B i j) = a * B i j + b * C i j
    have ha' : a = 1 - b := by linarith
    rw [ha']
    ring
  have hzero : affineArray B (C - B) 0 = B := by ext i j; simp [affineArray]
  have hone : affineArray B (C - B) 1 = C := by ext i j; simp [affineArray]
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, hzero, hone, hsum] using he

theorem finite_signed_compression_weighted_positive {p : ℝ} (hp : 1 < p) (s : ℝ)
    (hcurv : ∀ (Y V : Matrix (Fin 2) J ℝ), (∀ i j, 0 < Y i j) →
      0 < gramFirst (realEntryRoot p Y) * gramSecond (realEntryRoot p Y) -
        gramCross (realEntryRoot p Y) ^ 2 → 0 ≤ s * compressionHessian p Y V V)
    (B C : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 < B i j)
    (hC : ∀ i j, 0 < C i j)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    s * compressionFunctional p (a • B + b • C) ≤
      a * (s * compressionFunctional p B) + b * (s * compressionFunctional p C) := by
  obtain ⟨j, k, hjk⟩ := exists_pair_ne J
  by_cases hminor : rowMinor B j k = 0
  · let P := perturbFirstCoordinate B j
    have hP : Continuous P := continuous_perturbFirstCoordinate B j
    have hP0 : P 0 = B := by ext i k; simp [P, perturbFirstCoordinate]
    have hg : Continuous (compressionFunctional (J := J) p) :=
      continuous_compressionFunctional (by linarith)
    have hleft : Continuous (fun e : ℝ => s * compressionFunctional p (a • P e + b • C)) :=
      (hg.comp ((hP.const_smul a).add continuous_const)).const_mul s
    have hright : Continuous (fun e : ℝ =>
        a * (s * compressionFunctional p (P e)) + b * (s * compressionFunctional p C)) :=
      (((hg.comp hP).const_mul s).const_mul a).add continuous_const
    have he := le_of_tendsto_of_tendsto
      (hleft.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (hright.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (show ∀ᶠ e in 𝓝[>] (0 : ℝ),
        s * compressionFunctional p (a • P e + b • C) ≤
          a * (s * compressionFunctional p (P e)) + b * (s * compressionFunctional p C) by
        filter_upwards [self_mem_nhdsWithin] with e he
        exact finite_signed_compression_weighted_fullRank hp s hcurv (P e) C
          (perturbFirstCoordinate_positive B hB j he.le) hC
          (perturbFirstCoordinate_rank B hB hjk hminor he) ha hb hab)
    simpa only [hP0] using he
  · exact finite_signed_compression_weighted_fullRank hp s hcurv B C hB hC hminor ha hb hab

theorem finite_signed_compression_weighted_nonnegative {p : ℝ} (hp : 1 < p) (s : ℝ)
    (hcurv : ∀ (Y V : Matrix (Fin 2) J ℝ), (∀ i j, 0 < Y i j) →
      0 < gramFirst (realEntryRoot p Y) * gramSecond (realEntryRoot p Y) -
        gramCross (realEntryRoot p Y) ^ 2 → 0 ≤ s * compressionHessian p Y V V)
    (B C : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (hC : ∀ i j, 0 ≤ C i j)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    s * compressionFunctional p (a • B + b • C) ≤
      a * (s * compressionFunctional p B) + b * (s * compressionFunctional p C) := by
  let P : ℝ → Matrix (Fin 2) J ℝ := fun e => Matrix.of fun i j => B i j + e
  let Q : ℝ → Matrix (Fin 2) J ℝ := fun e => Matrix.of fun i j => C i j + e
  have hP : Continuous P := by unfold P; fun_prop
  have hQ : Continuous Q := by unfold Q; fun_prop
  have hP0 : P 0 = B := by ext i j; simp [P]
  have hQ0 : Q 0 = C := by ext i j; simp [Q]
  have hg : Continuous (compressionFunctional (J := J) p) :=
    continuous_compressionFunctional (by linarith)
  have hleft : Continuous (fun e : ℝ => s * compressionFunctional p (a • P e + b • Q e)) :=
    (hg.comp ((hP.const_smul a).add (hQ.const_smul b))).const_mul s
  have hright : Continuous (fun e : ℝ =>
      a * (s * compressionFunctional p (P e)) + b * (s * compressionFunctional p (Q e))) :=
    (((hg.comp hP).const_mul s).const_mul a).add (((hg.comp hQ).const_mul s).const_mul b)
  have he := le_of_tendsto_of_tendsto
    (hleft.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hright.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (show ∀ᶠ e in 𝓝[>] (0 : ℝ),
      s * compressionFunctional p (a • P e + b • Q e) ≤
        a * (s * compressionFunctional p (P e)) + b * (s * compressionFunctional p (Q e)) by
      filter_upwards [self_mem_nhdsWithin] with e he
      exact finite_signed_compression_weighted_positive hp s hcurv (P e) (Q e)
        (fun i j => add_pos_of_nonneg_of_pos (hB i j) he)
        (fun i j => add_pos_of_nonneg_of_pos (hC i j) he) ha hb hab)
  simpa only [hP0, hQ0] using he

theorem compressionFunctional_nontrivial_subadditive {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (B C : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j) :
    compressionFunctional p (B + C) ≤ compressionFunctional p B + compressionFunctional p C := by
  have he := finite_signed_compression_weighted_nonnegative hp 1
    (fun Y V hY hd => by
      have h := compressionHessian_finite_signed (Or.inr ⟨hp, hp2, rfl⟩) Y V hY hd
      simpa only [one_mul] using (show 0 ≤ compressionHessian p Y V V by linarith))
    B C hB hC (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  rw [← smul_add, compressionFunctional_homogeneous (by linarith : 0 < p)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (B + C) (fun i j => add_nonneg (hB i j) (hC i j))] at he
  simp only [one_mul] at he
  linarith

theorem compressionFunctional_nontrivial_superadditive {p : ℝ} (hp : 2 < p) (hp4 : p < 4)
    (B C : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j) :
    compressionFunctional p B + compressionFunctional p C ≤ compressionFunctional p (B + C) := by
  have he := finite_signed_compression_weighted_nonnegative (by linarith) (-1)
    (fun Y V hY hd => by
      have h := compressionHessian_finite_signed (Or.inl ⟨hp, hp4, rfl⟩) Y V hY hd
      simpa only [one_mul, neg_one_mul, neg_nonneg] using h)
    B C hB hC (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  rw [← smul_add, compressionFunctional_homogeneous (by linarith : 0 < p)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (B + C) (fun i j => add_nonneg (hB i j) (hC i j))] at he
  simp only [neg_one_mul] at he
  linarith

end

end ResearchMain.DiagonalSchatten
