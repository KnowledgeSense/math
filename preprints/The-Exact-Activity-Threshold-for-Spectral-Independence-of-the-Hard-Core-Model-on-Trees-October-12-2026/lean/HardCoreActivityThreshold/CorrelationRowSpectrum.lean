import HardCoreActivityThreshold.InfluenceSimilarity

/-! Spectral lower bounds forced by a row of an actual correlation matrix. -/
namespace HardCoreActivityThreshold
open Finset Matrix Unitary
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem conjugate_diagonal_entry (U : Matrix.unitaryGroup V ℝ) (d : V → ℝ) (v : V) :
    conjStarAlgAut ℝ (Matrix V V ℝ) U (diagonal d) v v =
      ∑ i, d i * (U v i)^2 := by
  simp only [conjStarAlgAut_apply, mul_apply, star_eq_conjTranspose,
    conjTranspose_apply, star_trivial]
  apply sum_congr rfl
  intro i _
  simp only [diagonal_apply, mul_ite, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte]
  ring

private theorem hermitian_diagonal_expansion (A : Matrix V V ℝ) (hA : A.IsHermitian) (v : V) :
    A v v = ∑ i, hA.eigenvalues i * (hA.eigenvectorUnitary v i)^2 := by
  conv_lhs => rw [hA.spectral_theorem]
  exact conjugate_diagonal_entry _ _ _

private theorem hermitian_row_square_expansion (A : Matrix V V ℝ) (hA : A.IsHermitian) (v : V) :
    (∑ w, (A v w)^2) = ∑ i, (hA.eigenvalues i)^2 * (hA.eigenvectorUnitary v i)^2 := by
  have he : (∑ w, (A v w)^2) = (A*A) v v := by
    rw [mul_apply]
    apply sum_congr rfl
    intro w _
    have hs : A w v = A v w := by simpa using congrArg (fun M => M v w) hA
    rw [hs, sq]
  rw [he]
  have hm : A*A = conjStarAlgAut ℝ (Matrix V V ℝ) hA.eigenvectorUnitary
      (diagonal (fun i => (hA.eigenvalues i)^2)) := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [← map_mul, diagonal_mul_diagonal]
    congr 1
    ext i j
    simp [sq]
  rw [hm]
  exact conjugate_diagonal_entry _ _ _

/-- A positive-semidefinite matrix with unit diagonal has row squared norm at most its largest eigenvalue. -/
theorem correlation_row_square_le_largest [Nonempty V] (μ : FiniteLaw (Finset V))
    (hvar : ∀ v, 0 < occupationVariance μ v) (v : V) :
    (∑ w, (correlationMatrix μ v w)^2) ≤ largestCorrelationEigenvalue μ := by
  rw [hermitian_row_square_expansion _ (correlationMatrix_isHermitian μ)]
  have he := hermitian_diagonal_expansion (correlationMatrix μ) (correlationMatrix_isHermitian μ) v
  rw [correlationMatrix_diag μ v (hvar v)] at he
  calc
    _ ≤ ∑ i, (largestCorrelationEigenvalue μ * (correlationMatrix_isHermitian μ).eigenvalues i) *
        ((correlationMatrix_isHermitian μ).eigenvectorUnitary v i)^2 := by
      apply sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have hi := correlationEigenvalue_le_largest μ i
      have hn := (correlationMatrix_posSemidef μ).eigenvalues_nonneg i
      nlinarith
    _ = largestCorrelationEigenvalue μ := by
      simp_rw [mul_assoc]
      rw [← mul_sum, ← he, mul_one]

private theorem unitary_row_square (U : Matrix.unitaryGroup V ℝ) (v : V) :
    (∑ i, (U v i)^2) = 1 := by
  have he := congrArg (fun M : Matrix V V ℝ => M v v) (Unitary.coe_mul_star_self U)
  simpa only [Unitary.coe_star, mul_apply, star_eq_conjTranspose, conjTranspose_apply, star_trivial,
    ← sq, one_apply_eq] using he

private theorem hermitian_row_le_eigenvalue_square [Nonempty V] (A : Matrix V V ℝ)
    (hA : A.IsHermitian) (v : V) :
    ∃ i, (∑ w, (A v w)^2) ≤ (hA.eigenvalues i)^2 := by
  obtain ⟨i, _, hi⟩ := exists_max_image univ (fun i => (hA.eigenvalues i)^2) univ_nonempty
  refine ⟨i, ?_⟩
  rw [hermitian_row_square_expansion A hA v]
  calc
    _ ≤ ∑ j, (hA.eigenvalues i)^2 * (hA.eigenvectorUnitary v j)^2 := by
      apply sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (hi j (mem_univ j)) (sq_nonneg _)
    _ = (hA.eigenvalues i)^2 := by rw [← mul_sum, unitary_row_square, mul_one]

private theorem real_eigenvalue_mem_complex_spectrum (A : Matrix V V ℝ)
    (hA : A.IsHermitian) (i : V) :
    (hA.eigenvalues i : ℂ) ∈ spectrum ℂ (A.map (fun x : ℝ => (x : ℂ))) := by
  have hr := Matrix.mem_spectrum_iff_isRoot_charpoly.mp (hA.eigenvalues_mem_spectrum_real i)
  apply Matrix.mem_spectrum_of_isRoot_charpoly
  have hc : (A.map (fun x : ℝ => (x : ℂ))).charpoly = A.charpoly.map Complex.ofRealHom := by
    convert Matrix.charpoly_map A Complex.ofRealHom using 1
  rw [hc]
  exact hr.map

private theorem real_eigenvalue_le_complex_radius (A : Matrix V V ℝ)
    (hA : A.IsHermitian) (i : V) :
    ENNReal.ofReal |hA.eigenvalues i| ≤ spectralRadius ℂ (A.map (fun x : ℝ => (x : ℂ))) := by
  rw [spectralRadius_eq_of_unital]
  apply le_iSup₂_of_le (hA.eigenvalues i : ℂ) (real_eigenvalue_mem_complex_spectrum A hA i)
  rw [← ENNReal.ofReal_coe_nnreal]
  simp [Real.norm_eq_abs]

theorem absoluteCorrelation_isHermitian (μ : FiniteLaw (Finset V)) :
    (absoluteCorrelationMinusIdentity μ).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext u v
  simp only [absoluteCorrelationMinusIdentity, transpose_apply, Matrix.sub_apply, of_apply]
  rw [correlationMatrix_symm μ v u]
  simp [one_apply, eq_comm]

theorem absoluteCorrelation_row_square (μ : FiniteLaw (Finset V))
    (hvar : ∀ v, 0 < occupationVariance μ v) (v : V) :
    (∑ w, (absoluteCorrelationMinusIdentity μ v w)^2) + 1 =
      ∑ w, (correlationMatrix μ v w)^2 := by
  have he (w : V) : (absoluteCorrelationMinusIdentity μ v w)^2 =
      (correlationMatrix μ v w)^2 - if w = v then 1 else 0 := by
    by_cases hw : w = v
    · subst w
      simp [absoluteCorrelationMinusIdentity, correlationMatrix_diag μ v (hvar v)]
    · simp [absoluteCorrelationMinusIdentity, one_apply, hw, Ne.symm hw, sq_abs]
  simp_rw [he]
  rw [sum_sub_distrib]
  simp

/-- A large row of the actual correlation matrix forces a large genuine influence spectral radius. -/
theorem influenceSpectralRadius_gt_of_row [Nonempty V] (μ : FiniteLaw (Finset V))
    (hvar : ∀ v, 0 < occupationVariance μ v) (v : V) {K : ℝ} (hK : 0 ≤ K)
    (hrow : K^2+1 < ∑ w, (correlationMatrix μ v w)^2) :
    ENNReal.ofReal K < influenceSpectralRadius μ := by
  obtain ⟨i, hi⟩ := hermitian_row_le_eigenvalue_square
    (absoluteCorrelationMinusIdentity μ) (absoluteCorrelation_isHermitian μ) v
  have he := absoluteCorrelation_row_square μ hvar v
  have hsq : K^2 < ((absoluteCorrelation_isHermitian μ).eigenvalues i)^2 := by linarith
  have habs : K < |(absoluteCorrelation_isHermitian μ).eigenvalues i| := by
    nlinarith [sq_abs ((absoluteCorrelation_isHermitian μ).eigenvalues i),
      abs_nonneg ((absoluteCorrelation_isHermitian μ).eigenvalues i)]
  rw [influenceSpectralRadius_eq_absoluteCorrelation μ hvar]
  apply lt_of_lt_of_le _ (real_eigenvalue_le_complex_radius _ (absoluteCorrelation_isHermitian μ) i)
  exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hK habs)).mpr habs

end HardCoreActivityThreshold
