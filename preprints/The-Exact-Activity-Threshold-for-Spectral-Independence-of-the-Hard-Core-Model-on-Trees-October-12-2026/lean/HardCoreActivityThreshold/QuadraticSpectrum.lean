import HardCoreActivityThreshold.InfluenceSimilarity

namespace HardCoreActivityThreshold
open Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem real_matrix_complex_spectrum (A : Matrix V V ℝ) (hA : A.IsHermitian) (z : ℂ) :
    z∈spectrum ℂ (A.map (fun x : ℝ => (x : ℂ))) ↔ ∃i,z=(hA.eigenvalues i : ℂ) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  change (A.map Complex.ofRealHom).charpoly.IsRoot z ↔ _
  rw [Matrix.charpoly_map,hA.charpoly_eq]
  simp [Polynomial.IsRoot,Polynomial.map_prod,Polynomial.eval_prod,Finset.prod_eq_zero_iff,sub_eq_zero]

 theorem hermitian_radius_le (A : Matrix V V ℝ) (hA : A.IsHermitian) (M : ℝ)
    (hM : ∀i,|hA.eigenvalues i|≤M) :
    spectralRadius ℂ (A.map (fun x : ℝ => (x : ℂ)))≤ENNReal.ofReal M := by
  rw [spectralRadius_eq_of_unital]
  apply iSup_le
  intro z
  apply iSup_le
  intro hz
  obtain ⟨i,rfl⟩ := (real_matrix_complex_spectrum A hA z).mp hz
  rw [←ENNReal.ofReal_coe_nnreal]
  simpa using ENNReal.ofReal_le_ofReal (hM i)

 theorem hermitian_eigenvalue_quadratic_bounds (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (a b : ℝ)
    (hlo : ∀x : V → ℝ,a*(∑i,(x i)^2)≤x ⬝ᵥ (A*ᵥx))
    (hhi : ∀x : V → ℝ,x ⬝ᵥ (A*ᵥx)≤b*(∑i,(x i)^2)) (i : V) :
    a≤hA.eigenvalues i ∧ hA.eigenvalues i≤b := by
  let x : V → ℝ := (hA.eigenvectorBasis i).ofLp
  have hs : (∑v,(x v)^2)=1 := by
    rw [←EuclideanSpace.real_norm_sq_eq (hA.eigenvectorBasis i),OrthonormalBasis.norm_eq_one]
    norm_num
  have he : x ⬝ᵥ (A*ᵥx)=hA.eigenvalues i := by
    rw [hA.eigenvalues_eq]
    simp [x]
  have hl := hlo x
  have hh := hhi x
  rw [hs,he,mul_one] at hl hh
  exact ⟨hl,hh⟩

 theorem hermitian_radius_quadratic_bound (A : Matrix V V ℝ) (hA : A.IsHermitian) (C : ℝ)
    (hC : 0≤C)
    (hlo : ∀x : V → ℝ,-(∑i,(x i)^2)≤x ⬝ᵥ (A*ᵥx))
    (hhi : ∀x : V → ℝ,x ⬝ᵥ (A*ᵥx)≤C*(∑i,(x i)^2)) :
    spectralRadius ℂ (A.map (fun x : ℝ => (x : ℂ)))≤ENNReal.ofReal (C+1) := by
  apply hermitian_radius_le A hA (C+1)
  intro i
  have he := hermitian_eigenvalue_quadratic_bounds A hA (-1) C
    (fun x => by simpa using hlo x) hhi i
  exact abs_le.mpr ⟨by linarith [he.1],by linarith [he.2]⟩

end HardCoreActivityThreshold
