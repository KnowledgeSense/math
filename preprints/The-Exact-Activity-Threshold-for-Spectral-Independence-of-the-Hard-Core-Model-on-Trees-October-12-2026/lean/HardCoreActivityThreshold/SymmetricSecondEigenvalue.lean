import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! The second sorted eigenvalue is the largest Rayleigh quotient orthogonal to a unit fixed vector. -/
namespace HardCoreActivityThreshold
open Finset
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {n : ℕ} (hn : Module.finrank ℝ E = n)

theorem symmetric_quadratic_eigen_expansion (v : E) :
    ⟪T v, v⟫ = ∑ i : Fin n, hT.eigenvalues hn i * ⟪hT.eigenvectorBasis hn i, v⟫^2 := by
  rw [← (hT.eigenvectorBasis hn).sum_inner_mul_inner (T v) v]
  apply sum_congr rfl
  intro i _
  rw [hT v (hT.eigenvectorBasis hn i), hT.apply_eigenvectorBasis, inner_smul_right,
    real_inner_comm v]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  ring

theorem symmetric_eigenvalue_le_one
    (hbound : ∀ v : E, ⟪T v, v⟫ ≤ ‖v‖^2) (i : Fin n) :
    hT.eigenvalues hn i ≤ 1 := by
  have hh := hbound (hT.eigenvectorBasis hn i)
  simpa [hT.apply_eigenvectorBasis, inner_smul_left] using hh

/-- The upper Rayleigh bound on the orthogonal complement of any unit fixed vector. -/
theorem symmetric_second_eigenvalue_bound (hn2 : 1 < n) (u : E) (hu : ‖u‖ = 1)
    (hfix : T u = u) (hbound : ∀ v : E, ⟪T v, v⟫ ≤ ‖v‖^2)
    (v : E) (hv : ⟪u, v⟫ = 0) :
    ⟪T v, v⟫ ≤ hT.eigenvalues hn ⟨1, hn2⟩ * ‖v‖^2 := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, hn2⟩
  let b := hT.eigenvectorBasis hn
  by_cases h1 : hT.eigenvalues hn i1 = 1
  · simpa only [show (⟨1, hn2⟩ : Fin n) = i1 from rfl, h1, one_mul] using hbound v
  have hlt : hT.eigenvalues hn i1 < 1 := lt_of_le_of_ne (symmetric_eigenvalue_le_one hT hn hbound i1) h1
  have huzero (i : Fin n) (hi : i ≠ i0) : ⟪b i, u⟫ = 0 := by
    have hle : i1 ≤ i := by
      change 1 ≤ i.val
      have : i.val ≠ 0 := by
        intro he
        apply hi
        exact Fin.ext he
      omega
    have heig : hT.eigenvalues hn i < 1 := lt_of_le_of_lt (hT.eigenvalues_antitone hn hle) hlt
    have hh := hT.eigenvectorBasis_apply_self_apply hn u i
    rw [hfix] at hh
    simp only [OrthonormalBasis.repr_apply_apply] at hh
    change ⟪b i, u⟫ = hT.eigenvalues hn i * ⟪b i, u⟫ at hh
    nlinarith
  have hu_expand : u = ⟪b i0, u⟫ • b i0 := by
    nth_rw 1 [← b.sum_repr' u]
    apply sum_eq_single i0
    · intro i _ hi
      rw [huzero i hi, zero_smul]
    · simp
  have hu0 : ⟪b i0, u⟫ ≠ 0 := by
    intro hz
    have huz : u = 0 := by simpa only [hz, zero_smul] using hu_expand
    simp [huz] at hu
  have hvzero : ⟪b i0, v⟫ = 0 := by
    rw [hu_expand, inner_smul_left] at hv
    exact (mul_eq_zero.mp hv).resolve_left hu0
  rw [symmetric_quadratic_eigen_expansion hT hn v, ← b.sum_sq_inner_right v, mul_sum]
  apply sum_le_sum
  intro i _
  by_cases hi : i = i0
  · subst i
    simp only [show hT.eigenvectorBasis hn i0 = b i0 from rfl, hvzero, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply hT.eigenvalues_antitone hn
    change 1 ≤ i.val
    have : i.val ≠ 0 := by intro he; apply hi; exact Fin.ext he
    omega

/-- A nonzero centered eigenvector realizes the second sorted eigenvalue, even if one is repeated. -/
theorem symmetric_second_eigenvalue_attained (hn2 : 1 < n) (u : E)
    (hfix : T u = u) (hbound : ∀ v : E, ⟪T v, v⟫ ≤ ‖v‖^2) :
    ∃ v : E, v ≠ 0 ∧ ⟪u, v⟫ = 0 ∧ T v = hT.eigenvalues hn ⟨1, hn2⟩ • v := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, hn2⟩
  let b := hT.eigenvectorBasis hn
  have hb (i : Fin n) : T (b i) = hT.eigenvalues hn i • b i := hT.apply_eigenvectorBasis hn i
  have h01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; dsimp [i0, i1] at this; omega
  by_cases h1 : hT.eigenvalues hn i1 = 1
  · have h0 : hT.eigenvalues hn i0 = 1 := le_antisymm
      (symmetric_eigenvalue_le_one hT hn hbound i0)
      (by rw [← h1]; exact hT.eigenvalues_antitone hn (by change 0 ≤ 1; omega))
    by_cases hu0 : ⟪u, b i0⟫ = 0
    · refine ⟨b i0, b.toBasis.ne_zero i0, hu0, ?_⟩
      rw [hb, h0, show (⟨1, hn2⟩ : Fin n) = i1 from rfl, h1]
    · let a : ℝ := ⟪u, b i1⟫ / ⟪u, b i0⟫
      let v : E := b i1 - a • b i0
      have hvinner : ⟪b i1, v⟫ = 1 := by
        simp [v, inner_sub_right, inner_smul_right, b.inner_eq_zero h01.symm]
      refine ⟨v, ?_, ?_, ?_⟩
      · intro hz
        simp [hz] at hvinner
      · dsimp [v, a]
        rw [inner_sub_right, inner_smul_right, div_mul_cancel₀ _ hu0, sub_self]
      · dsimp [v]
        rw [map_sub, map_smul, hb, hb, h0, h1]
        simp
  · refine ⟨b i1, b.toBasis.ne_zero i1, ?_, hb i1⟩
    have hh := hT u (b i1)
    rw [hfix, hb, inner_smul_right] at hh
    have hlt : hT.eigenvalues hn i1 < 1 := lt_of_le_of_ne
      (symmetric_eigenvalue_le_one hT hn hbound i1) h1
    nlinarith

end HardCoreActivityThreshold
