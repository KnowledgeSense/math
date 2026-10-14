import BoseBurton.ActualCorrection
import BoseBurton.KernelReindex
import BoseBurton.OriginalKernelProperties

noncomputable section
namespace BoseBurton
open Submodule Module Polynomial MatroidInverseZ
open scoped Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Module.Finite K V]

/-- Finite-dimensional vector spaces over the actual finite field are finite. -/
theorem finiteVectorSpace (K : Type*) [Field K] [Fintype K] (V : Type*)
    [AddCommGroup V] [Module K V] [Module.Finite K V] : Finite V :=
  Finite.of_equiv (Fin (finrank K V) → K) (Module.finBasis K V).equivFun.toEquiv.symm


/-- The ordinary inverse-Z invariant of the literal Bose–Burton restriction. -/
def boseBurtonY (W : Submodule K V) : Polynomial ℤ := by
  letI : Finite V := finiteVectorSpace K V
  exact matroidInverseZ (matroid W)

/-- Exact identification of the original matroid invariant with the source finite kernel. -/
theorem boseBurtonY_eq_originalKernel (W : Submodule K V) (hW : W ≠ ⊤) :
    (boseBurtonY W).map (Int.castRingHom ℝ) =
      originalSignedKernel (Fintype.card K : ℝ) (finrank K V) (finrank K W) := by
  let : Finite V := finiteVectorSpace K V
  rw [boseBurtonY, actual_inverseZ_correction W hW,
    correctionRow_reindex _ _ _ (Submodule.finrank_le W)]

omit [Fintype K] [Module.Finite K V] in
theorem proper_of_dimension_lt (W : Submodule K V) (hsr : finrank K W < finrank K V) : W ≠ ⊤ := by
  intro h
  rw [h, finrank_top] at hsr
  exact (lt_irrefl _) hsr

theorem boseBurtonY_coeff_kernel (W : Submodule K V) (hsr : finrank K W < finrank K V) (k : ℕ) :
    ((boseBurtonY W).coeff k : ℝ) =
      (originalSignedKernel (Fintype.card K : ℝ) (finrank K V) (finrank K W)).coeff k := by
  have h := congrArg (fun p : Polynomial ℝ => p.coeff k)
    (boseBurtonY_eq_originalKernel W (proper_of_dimension_lt W hsr))
  rw [Polynomial.coeff_map] at h
  exact h

/-- Every coefficient, including zero coefficients above rank, has the exact source formula. -/
theorem boseBurtonY_coefficient_formula (W : Submodule K V)
    (hsr : finrank K W < finrank K V) (k : ℕ) :
    ((boseBurtonY W).coeff k : ℝ) = (Fintype.card K : ℝ)^((finrank K V).choose 2) *
      scalarCoefficient (Fintype.card K : ℝ)⁻¹ (finrank K V) (finrank K W) k := by
  rw [boseBurtonY_coeff_kernel W hsr,
    originalSignedKernel_coeff _ (by exact_mod_cast Fintype.one_lt_card (α := K)) _ _ _ hsr]

theorem boseBurtonY_coeff_positive (W : Submodule K V)
    (hsr : finrank K W < finrank K V) (k : ℕ) (hk : k ≤ finrank K V) :
    0 < (boseBurtonY W).coeff k := by
  have h := originalSignedKernel_coeff_pos (Fintype.card K : ℝ)
    (by exact_mod_cast Fintype.one_lt_card (α := K)) (finrank K V) (finrank K W) k hsr hk
  rw [← boseBurtonY_coeff_kernel W hsr k] at h
  exact_mod_cast h

theorem boseBurtonY_coeff_symm (W : Submodule K V)
    (hsr : finrank K W < finrank K V) (k : ℕ) (hk : k ≤ finrank K V) :
    (boseBurtonY W).coeff (finrank K V-k) = (boseBurtonY W).coeff k := by
  have h := originalSignedKernel_coeff_symm (Fintype.card K : ℝ)
    (by exact_mod_cast Fintype.one_lt_card (α := K)) (finrank K V) (finrank K W) k hsr hk
  rw [← boseBurtonY_coeff_kernel W hsr (finrank K V-k), ← boseBurtonY_coeff_kernel W hsr k] at h
  exact_mod_cast h

theorem boseBurtonY_coeff_above (W : Submodule K V)
    (hsr : finrank K W < finrank K V) (k : ℕ) (hk : finrank K V < k) :
    (boseBurtonY W).coeff k = 0 := by
  have h := originalSignedKernel_coeff_above (Fintype.card K : ℝ)
    (by exact_mod_cast Fintype.one_lt_card (α := K)) (finrank K V) (finrank K W) k hsr hk
  rw [← boseBurtonY_coeff_kernel W hsr k] at h
  exact_mod_cast h

theorem boseBurtonY_strict_logConcave (W : Submodule K V)
    (hs : 1 ≤ finrank K W) (hsr : finrank K W < finrank K V)
    (k : ℕ) (hk : 1 ≤ k) (hkr : k < finrank K V) :
    (boseBurtonY W).coeff (k-1) * (boseBurtonY W).coeff (k+1) < ((boseBurtonY W).coeff k)^2 := by
  have h := originalSignedKernel_strict_log_concave (Fintype.card K : ℝ)
    (by exact_mod_cast Fintype.one_lt_card (α := K)) (finrank K V) (finrank K W) k hsr hs hk hkr
  rw [← boseBurtonY_coeff_kernel W hsr (k-1), ← boseBurtonY_coeff_kernel W hsr (k+1),
    ← boseBurtonY_coeff_kernel W hsr k] at h
  exact_mod_cast h

theorem boseBurtonY_natDegree (W : Submodule K V) (hsr : finrank K W < finrank K V) :
    (boseBurtonY W).natDegree = finrank K V := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_le_iff_coeff_eq_zero.mpr (boseBurtonY_coeff_above W hsr)
  · exact (boseBurtonY_coeff_positive W hsr _ le_rfl).ne'

/-- Whole Bose–Burton ordinary inverse-Z theorem over every finite field, for every
nonzero proper deleted projective subspace. This includes all affine and rank-two boundaries. -/
theorem bose_burton_inverseZ_main (W : Submodule K V)
    (hs : 1 ≤ finrank K W) (hsr : finrank K W < finrank K V) :
    (boseBurtonY W).natDegree = finrank K V ∧
    (∀ k, k ≤ finrank K V → 0 < (boseBurtonY W).coeff k) ∧
    (∀ k, k ≤ finrank K V → (boseBurtonY W).coeff (finrank K V-k) = (boseBurtonY W).coeff k) ∧
    (∀ k, 1 ≤ k → k < finrank K V →
      (boseBurtonY W).coeff (k-1) * (boseBurtonY W).coeff (k+1) < ((boseBurtonY W).coeff k)^2) :=
  ⟨boseBurtonY_natDegree W hsr, boseBurtonY_coeff_positive W hsr,
    boseBurtonY_coeff_symm W hsr, boseBurtonY_strict_logConcave W hs hsr⟩

end BoseBurton
