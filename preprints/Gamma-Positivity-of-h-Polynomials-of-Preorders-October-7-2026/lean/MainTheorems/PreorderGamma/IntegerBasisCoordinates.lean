import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic

namespace ResearchMain.PreorderGamma

open Module
open scoped BigOperators Classical Matrix

variable {I T : Type*} [Fintype I] [DecidableEq I]

def integerVectorCast (z : I → ℤ) : I → ℝ := fun i => (z i : ℝ)

def integerConfigurationMatrix (V : T → I → ℤ) : Matrix I T ℤ := fun i t => V t i

def integerColumnMatrix (V : T → I → ℤ) (f : I → T) : Matrix I I ℤ :=
  fun i j => V (f j) i

theorem integer_column_det_range (V : T → I → ℤ) (f : I → T)
    (hV : (integerConfigurationMatrix V).IsTotallyUnimodular) :
    (integerColumnMatrix V f).det ∈ Set.range (SignType.cast : SignType → ℤ) := by
  exact (Matrix.isTotallyUnimodular_iff_fintype _).mp hV I id f

theorem integer_column_det_ne_zero (V : T → I → ℤ) (f : I → T)
    (hf : LinearIndependent ℝ (fun j => integerVectorCast (V (f j)))) :
    (integerColumnMatrix V f).det ≠ 0 := by
  let A : Matrix I I ℝ := (integerColumnMatrix V f).map (Int.castRingHom ℝ)
  have hlin : LinearIndependent ℝ A.col := hf
  have hinj : Function.Injective A.mulVec := Matrix.mulVec_injective_iff.mpr hlin
  intro hz
  have hdet : A.det = 0 := by
    change ((integerColumnMatrix V f).map (fun x : ℤ => (x : ℝ))).det = 0
    rw [← Int.cast_det, hz, Int.cast_zero]
  obtain ⟨x, hx, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hx
  apply hinj
  simpa only [Matrix.mulVec_zero] using hzero

theorem integer_column_det_sign (V : T → I → ℤ) (f : I → T)
    (hV : (integerConfigurationMatrix V).IsTotallyUnimodular)
    (hf : LinearIndependent ℝ (fun j => integerVectorCast (V (f j)))) :
    (integerColumnMatrix V f).det = 1 ∨ (integerColumnMatrix V f).det = -1 := by
  obtain ⟨s, hs⟩ := integer_column_det_range V f hV
  have hn := integer_column_det_ne_zero V f hf
  cases s <;> simp_all

noncomputable def realColumnBasis (V : T → I → ℤ) (f : I → T)
    (hf : LinearIndependent ℝ (fun j => integerVectorCast (V (f j)))) :
    Basis I ℝ (I → ℝ) := basisOfPiSpaceOfLinearIndependent hf

omit [DecidableEq I] in
theorem realColumnBasis_apply (V : T → I → ℤ) (f : I → T)
    (hf : LinearIndependent ℝ (fun j => integerVectorCast (V (f j)))) (i : I) :
    realColumnBasis V f hf i = integerVectorCast (V (f i)) := by
  exact congrFun (coe_basisOfPiSpaceOfLinearIndependent hf) i

noncomputable def integerBasisCoordinates (V : T → I → ℤ) (f : I → T)
    (z : I → ℤ) : I → ℤ :=
  (integerColumnMatrix V f).det • (integerColumnMatrix V f).cramer z

theorem integer_basis_coordinates_solve (V : T → I → ℤ) (f : I → T)
    (hV : (integerConfigurationMatrix V).IsTotallyUnimodular)
    (hf : LinearIndependent ℝ (fun j => integerVectorCast (V (f j)))) (z : I → ℤ) :
    (integerColumnMatrix V f) *ᵥ integerBasisCoordinates V f z = z := by
  unfold integerBasisCoordinates
  rw [Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul]
  rcases integer_column_det_sign V f hV hf with h | h <;> simp [h]

theorem integer_basis_repr_eq (V : T → I → ℤ) (f : I → T)
    (hV : (integerConfigurationMatrix V).IsTotallyUnimodular)
    (hf : LinearIndependent ℝ (fun j => integerVectorCast (V (f j))))
    (z : I → ℤ) (i : I) :
    (realColumnBasis V f hf).repr (integerVectorCast z) i =
      (integerBasisCoordinates V f z i : ℝ) := by
  have hsolve := integer_basis_coordinates_solve V f hV hf z
  have hsum : (∑ j, (integerBasisCoordinates V f z j : ℝ) • realColumnBasis V f hf j) =
      integerVectorCast z := by
    funext k
    have h := congrArg (Int.castRingHom ℝ) (congrFun hsolve k)
    simpa only [Matrix.mulVec, dotProduct, integerColumnMatrix, integerVectorCast,
      Int.coe_castRingHom, Int.cast_sum, Int.cast_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      realColumnBasis_apply, mul_comm] using h
  rw [← hsum]
  exact congrFun ((realColumnBasis V f hf).repr_sum_self
    (fun j => (integerBasisCoordinates V f z j : ℝ))) i

theorem integer_basis_repr_integral (V : T → I → ℤ) (f : I → T)
    (hV : (integerConfigurationMatrix V).IsTotallyUnimodular)
    (hf : LinearIndependent ℝ (fun j => integerVectorCast (V (f j))))
    (z : I → ℤ) (i : I) :
    ∃ c : ℤ, (realColumnBasis V f hf).repr (integerVectorCast z) i = (c : ℝ) :=
  ⟨integerBasisCoordinates V f z i, integer_basis_repr_eq V f hV hf z i⟩

theorem integer_column_cramer_range (V : T → I → ℤ) (f : I → T)
    (hV : (integerConfigurationMatrix V).IsTotallyUnimodular) (t : T) (i : I) :
    (integerColumnMatrix V f).cramer (V t) i ∈
      Set.range (SignType.cast : SignType → ℤ) := by
  rw [Matrix.cramer_apply]
  have hmatrix : (integerColumnMatrix V f).updateCol i (V t) =
      (integerConfigurationMatrix V).submatrix id (fun j => if j = i then t else f j) := by
    ext k j
    by_cases h : j = i <;>
      simp [integerColumnMatrix, integerConfigurationMatrix, h]
  rw [hmatrix]
  exact (Matrix.isTotallyUnimodular_iff_fintype _).mp hV I id _

theorem integer_basis_column_sign (V : T → I → ℤ) (f : I → T)
    (hV : (integerConfigurationMatrix V).IsTotallyUnimodular) (t : T) (i : I) :
    integerBasisCoordinates V f (V t) i ∈ Set.range (SignType.cast : SignType → ℤ) := by
  obtain ⟨a, ha⟩ := integer_column_det_range V f hV
  obtain ⟨b, hb⟩ := integer_column_cramer_range V f hV t i
  refine ⟨a * b, ?_⟩
  simp only [integerBasisCoordinates, Pi.smul_apply, smul_eq_mul]
  rw [SignType.coe_mul, ha, hb]

theorem integer_basis_column_coordinates (V : T → I → ℤ) (f : I → T)
    (hV : (integerConfigurationMatrix V).IsTotallyUnimodular) (t : T) (i : I) :
    integerBasisCoordinates V f (V t) i = -1 ∨
      integerBasisCoordinates V f (V t) i = 0 ∨
        integerBasisCoordinates V f (V t) i = 1 := by
  obtain ⟨s, hs⟩ := integer_basis_column_sign V f hV t i
  cases s <;> simp_all

theorem real_basis_column_coordinates (V : T → I → ℤ) (f : I → T)
    (hV : (integerConfigurationMatrix V).IsTotallyUnimodular)
    (hf : LinearIndependent ℝ (fun j => integerVectorCast (V (f j)))) (t : T) (i : I) :
    (realColumnBasis V f hf).repr (integerVectorCast (V t)) i = -1 ∨
      (realColumnBasis V f hf).repr (integerVectorCast (V t)) i = 0 ∨
        (realColumnBasis V f hf).repr (integerVectorCast (V t)) i = 1 := by
  rw [integer_basis_repr_eq V f hV hf]
  rcases integer_basis_column_coordinates V f hV t i with h | h | h <;> simp [h]

omit [DecidableEq I] in
theorem integer_column_basis_extension [Fintype T] (V : T → I → ℤ) (S : Set T)
    (hS : LinearIndepOn ℝ (fun t => integerVectorCast (V t)) S)
    (hspan : Submodule.span ℝ (Set.range (fun t => integerVectorCast (V t))) = ⊤) :
    ∃ f : I → T, Function.Injective f ∧ S ⊆ Set.range f ∧
      LinearIndependent ℝ (fun j => integerVectorCast (V (f j))) := by
  obtain ⟨B, _, hSB, hspanB, hlin⟩ :=
    exists_linearIndepOn_extension hS (Set.subset_univ S)
  have hfamily : LinearIndependent ℝ (fun t : B => integerVectorCast (V t.val)) := hlin
  have hrange : Set.range (fun t : B => integerVectorCast (V t.val)) =
      (fun t => integerVectorCast (V t)) '' B := by
    ext x
    simp
  have hfull : ⊤ ≤ Submodule.span ℝ
      (Set.range (fun t : B => integerVectorCast (V t.val))) := by
    rw [hrange, ← hspan]
    apply Submodule.span_le.mpr
    intro x hx
    exact hspanB (by simpa only [Set.image_univ] using hx)
  let b : Basis B ℝ (I → ℝ) := Basis.mk hfamily hfull
  have hcard : Fintype.card B = Fintype.card I := by
    rw [← Module.finrank_eq_card_basis b]
    exact Module.finrank_fintype_fun_eq_card ℝ
  let e : B ≃ I := Fintype.equivOfCardEq hcard
  refine ⟨fun i => (e.symm i).val, ?_, ?_, ?_⟩
  · exact Subtype.val_injective.comp e.symm.injective
  · intro t ht
    refine ⟨e ⟨t, hSB ht⟩, ?_⟩
    simp only [e.symm_apply_apply]
  · exact hfamily.comp e.symm e.symm.injective

end ResearchMain.PreorderGamma
