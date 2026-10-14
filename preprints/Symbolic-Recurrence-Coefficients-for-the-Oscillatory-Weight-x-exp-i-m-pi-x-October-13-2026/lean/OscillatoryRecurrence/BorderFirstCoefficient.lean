import OscillatoryRecurrence.BorderJet
import Mathlib.LinearAlgebra.Matrix.Adjugate

noncomputable section
open Polynomial Finset
open scoped BigOperators Matrix
namespace OscillatoryRecurrence

theorem det_updateCol_sub_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (M : Matrix ι ι R) (j : ι) (v c : ι → R) (hc : c j=0) :
    (M.updateCol j (v-M*ᵥc)).det=(M.updateCol j v).det := by
  change (M.cramer (v-M*ᵥc)) j=(M.cramer v) j
  rw [map_sub]
  simp only [Pi.sub_apply]
  simp only [Matrix.cramer_eq_adjugate_mulVec,Matrix.mulVec_mulVec,Matrix.adjugate_mul,
    Matrix.smul_mulVec,Matrix.one_mulVec]
  simp [hc]

/-- Once a border's constant column is eliminated, its first determinant coefficient
is the single replaced-column determinant of the first-order residual. -/
theorem border_first_coefficients {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ[X]) (j : ι) (v : ι → ℚ[X]) (c : ι → ℚ)
    (hc : c j=0)
    (hv : (fun i => (v i).coeff 0)=(M.map (fun p => p.coeff 0))*ᵥc) :
    ((M.updateCol j v).det).coeff 0=0 ∧
    ((M.updateCol j v).det).coeff 1=
      ((M.map (fun p => p.coeff 0)).updateCol j
        ((fun i => (v i).coeff 1)-(M.map (fun p => p.coeff 1))*ᵥc)).det := by
  let w : ι → ℚ[X] := v-M*ᵥ(fun i => C (c i))
  have hw (i : ι) : (w i).coeff 0=0 := by
    have h := congrFun hv i
    simp only [Matrix.mulVec,dotProduct,Matrix.map_apply] at h
    simp only [w,Pi.sub_apply,Matrix.mulVec,dotProduct,coeff_sub,finsetSum_coeff,coeff_mul_C]
    linarith
  have hw1 (i : ι) : (w i).coeff 1=
      ((fun i => (v i).coeff 1)-(M.map (fun p => p.coeff 1))*ᵥc) i := by
    simp [w,Matrix.mulVec,dotProduct,coeff_mul_C]
  have he : w=(X:ℚ[X]) • (fun i => (w i).divX) := by
    funext i
    have h := X_mul_divX_add (w i)
    simpa [hw] using h.symm
  have hd : (M.updateCol j v).det=X*(M.updateCol j (fun i => (w i).divX)).det := by
    rw [← det_updateCol_sub_mulVec M j v (fun i => C (c i)) (by simp [hc])]
    change (M.updateCol j w).det=_
    nth_rw 1 [he]
    rw [Matrix.det_updateCol_smul]
  rw [hd]
  constructor
  · simp
  · rw [coeff_X_mul,coeff_zero_eq_eval_zero]
    have heval := (Polynomial.evalRingHom (0:ℚ)).map_det (M.updateCol j (fun i => (w i).divX))
    change ((M.updateCol j (fun i => (w i).divX)).det).eval 0=_ at heval
    rw [heval]
    congr 1
    apply Matrix.ext
    intro a b
    by_cases hb : b=j
    · subst b
      simp only [RingHom.mapMatrix_apply,Matrix.map_apply,Matrix.updateCol_self]
      change (w a).divX.eval 0=_
      rw [← coeff_zero_eq_eval_zero,coeff_divX,zero_add,hw1]
    · simp [RingHom.mapMatrix_apply,hb,← coeff_zero_eq_eval_zero]

end OscillatoryRecurrence
