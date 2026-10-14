import OscillatoryRecurrence.OriginalRecurrence

noncomputable section
open Polynomial
open scoped BigOperators Matrix
namespace OscillatoryRecurrence

theorem determinant_LU_certificate {n : ℕ} (A L U : Matrix (Fin n) (Fin n) ℚ)
    (hA : A=L*U) (hL : L.IsLowerTriangular) (hU : U.IsUpperTriangular) :
    A.det=(∏i,L i i)*(∏i,U i i) := by
  rw [hA,Matrix.det_mul,Matrix.det_of_isLowerTriangular L hL,Matrix.det_of_isUpperTriangular hU]

theorem polynomialHankel_eval (n : ℕ) (x : ℚ) :
    (polynomialHankel n).eval x=
      (Matrix.of (fun i j : Fin n => (endpointMoment (i.val+j.val)).eval x)).det := by
  exact (Polynomial.evalRingHom x).map_det _

theorem polynomialBorder_eval (n : ℕ) (hn : 0<n) (x : ℚ) :
    (polynomialBorder n).eval x=
      (Matrix.of (fun i j : Fin n => (endpointMoment (i.val+borderColumn n j)).eval x)).det := by
  unfold polynomialBorder
  rw [ite_eq_right (Nat.ne_of_gt hn)]
  exact (Polynomial.evalRingHom x).map_det _

theorem recurrenceFamily_hankel_eq {n : ℕ} (hn : 2≤n) (p : ℚ[X]) (c : ℚ)
    (hc : c≠0) (hp : p.Monic) (h : polynomialHankel n=C c*p) :
    recurrenceFamily (hankelDegree n)=p := by
  have hl : (polynomialHankel n).leadingCoeff=c := by
    rw [h,leadingCoeff_mul,leadingCoeff_C,hp.leadingCoeff,mul_one]
  rw [recurrenceFamily_hankel hn,normalizedHankel,hl,h]
  calc
    _ = C (c*c⁻¹)*p := by rw [map_mul]; ring
    _ = p := by simp [hc]

theorem recurrenceFamily_numerator_eq {n : ℕ} (hn : 4≤n) (p : ℚ[X]) (c : ℚ)
    (hc : c≠0) (hp : p.Monic) (h : polynomialNumerator n=X*(C c*p)) :
    recurrenceFamily (hankelDegree n-1)=p := by
  have hd : (polynomialNumerator n).divX=C c*p := by
    apply mul_left_cancel₀ (X_ne_zero : (X:ℚ[X])≠0)
    rw [polynomialNumerator_divX_identity,h]
  have hl : (polynomialNumerator n).divX.leadingCoeff=c := by
    rw [hd,leadingCoeff_mul,leadingCoeff_C,hp.leadingCoeff,mul_one]
  rw [recurrenceFamily_numerator hn,normalizedNumerator,hl,hd]
  calc
    _ = C (c*c⁻¹)*p := by rw [map_mul]; ring
    _ = p := by simp [hc]

end OscillatoryRecurrence
