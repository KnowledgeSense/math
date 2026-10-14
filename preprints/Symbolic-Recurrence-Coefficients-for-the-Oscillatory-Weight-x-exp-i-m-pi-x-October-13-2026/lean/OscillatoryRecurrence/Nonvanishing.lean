import OscillatoryRecurrence.Determinants
import OscillatoryRecurrence.TranscendencePi
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.LinearAlgebra.Vandermonde

noncomputable section
open Polynomial Finset
open scoped BigOperators
namespace OscillatoryRecurrence

lemma endpointMoment_eval_zero (r : ℕ) : (endpointMoment r).eval 0 = 2*(r+1).factorial := by
  induction r with
  | zero => norm_num [endpointMoment]
  | succ r ih =>
    rw [endpointMoment]
    simp only [eval_add,eval_mul,eval_C,eval_pow,eval_X,ih]
    by_cases he : Even (r+1)
    · have hdiv : (r+1)/2 ≠ 0 := by obtain ⟨k,hk⟩ := he; omega
      simp [he,zero_pow hdiv,Nat.factorial_succ]
      ring
    · simp [he,Nat.factorial_succ]
      ring

lemma factorial_hankel_positive (n : ℕ) :
    0 < Matrix.det (fun i j : Fin n => (2 : ℚ)*(i.val+j.val+1).factorial) := by
  let v : Fin n → ℚ := fun i => (i.val+2 : ℕ)
  let p : Fin n → ℚ[X] := fun j => ascPochhammer ℚ j.val
  let E : Matrix (Fin n) (Fin n) ℚ := Matrix.of (fun i j => (p j).eval (v i))
  have hd : E.det = (Matrix.vandermonde v).det :=
    (Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde v p
      (fun j => ascPochhammer_natDegree ℚ j.val) (fun j => monic_ascPochhammer ℚ j.val)).symm
  have hE : 0 < E.det := by
    rw [hd,Matrix.det_vandermonde]
    apply prod_pos
    intro i hi
    apply prod_pos
    intro j hj
    apply sub_pos.mpr
    have h := Finset.mem_Ioi.mp hj
    dsimp [v]
    exact_mod_cast (show i.val+2 < j.val+2 by omega)
  have heq : (fun i j : Fin n => (2 : ℚ)*(i.val+j.val+1).factorial) =
      Matrix.of (fun i j => (2*((i.val+1).factorial : ℚ))*E i j) := by
    ext i j
    dsimp [E,p,v]
    rw [ascPochhammer_nat_eq_natCast_ascFactorial]
    have h := Nat.factorial_mul_ascFactorial (i.val+1) j.val
    have hc : ((i.val+1).factorial : ℚ)*((i.val+2).ascFactorial j.val : ℚ) =
        ((i.val+j.val+1).factorial : ℚ) := by exact_mod_cast h.trans (by congr 1; omega)
    linear_combination -2*hc
  rw [heq,Matrix.det_mul_column]
  exact mul_pos (prod_pos (fun i _ => by positivity)) hE

lemma polynomialHankel_eval_zero_pos (n : ℕ) : 0 < (polynomialHankel n).eval 0 := by
  have h := (Polynomial.evalRingHom (0 : ℚ)).map_det
    (fun i j : Fin n => endpointMoment (i.val+j.val))
  change (polynomialHankel n).eval 0 =
    Matrix.det (fun i j : Fin n => (endpointMoment (i.val+j.val)).eval 0) at h
  simp only [endpointMoment_eval_zero] at h
  rw [h]
  exact factorial_hankel_positive n

lemma polynomialHankel_ne_zero (n : ℕ) : polynomialHankel n ≠ 0 := by
  intro h
  have hp := polynomialHankel_eval_zero_pos n
  simp [h] at hp

lemma integral_frequency_transcendental (m : ℤ) (hm : m ≠ 0) :
    Transcendental ℚ ((m : ℝ)*Real.pi) := by
  intro ha
  apply TranscendencePi.transcendental_pi
  have h := (isAlgebraic_intCast (R := ℚ) (A := ℝ) m).inv.mul ha
  have hmc : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  simpa only [← mul_assoc, inv_mul_cancel₀ hmc, one_mul] using h

lemma squared_frequency_transcendental (m : ℤ) (hm : m ≠ 0) :
    Transcendental ℚ ((((m : ℝ)*Real.pi)^2 : ℝ) : ℂ) := by
  have h := (integral_frequency_transcendental m hm).pow (show 0 < 2 by decide)
  exact (transcendental_algebraMap_iff (R := ℚ) (S := ℝ) (A := ℂ)
    Complex.ofReal_injective).mpr h

lemma polynomialHankel_frequency_ne_zero (m : ℤ) (hm : m ≠ 0) (n : ℕ) :
    (polynomialHankel n).eval₂ (Rat.castHom ℂ) ((((m : ℝ)*Real.pi)^2 : ℝ) : ℂ) ≠ 0 := by
  intro h
  apply squared_frequency_transcendental m hm
  exact ⟨polynomialHankel n, polynomialHankel_ne_zero n, h⟩

/-- All genuine moment Hankel determinants are nonzero at every allowed integer frequency. -/
theorem hankel_ne_zero (m : ℤ) (hm : m ≠ 0) (n : ℕ) :
    hankel ((m : ℝ)*Real.pi) n ≠ 0 := by
  have ht := integral_frequency_ne_zero m hm
  have h := exponential_hankel_normalization _ _ ht
    (integral_frequency_exp m) (integral_frequency_exp_neg m) n
  have hz : -(Complex.I*((m : ℝ)*Real.pi))^2 = (((m : ℝ)*Real.pi)^2 : ℂ) := by
    rw [mul_pow,Complex.I_sq]
    ring
  rw [hz] at h
  have hs : (-1 : ℂ)^m ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hp := polynomialHankel_frequency_ne_zero m hm n
  simp only [Complex.ofReal_pow,Complex.ofReal_mul] at hp
  intro hzero
  have hzero' : Matrix.det (fun i j : Fin n =>
      exponentialMoment (Complex.I*((m : ℝ)*Real.pi)) (i.val+j.val+1)) = 0 := by
    simpa only [hankel,moment,Complex.ofReal_mul] using hzero
  rw [hzero',mul_zero] at h
  exact (mul_ne_zero (pow_ne_zero _ hs) hp) h.symm

end OscillatoryRecurrence
