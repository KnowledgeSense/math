import HilbertBipartite.HilbertLength
import Mathlib.RingTheory.Polynomial.HilbertPoly

open Finset Polynomial
namespace HilbertBipartite

/-- The convention used in the paper, as an actual polynomial in the power exponent. -/
noncomputable def hilbertSamuelExpression (n : ℕ) (e : ℕ → ℚ) : Polynomial ℚ :=
  ∑ i ∈ range (n+1), C ((-1 : ℚ)^i * e i) * preHilbertPoly ℚ (n-i) 1

theorem hilbertSamuelExpression_eval (n s : ℕ) (e : ℕ → ℚ) (hs : 1 ≤ s) :
    (hilbertSamuelExpression n e).eval (s : ℚ) =
      ∑ i ∈ range (n+1), (-1 : ℚ)^i * e i * ((s+n-i-1).choose (n-i) : ℚ) := by
  simp only [hilbertSamuelExpression, eval_finsetSum, eval_mul, eval_C]
  apply sum_congr rfl
  intro i hi
  have hin := mem_range.mp hi
  rw [preHilbertPoly_eq_choose_add_sub ℚ (n-i) (by omega : 1 ≤ s+(n-i))]
  rw [show s+(n-i)-1=s+n-i-1 by omega]

/-- The Hilbert--Samuel polynomial property is expressed only through literal module lengths. -/
def IsHilbertSamuelPolynomial (K : Type*) [Field K] (p q : ℕ) (P : Polynomial ℚ) : Prop :=
  ∃ N : ℕ, ∀ s > N,
    ((Module.length (MvPolynomial (Fin p ⊕ Fin q) K)
      (MvPolynomial (Fin p ⊕ Fin q) K ⧸ bipartiteIdeal K p q ^ s)).toNat : ℚ) = P.eval (s : ℚ)

/-- The numerator construction genuinely yields the Hilbert--Samuel polynomial. -/
theorem hilbertSamuelExpression_isHilbertSamuel (K : Type*) [Field K]
    (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    IsHilbertSamuelPolynomial K p q
      (hilbertSamuelExpression (p+q) (hilbertCoefficient p q)) := by
  refine ⟨0, fun s hs => ?_⟩
  rw [hilbertSamuelExpression_eval _ _ _ (by omega)]
  simpa only [Nat.add_assoc] using compositionLength_hilbertExpansion K p q s hp hq (by omega)

theorem hilbertSamuelPolynomial_unique (K : Type*) [Field K] (p q : ℕ)
    {P Q : Polynomial ℚ} (hP : IsHilbertSamuelPolynomial K p q P)
    (hQ : IsHilbertSamuelPolynomial K p q Q) : P = Q := by
  obtain ⟨NP, hP⟩ := hP
  obtain ⟨NQ, hQ⟩ := hQ
  apply eq_of_infinite_eval_eq
  apply ((Set.Ioi_infinite (max NP NQ)).image (Nat.cast_injective (R := ℚ)).injOn).mono
  rintro x ⟨s, hs, rfl⟩
  simp only [Set.mem_Ioi, max_lt_iff] at hs
  exact (hP s hs.1).symm.trans (hQ s hs.2)

theorem existsUnique_hilbertSamuelPolynomial (K : Type*) [Field K]
    (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ∃! P : Polynomial ℚ, IsHilbertSamuelPolynomial K p q P := by
  refine ⟨hilbertSamuelExpression (p+q) (hilbertCoefficient p q),
    hilbertSamuelExpression_isHilbertSamuel K p q hp hq, ?_⟩
  intro P hP
  exact hilbertSamuelPolynomial_unique K p q hP
    (hilbertSamuelExpression_isHilbertSamuel K p q hp hq)

theorem hilbertSamuelExpression_top_coeff (n : ℕ) (e : ℕ → ℚ) :
    (hilbertSamuelExpression n e).coeff n = e 0 * (n.factorial : ℚ)⁻¹ := by
  simp only [hilbertSamuelExpression, finsetSum_coeff, coeff_C_mul]
  rw [sum_eq_single 0]
  · simp [coeff_preHilbertPoly_self]
  · intro i hi hi0
    have hin := mem_range.mp hi
    rw [coeff_eq_zero_of_natDegree_lt (by
      rw [natDegree_preHilbertPoly]
      omega : (preHilbertPoly ℚ (n-i) 1).natDegree < n), mul_zero]
  · simp

theorem hilbertSamuelExpression_succ (n : ℕ) (e : ℕ → ℚ) :
    hilbertSamuelExpression (n+1) e =
      C (e 0) * preHilbertPoly ℚ (n+1) 1 -
        hilbertSamuelExpression n (fun i => e (i+1)) := by
  unfold hilbertSamuelExpression
  rw [sum_range_succ']
  simp only [pow_zero, one_mul, Nat.sub_zero, Nat.add_sub_add_right]
  have ht : (∑ i ∈ range (n+1),
      C ((-1 : ℚ)^(i+1)*e (i+1)) * preHilbertPoly ℚ (n-i) 1) =
      -(∑ i ∈ range (n+1), C ((-1 : ℚ)^i*e (i+1)) * preHilbertPoly ℚ (n-i) 1) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    rw [pow_succ]
    simp only [mul_neg_one, neg_mul, map_neg]
  rw [ht]
  ring

/-- The binomial convention uniquely determines its coefficient vector. -/
theorem hilbertSamuelExpression_injective (n : ℕ) (e f : ℕ → ℚ)
    (h : hilbertSamuelExpression n e = hilbertSamuelExpression n f) :
    ∀ i ≤ n, e i = f i := by
  have hzero (n : ℕ) (e f : ℕ → ℚ)
      (h : hilbertSamuelExpression n e = hilbertSamuelExpression n f) : e 0 = f 0 := by
    have ht := congrArg (fun P : Polynomial ℚ => P.coeff n) h
    rw [hilbertSamuelExpression_top_coeff, hilbertSamuelExpression_top_coeff] at ht
    exact mul_right_cancel₀ (inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n)) ht
  induction n generalizing e f with
  | zero =>
    intro i hi
    have hi0 : i=0 := by omega
    simpa [hi0] using hzero 0 e f h
  | succ n ih =>
    have hz := hzero (n+1) e f h
    have ht : hilbertSamuelExpression n (fun i => e (i+1)) =
        hilbertSamuelExpression n (fun i => f (i+1)) := by
      rw [hilbertSamuelExpression_succ, hilbertSamuelExpression_succ, hz] at h
      exact sub_right_inj.mp h
    intro i hi
    cases i with
    | zero => exact hz
    | succ i => exact ih (fun j => e (j+1)) (fun j => f (j+1)) ht i (by omega)

/-- Hilbert coefficients in Samuel's eventual-polynomial convention, defined using
only actual polynomial-ring module lengths. -/
def IsHilbertCoefficientFamily (K : Type*) [Field K] (p q : ℕ) (e : ℕ → ℚ) : Prop :=
  IsHilbertSamuelPolynomial K p q (hilbertSamuelExpression (p+q) e)

theorem hilbertCoefficient_is_family (K : Type*) [Field K]
    (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    IsHilbertCoefficientFamily K p q (hilbertCoefficient p q) :=
  hilbertSamuelExpression_isHilbertSamuel K p q hp hq

theorem hilbertCoefficient_unique (K : Type*) [Field K]
    (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (e : ℕ → ℚ)
    (he : IsHilbertCoefficientFamily K p q e) :
    ∀ i ≤ p+q, e i = hilbertCoefficient p q i := by
  apply hilbertSamuelExpression_injective
  exact hilbertSamuelPolynomial_unique K p q he
    (hilbertCoefficient_is_family K p q hp hq)

end HilbertBipartite
