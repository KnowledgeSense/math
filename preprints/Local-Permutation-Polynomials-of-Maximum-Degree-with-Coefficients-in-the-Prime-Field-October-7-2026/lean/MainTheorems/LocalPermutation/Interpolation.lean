import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace ResearchMain.LocalPermutation

open Classical MvPolynomial

universe u

variable {K σ : Type u} [Field K] [Fintype K] [Fintype σ]

def Reduced (P : MvPolynomial σ K) : Prop :=
  P ∈ restrictDegree σ K (Fintype.card K - 1)

omit [Fintype σ] in
theorem reduced_iff_degreeOf {P : MvPolynomial σ K} : Reduced P ↔ ∀ i, P.degreeOf i ≤ Fintype.card K - 1 := by
  simp only [Reduced, mem_restrictDegree, degreeOf_le_iff]
  constructor
  · exact fun h i d hd => h d hd i
  · exact fun h d hd i => h i d hd

noncomputable def interpolate (f : (σ → K) → K) : MvPolynomial σ K :=
  ∑ a, C (f a) * indicator a

theorem interpolate_reduced (f : (σ → K) → K) : Reduced (interpolate f) := by
  unfold Reduced interpolate
  apply Submodule.sum_mem
  intro a _
  simpa only [smul_eq_C_mul] using
    (restrictDegree σ K (Fintype.card K - 1)).smul_mem (f a) (indicator_mem_restrictDegree a)

theorem eval_interpolate (f : (σ → K) → K) (x : σ → K) : eval x (interpolate f) = f x := by
  classical
  simp only [interpolate, map_sum, map_mul, eval_C]
  rw [Finset.sum_eq_single x]
  · rw [eval_indicator_apply_eq_one, mul_one]
  · intro a _ hax
    rw [eval_indicator_apply_eq_zero x a (Ne.symm hax), mul_zero]
  · simp

theorem reduced_ext {P Q : MvPolynomial σ K} (hP : Reduced P) (hQ : Reduced Q)
    (h : ∀ x : σ → K, eval x P = eval x Q) : P = Q := by
  apply sub_eq_zero.mp
  exact MvPolynomial.eq_zero_of_eval_eq_zero σ K (P - Q)
    (fun x => by rw [map_sub, h x, sub_self])
    ((restrictDegree σ K (Fintype.card K - 1)).sub_mem hP hQ)

theorem interpolate_eval {P : MvPolynomial σ K} (hP : Reduced P) :
    interpolate (fun x => eval x P) = P :=
  reduced_ext (interpolate_reduced _) hP (eval_interpolate _)

omit [Fintype σ] in
theorem reduced_map (φ : K →+* K) {P : MvPolynomial σ K} (hP : Reduced P) : Reduced (map φ P) := by
  rw [Reduced, mem_restrictDegree] at hP ⊢
  exact fun d hd i => hP d (support_map_subset φ P hd) i

def FrobeniusEquivariant (p : ℕ) (f : (σ → K) → K) : Prop :=
  ∀ x, f (fun i => x i ^ p) = f x ^ p

def PrimeCoefficients (P : MvPolynomial σ K) : Prop :=
  ∀ d, P.coeff d ∈ (⊥ : Subfield K)

theorem interpolate_primeCoefficients (p : ℕ) [Fact p.Prime] [CharP K p]
    (f : (σ → K) → K) (hf : FrobeniusEquivariant p f) : PrimeCoefficients (interpolate f) := by
  let φ := frobenius K p
  have hsurj : Function.Surjective φ := Finite.surjective_of_injective φ.injective
  have hmap : map φ (interpolate f) = interpolate f := by
    apply reduced_ext (reduced_map φ (interpolate_reduced f)) (interpolate_reduced f)
    intro y
    choose x hx using fun i => hsurj (y i)
    have hxy : φ ∘ x = y := funext hx
    rw [← hxy, ← map_eval, eval_interpolate, eval_interpolate]
    exact (hf x).symm
  intro d
  apply (Subfield.mem_bot_iff_pow_eq_self K p).mpr
  have h := congrArg (fun P : MvPolynomial σ K => P.coeff d) hmap
  simpa only [coeff_map, φ, frobenius_def] using h

def IsLocalPermutation [DecidableEq σ] (f : (σ → K) → K) : Prop :=
  ∀ i x, Function.Bijective (fun a => f (Function.update x i a))

theorem inverse_power (hq : 2 < Fintype.card K) (x : K) : x ^ (Fintype.card K - 2) = x⁻¹ := by
  by_cases hx : x = 0
  · simp [hx, zero_pow (by omega : Fintype.card K - 2 ≠ 0)]
  · apply (mul_right_inj' hx).mp
    rw [mul_inv_cancel₀ hx, ← pow_succ', show Fintype.card K - 2 + 1 = Fintype.card K - 1 by omega]
    exact FiniteField.pow_card_sub_one_eq_one x hx

end ResearchMain.LocalPermutation
