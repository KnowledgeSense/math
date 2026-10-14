import MainTheorems.LocalPermutation.FiniteSums
import Mathlib.Algebra.MvPolynomial.Equiv

namespace ResearchMain.LocalPermutation

open Classical MvPolynomial

variable {K : Type} [Field K] [Fintype K]

theorem finSucc_coeff_reduced {n : ℕ} {P : MvPolynomial (Fin (n + 1)) K} (hP : Reduced P) (k : ℕ) :
    Reduced ((finSuccEquiv K n P).coeff k) := by
  apply reduced_iff_degreeOf.mpr
  intro i
  exact (degreeOf_coeff_finSuccEquiv P i k).trans (reduced_iff_degreeOf.mp hP i.succ)

theorem first_coeff_last_zero (hq : 2 < Fintype.card K) {n : ℕ}
    {P : MvPolynomial (Fin (n + 1)) K} (hP : Reduced P)
    (hf : IsLocalPermutation (fun x => eval x P)) :
    (finSuccEquiv K n P).coeff (Fintype.card K - 1) = 0 := by
  apply MvPolynomial.eq_zero_of_eval_eq_zero (Fin n) K _ _ (finSucc_coeff_reduced hP _)
  intro x
  let Q := Polynomial.map (eval x) (finSuccEquiv K n P)
  have hdeg : Q.natDegree < Fintype.card K := by
    have h := (Polynomial.natDegree_map_le (f := eval x) (p := finSuccEquiv K n P)).trans
      ((natDegree_finSuccEquiv P).le.trans (reduced_iff_degreeOf.mp hP 0))
    change Q.natDegree ≤ Fintype.card K - 1 at h
    have := Fintype.card_pos (α := K)
    omega
  have hu (a : K) : Function.update (Fin.cons (0 : K) x : Fin (n + 1) → K) 0 a = Fin.cons a x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hbij : Function.Bijective Q.eval := by
    have h := hf 0 (Fin.cons (0 : K) x)
    simpa only [hu, eval_eq_eval_mv_eval'] using h
  have hzero := permutation_coeff_last_zero hq hdeg hbij
  simpa only [Q, Polynomial.coeff_map] using hzero

theorem first_degree_bound (hq : 2 < Fintype.card K) {n : ℕ}
    {P : MvPolynomial (Fin (n + 1)) K} (hP : Reduced P)
    (hf : IsLocalPermutation (fun x => eval x P)) : P.degreeOf 0 ≤ Fintype.card K - 2 := by
  have hdeg := reduced_iff_degreeOf.mp hP 0
  have hzero := first_coeff_last_zero hq hP hf
  by_cases hPzero : P = 0
  · simp [hPzero]
  · have hlast : P.degreeOf 0 ≠ Fintype.card K - 1 := by
      intro he
      rw [← he, ← natDegree_finSuccEquiv, Polynomial.coeff_natDegree,
        Polynomial.leadingCoeff_eq_zero] at hzero
      exact hPzero ((finSuccEquiv K n).injective (by simpa using hzero))
    omega

omit [Field K] [Fintype K] in
theorem localPermutation_rename {n : ℕ} (e : Equiv.Perm (Fin n))
    {f : (Fin n → K) → K} (hf : IsLocalPermutation f) : IsLocalPermutation (fun x => f (x ∘ e)) := by
  intro i x
  have hu (a : K) : Function.update x i a ∘ e = Function.update (x ∘ e) (e.symm i) a := by
    simpa only [e.apply_symm_apply] using Function.update_comp_eq_of_injective x e.injective (e.symm i) a
  simpa only [hu] using hf (e.symm i) (x ∘ e)

theorem degree_bound (hq : 2 < Fintype.card K) {n : ℕ} {P : MvPolynomial (Fin n) K}
    (hP : Reduced P) (hf : IsLocalPermutation (fun x => eval x P)) (i : Fin n) :
    P.degreeOf i ≤ Fintype.card K - 2 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let e := Equiv.swap i (0 : Fin (n + 1))
    have hrename : Reduced (rename e P) := by
      apply reduced_iff_degreeOf.mpr
      intro j
      simpa only [e.apply_symm_apply] using
        (degreeOf_rename_of_injective (p := P) e.injective (e.symm j)).le.trans (reduced_iff_degreeOf.mp hP (e.symm j))
    have hlocal : IsLocalPermutation (fun x => eval x (rename e P)) := by
      simpa only [eval_rename] using localPermutation_rename e hf
    have h := first_degree_bound hq hrename hlocal
    have he : (rename e P).degreeOf 0 = P.degreeOf i := by
      simpa only [e, Equiv.swap_apply_left] using degreeOf_rename_of_injective (p := P) e.injective i
    rwa [he] at h

end ResearchMain.LocalPermutation
