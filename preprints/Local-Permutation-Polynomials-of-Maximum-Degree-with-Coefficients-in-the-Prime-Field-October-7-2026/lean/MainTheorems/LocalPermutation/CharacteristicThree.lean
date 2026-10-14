import MainTheorems.LocalPermutation.CharacteristicThreeMoments
import MainTheorems.LocalPermutation.OneVariable

namespace ResearchMain.LocalPermutation

open Classical Polynomial

variable {K : Type} [Field K] [Fintype K]

noncomputable def recursiveLPP : (n : ℕ) → (Fin (n + 1) → K) → K
  | 0 => fun x => x 0
  | n + 1 => extendFunction (Equiv.swap 0 1) (recursiveLPP n)

omit [Fintype K] in
theorem recursiveLPP_localPermutation (n : ℕ) : IsLocalPermutation (recursiveLPP (K := K) n) := by
  induction n with
  | zero =>
    change IsLocalPermutation (fun x : Fin 1 → K => x 0)
    intro i x
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [Function.update_self]
    exact Function.bijective_id
  | succ n ih => exact extendFunction_localPermutation (Equiv.swap 0 1) ih

omit [Fintype K] in
theorem recursiveLPP_frobenius (p : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ) :
    FrobeniusEquivariant p (recursiveLPP (K := K) n) := by
  induction n with
  | zero => exact fun _ => rfl
  | succ n ih => exact extendFunction_frobenius p (Equiv.swap 0 1) (transposition_frobenius p) ih

variable [CharP K 3]

theorem recursiveLPP_state_moments (hq : 3 < Fintype.card K) (n : ℕ) :
    weightedMoment (fun x => stateA (recursiveLPP (K := K) n x)) = (-1) ^ n ∧
    weightedMoment (fun x => stateB (recursiveLPP (K := K) n x)) = (-1) ^ n := by
  induction n with
  | zero =>
    exact ⟨by simpa only [recursiveLPP, pow_zero] using stateA_moment hq,
      by simpa only [recursiveLPP, pow_zero] using stateB_moment hq⟩
  | succ n ih =>
    constructor
    · change weightedMoment (fun x => stateA (extendFunction (Equiv.swap 0 1) (recursiveLPP n) x)) = _
      rw [extendFunction_moment (by omega) (Equiv.swap 0 1) (recursiveLPP n) stateA
        stateAPolynomial (stateAPolynomial_degree hq) (fun z => by rw [eval_stateAPolynomial hq, stateA_swap])]
      simp_rw [derivative_stateAPolynomial hq]
      rw [ih.2, pow_succ]
      ring
    · change weightedMoment (fun x => stateB (extendFunction (Equiv.swap 0 1) (recursiveLPP n) x)) = _
      rw [extendFunction_moment (by omega) (Equiv.swap 0 1) (recursiveLPP n) stateB
        stateBSwappedPolynomial (stateBSwappedPolynomial_degree hq) (eval_stateBSwappedPolynomial hq)]
      simp_rw [derivative_stateBSwappedPolynomial hq]
      rw [ih.1, pow_succ]
      ring

theorem recursiveLPP_moment (hq : 3 < Fintype.card K) (n : ℕ) :
    weightedMoment (recursiveLPP (K := K) (n + 1)) = -((-1) ^ n) := by
  change weightedMoment (fun x => id (extendFunction (Equiv.swap 0 1) (recursiveLPP n) x)) = _
  rw [extendFunction_moment (by omega) (Equiv.swap 0 1) (recursiveLPP n) id
    transpositionPolynomial (transpositionPolynomial_degree (by omega)) (eval_transpositionPolynomial (K := K))]
  simp_rw [derivative_transposition_inv hq]
  rw [(recursiveLPP_state_moments hq n).1]

theorem characteristic_three_maximum_degree (hq : 3 < Fintype.card K) {n : ℕ} (hn : 1 ≤ n) :
    HasMaximumDegree K n := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => exact one_variable_maximum_degree 3 (by omega)
    | succ n =>
      apply exists_maximum_degree 3 (by omega) (recursiveLPP_localPermutation (n + 1)) (recursiveLPP_frobenius 3 (n + 1))
      rw [recursiveLPP_moment hq]
      exact neg_ne_zero.mpr (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

end ResearchMain.LocalPermutation
