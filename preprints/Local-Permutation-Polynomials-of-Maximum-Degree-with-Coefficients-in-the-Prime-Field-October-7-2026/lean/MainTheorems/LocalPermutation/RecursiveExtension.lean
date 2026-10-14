import MainTheorems.LocalPermutation.Moments
import MainTheorems.LocalPermutation.InverseSums
import Mathlib.Data.Fin.Tuple.Basic

namespace ResearchMain.LocalPermutation

open Classical Polynomial

variable {K : Type} [Field K] [Fintype K]

def extendFunction {n : ℕ} (e : Equiv.Perm K) (f : (Fin n → K) → K) (x : Fin (n + 1) → K) : K :=
  e ((f (Fin.tail x))⁻¹ + (x 0)⁻¹)

omit [Fintype K] in
theorem extendFunction_localPermutation {n : ℕ} (e : Equiv.Perm K) {f : (Fin n → K) → K}
    (hf : IsLocalPermutation f) : IsLocalPermutation (extendFunction e f) := by
  intro i x
  rw [← Fin.cons_self_tail x]
  cases i using Fin.cases with
  | zero =>
    simp only [Fin.update_cons_zero, extendFunction, Fin.tail_cons, Fin.cons_zero]
    exact e.bijective.comp ((Equiv.addLeft (f (Fin.tail x))⁻¹).bijective.comp inv_bijective)
  | succ j =>
    simp only [← Fin.cons_update, extendFunction, Fin.tail_cons, Fin.cons_zero]
    exact e.bijective.comp ((Equiv.addRight (x 0)⁻¹).bijective.comp (inv_bijective.comp (hf j (Fin.tail x))))

omit [Fintype K] in
theorem extendFunction_frobenius (p : ℕ) [Fact p.Prime] [CharP K p] {n : ℕ}
    (e : Equiv.Perm K) (he : ∀ a, e (a ^ p) = e a ^ p) {f : (Fin n → K) → K}
    (hf : FrobeniusEquivariant p f) : FrobeniusEquivariant p (extendFunction e f) := by
  intro x
  change e ((f (fun i => x i.succ ^ p))⁻¹ + (x 0 ^ p)⁻¹) =
    e ((f (Fin.tail x))⁻¹ + (x 0)⁻¹) ^ p
  have hfx := hf (Fin.tail x)
  change f (fun i => x i.succ ^ p) = (f (Fin.tail x)) ^ p at hfx
  rw [hfx, ← inv_pow, ← inv_pow, ← add_pow_char, he]

theorem extendFunction_moment (hq : 2 < Fintype.card K) {n : ℕ} (e : Equiv.Perm K)
    (f : (Fin n → K) → K) (H : K → K) (P : K[X]) (hP : P.natDegree < Fintype.card K)
    (heval : ∀ z, P.eval z = H (e z)) :
    weightedMoment (fun x => H (extendFunction e f x)) =
      -weightedMoment (fun x => P.derivative.eval (f x)⁻¹) := by
  have hsum := Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => K))
    (fun x => H (extendFunction e f x) * ∏ i, x i)
  change (∑ x : K × (Fin n → K), H (extendFunction e f (Fin.cons x.1 x.2)) *
    ∏ i, Fin.cons x.1 x.2 i) = _ at hsum
  unfold weightedMoment
  rw [← hsum, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [extendFunction, Fin.tail_cons, Fin.cons_zero, Fin.prod_univ_succ, Fin.cons_succ]
  have hs (x : Fin n → K) :
      (∑ a : K, H (e ((f x)⁻¹ + a⁻¹)) * (a * ∏ i, x i)) =
        -(P.derivative.eval (f x)⁻¹ * ∏ i, x i) := by
    have hi := Equiv.sum_comp (Equiv.inv K)
      (fun a => H (e ((f x)⁻¹ + a⁻¹)) * a)
    change (∑ a : K, H (e ((f x)⁻¹ + (a⁻¹)⁻¹)) * a⁻¹) =
      ∑ a : K, H (e ((f x)⁻¹ + a⁻¹)) * a at hi
    simp only [inv_inv, ← heval] at hi
    simp_rw [← heval, ← mul_assoc]
    rw [← Finset.sum_mul, ← hi, sum_eval_add_mul_inverse hq hP, neg_mul]
  simp_rw [hs]
  rw [Finset.sum_neg_distrib]

end ResearchMain.LocalPermutation
