import MainTheorems.DominationRoots.DominationNumber
import Mathlib.RingTheory.Polynomial.Vieta

namespace ResearchMain.DominationRoots

open Polynomial

theorem esymm_one_eq_sum (s : Multiset ℝ) : s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]

theorem esymm_two_cons (x : ℝ) (s : Multiset ℝ) :
    (x ::ₘ s).esymm 2 = s.esymm 2 + x * s.sum := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add, Multiset.map_map]
  simp only [Function.comp_def, Multiset.prod_cons]
  rw [Multiset.sum_map_mul_left]
  change s.esymm 2 + x * s.esymm 1 = s.esymm 2 + x * s.sum
  rw [esymm_one_eq_sum]

theorem sum_squares_esymm_two (s : Multiset ℝ) :
    (s.map (fun x => x ^ 2)).sum = s.sum ^ 2 - 2 * s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons x s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons, esymm_two_cons, ih]
    ring

theorem split_root_sum {p : ℝ[X]} (hm : p.Monic) (hs : p.Splits) (hd : 1 ≤ p.natDegree) :
    p.roots.sum = -p.coeff (p.natDegree - 1) := by
  have h := coeff_eq_esymm_roots_of_splits hs (k := p.natDegree - 1) (Nat.sub_le _ _)
  have he : p.natDegree - (p.natDegree - 1) = 1 := by omega
  rw [hm.leadingCoeff, he, esymm_one_eq_sum] at h
  linarith

theorem split_root_square_sum {p : ℝ[X]} (hm : p.Monic) (hs : p.Splits)
    (hd : 2 ≤ p.natDegree) :
    (p.roots.map (fun x => x ^ 2)).sum =
      p.coeff (p.natDegree - 1) ^ 2 - 2 * p.coeff (p.natDegree - 2) := by
  have h := coeff_eq_esymm_roots_of_splits hs (k := p.natDegree - 2) (Nat.sub_le _ _)
  have he : p.natDegree - (p.natDegree - 2) = 2 := by omega
  rw [hm.leadingCoeff, he] at h
  norm_num at h
  rw [sum_squares_esymm_two, split_root_sum hm hs (by omega), ← h]
  ring

theorem nonnegativePolynomial_eval_positive {p : ℝ[X]} (hc : ∀ k, 0 ≤ p.coeff k)
    (h0 : 0 < p.coeff 0) {x : ℝ} (hx : 0 ≤ x) : 0 < p.eval x := by
  rw [eval_eq_sum_range]
  apply Finset.sum_pos'
  · intro k hk
    exact mul_nonneg (hc k) (pow_nonneg hx k)
  · exact ⟨0, Finset.mem_range.mpr (Nat.succ_pos _), by simpa using h0⟩

end ResearchMain.DominationRoots
