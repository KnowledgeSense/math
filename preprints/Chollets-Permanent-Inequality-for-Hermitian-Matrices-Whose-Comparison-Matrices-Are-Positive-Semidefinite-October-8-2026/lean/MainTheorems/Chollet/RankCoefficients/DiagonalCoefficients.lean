import MainTheorems.Chollet.RankCoefficients.DiagonalExpansion
import MainTheorems.Chollet.RankPolynomial
import MainTheorems.Chollet.ElementaryBounds
import Mathlib.Algebra.Polynomial.Roots

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem rankPolynomial_diagonal_expand (d x : I → ℂ) :
    rankPolynomial (Matrix.diagonal d) x =
      ∑ t ∈ (Finset.univ : Finset I).powerset,
        Polynomial.C ((t.card.factorial : ℂ) *
          (∏ i ∈ t, ((‖x i‖ ^ 2 : ℝ) : ℂ)) *
          ∏ i ∈ Finset.univ \ t, d i) * Polynomial.X ^ t.card := by
  apply Polynomial.funext
  intro s
  rw [rankPolynomial_eval, permanent_diagonal_rank]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem rankCoefficient_diagonal_expand (d : I → ℝ) (x : I → ℂ) (k : ℕ) :
    rankCoefficient (Matrix.diagonal (fun i => (d i : ℂ))) x k =
      (k.factorial : ℝ) * ∑ t ∈ (Finset.univ : Finset I).powersetCard k,
        (∏ i ∈ t, ‖x i‖ ^ 2) * ∏ i ∈ Finset.univ \ t, d i := by
  rw [rankCoefficient, rankPolynomial_diagonal_expand, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow, Complex.re_sum]
  rw [Finset.powersetCard_eq_filter, Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases htk : t.card = k
  · simp only [htk, ite_true]
    norm_cast
    ring
  · have hkt : k ≠ t.card := Ne.symm htk
    simp only [htk, hkt, ite_false, Complex.zero_re]

theorem diagonal_weight_factor (d r : I → ℝ) (hd : ∀ i, d i ≠ 0) (s : Finset I) :
    (∏ i ∈ s, r i) * (∏ i ∈ Finset.univ \ s, d i) =
      (∏ i, d i) * ∏ i ∈ s, r i / d i := by
  have hprod : (∏ i ∈ s, d i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hd i)
  have hsplit : (∏ i, d i) = (∏ i ∈ s, d i) * ∏ i ∈ Finset.univ \ s, d i := by
    rw [← Finset.prod_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  rw [hsplit, Finset.prod_div_distrib]
  field_simp

theorem rankCoefficient_diagonal_elementary (d : I → ℝ) (x : I → ℂ)
    (hd : ∀ i, d i ≠ 0) (k : ℕ) :
    rankCoefficient (Matrix.diagonal (fun i => (d i : ℂ))) x k =
      (∏ i, d i) * (k.factorial : ℝ) *
        ((Finset.univ : Finset I).val.map (fun i => ‖x i‖ ^ 2 / d i)).esymm k := by
  rw [rankCoefficient_diagonal_expand, Finset.esymm_map_val]
  have he : (∑ t ∈ (Finset.univ : Finset I).powersetCard k,
      (∏ i ∈ t, ‖x i‖ ^ 2) * ∏ i ∈ Finset.univ \ t, d i) =
      (∏ i, d i) * ∑ t ∈ (Finset.univ : Finset I).powersetCard k,
        ∏ i ∈ t, ‖x i‖ ^ 2 / d i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    exact diagonal_weight_factor d (fun i => ‖x i‖ ^ 2) hd t
  rw [he]
  ring

theorem rankCoefficient_diagonal_bound (d : I → ℝ) (x : I → ℂ)
    (hd : ∀ i, 0 < d i) (hm : ∑ i, ‖x i‖ ^ 2 / d i ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) :
    rankCoefficient (Matrix.diagonal (fun i => (d i : ℂ))) x k ≤
      rankCoefficient (Matrix.diagonal (fun i => (d i : ℂ))) x 1 ∧
    rankCoefficient (Matrix.diagonal (fun i => (d i : ℂ))) x 1 ≤
      rankCoefficient (Matrix.diagonal (fun i => (d i : ℂ))) x 0 := by
  let r := (Finset.univ : Finset I).val.map (fun i => ‖x i‖ ^ 2 / d i)
  have hr : ∀ v ∈ r, 0 ≤ v := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hv
    exact div_nonneg (sq_nonneg _) (hd i).le
  have hmass : r.sum ≤ 1 := hm
  have hprod : 0 ≤ ∏ i, d i := Finset.prod_nonneg (fun i _ => (hd i).le)
  have hfirst := mul_le_mul_of_nonneg_left
    (ResearchMain.Chollet.factorial_elementary_bound r hr hmass k hk) hprod
  have hzero := mul_le_mul_of_nonneg_left hmass hprod
  rw [rankCoefficient_diagonal_elementary d x (fun i => (hd i).ne') k,
    rankCoefficient_diagonal_elementary d x (fun i => (hd i).ne') 1,
    rankCoefficient_diagonal_elementary d x (fun i => (hd i).ne') 0]
  constructor
  · simpa only [r, Nat.factorial_one, Nat.cast_one, mul_one,
      ResearchMain.Chollet.elementary_one, mul_assoc] using hfirst
  · simpa only [r, Nat.factorial_one, Nat.factorial_zero, Nat.cast_one,
      mul_one, ResearchMain.Chollet.elementary_one, ResearchMain.Chollet.elementary_zero]
      using hzero

end ResearchMain.Chollet.RankCoefficients

