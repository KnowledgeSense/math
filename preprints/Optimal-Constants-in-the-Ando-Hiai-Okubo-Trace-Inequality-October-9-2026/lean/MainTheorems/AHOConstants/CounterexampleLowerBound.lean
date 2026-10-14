import MainTheorems.AHOConstants.CounterexampleActive
import MainTheorems.AHOConstants.CutMonomials
import MainTheorems.AHOConstants.FlowFactorization

namespace ResearchMain.AHOConstants

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem counterexampleActivePair_summand_lower {ε z : ℝ} (hε : 0 < ε)
    (hz : 0 < z) (hz' : z ≤ 1 / 8) (p q : ℝ) (large : Bool) (i j : Fin 2) :
    (1 / 16 : ℝ) * ε ^ ((if large then 0 else p) + if j = 0 then q else 0) *
        z ^ ((if large = true ∧ i = 1 then (1 : ℕ) else 0) +
          if large = true ∧ j = 1 then 1 else 0) ≤
      counterexampleActivePair ε z p q i j := by
  let w : ℝ := if large then 1 else ε ^ p
  let c : ℝ := if j = 0 then ε ^ q else 1
  let vi : ℝ := activeEigenvector z large i
  let vj : ℝ := activeEigenvector z large j
  let li : ℝ := (1 / 4 : ℝ) * if large = true ∧ i = 1 then z else 1
  let lj : ℝ := (1 / 4 : ℝ) * if large = true ∧ j = 1 then z else 1
  have hw : 0 ≤ w := by dsimp [w]; split_ifs <;> positivity
  have hc : 0 ≤ c := by dsimp [c]; split_ifs <;> positivity
  have hli : 0 ≤ li := by dsimp [li]; split_ifs <;> positivity
  have hlj : 0 ≤ lj := by dsimp [lj]; split_ifs <;> positivity
  have hvi : 0 ≤ vi := (activeEigenvector_positive hz hz' large i).le
  have hvj : 0 ≤ vj := (activeEigenvector_positive hz hz' large j).le
  have hi : li ≤ vi := activeEigenvector_lower hz hz' large i
  have hj : lj ≤ vj := activeEigenvector_lower hz hz' large j
  have hl : w * li * lj * c ≤ w * vi * vj * c := by
    have hpair := mul_le_mul hi hj hlj hvi
    have h := mul_le_mul_of_nonneg_left hpair hw
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h hc
  have hs : w * vi * vj * c ≤ counterexampleActivePair ε z p q i j := by
    have hsmall : 0 ≤ ε ^ p * activeEigenvector z false i * activeEigenvector z false j :=
      mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos hε _).le
        (activeEigenvector_positive hz hz' false i).le)
        (activeEigenvector_positive hz hz' false j).le
    have hlarge : 0 ≤ activeEigenvector z true i * activeEigenvector z true j :=
      mul_nonneg (activeEigenvector_positive hz hz' true i).le
        (activeEigenvector_positive hz hz' true j).le
    apply mul_le_mul_of_nonneg_right _ hc
    cases large <;> dsimp [w, vi, vj, counterexampleActivePair] at * <;> nlinarith
  have he : w * li * lj * c =
      (1 / 16 : ℝ) * ε ^ ((if large then 0 else p) + if j = 0 then q else 0) *
        z ^ ((if large = true ∧ i = 1 then (1 : ℕ) else 0) +
          if large = true ∧ j = 1 then 1 else 0) := by
    rw [Real.rpow_add hε]
    cases large <;> fin_cases i <;> fin_cases j <;>
      norm_num [w, li, lj, c, pow_two] <;> ring
  exact he ▸ hl.trans hs

def cutWalk {m : ℕ} (T : Finset (Fin (m + 1))) (i : Fin (m + 1)) : Fin 2 :=
  if (finRotate (m + 1)).symm i ∈ T then 1 else 0

theorem cutWalk_next {m : ℕ} (T : Finset (Fin (m + 1))) (i : Fin (m + 1)) :
    cutWalk T (finRotate (m + 1) i) = if i ∈ T then 1 else 0 := by
  simp only [cutWalk, Equiv.symm_apply_apply]

theorem counterexample_cut_step_lower {m : ℕ} {ε z : ℝ} (hε : 0 < ε)
    (hz : 0 < z) (hz' : z ≤ 1 / 8) (p q : Fin (m + 1) → ℝ)
    (S T : Finset (Fin (m + 1))) (i : Fin (m + 1)) :
    (1 / 16 : ℝ) * ε ^ ((if i ∈ S then 0 else p i) + if i ∈ T then 0 else q i) *
        z ^ ((if i ∈ S ∧ (finRotate (m + 1)).symm i ∈ T then (1 : ℕ) else 0) +
          if i ∈ S ∧ i ∈ T then 1 else 0) ≤
      counterexampleActivePair ε z (p i) (q i)
        (cutWalk T i) (cutWalk T (finRotate (m + 1) i)) := by
  have h := counterexampleActivePair_summand_lower hε hz hz' (p i) (q i)
    (decide (i ∈ S)) (cutWalk T i) (cutWalk T (finRotate (m + 1) i))
  rw [cutWalk_next] at h
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    by_cases hprev : (finRotate (m + 1)).symm i ∈ T <;>
      simpa [cutWalk, hS, hT, hprev] using h

theorem counterexample_cut_trace_lower {m : ℕ} {ε z : ℝ} (hε : 0 < ε)
    (hz : 0 < z) (hz' : z ≤ 1 / 8) (p q : Fin (m + 1) → ℝ)
    (hp : (∑ i, p i) = 1) (hq : (∑ i, q i) = 1)
    (S T : Finset (Fin (m + 1))) :
    (1 / 16 : ℝ) ^ (m + 1) * ε ^ (2 - cutMass p S - cutMass q T) *
        z ^ (cutEdges S T).card ≤
      Matrix.trace (List.ofFn (fun i => counterexampleActivePair ε z (p i) (q i))).prod := by
  have hprod : (∏ i : Fin (m + 1),
      (1 / 16 : ℝ) * ε ^ ((if i ∈ S then 0 else p i) + if i ∈ T then 0 else q i) *
        z ^ ((if i ∈ S ∧ (finRotate (m + 1)).symm i ∈ T then (1 : ℕ) else 0) +
          if i ∈ S ∧ i ∈ T then 1 else 0)) ≤
      ∏ i : Fin (m + 1), counterexampleActivePair ε z (p i) (q i)
        (cutWalk T i) (cutWalk T (finRotate (m + 1) i)) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      positivity
    · intro i hi
      exact counterexample_cut_step_lower hε hz hz' p q S T i
  have hedges : (∑ i : Fin (m + 1),
      ((if i ∈ S ∧ (finRotate (m + 1)).symm i ∈ T then (1 : ℕ) else 0) +
        if i ∈ S ∧ i ∈ T then 1 else 0)) = (cutEdges S T).card := by
    rw [cutEdges_count_previous]
    apply Finset.sum_congr rfl
    intro i hi
    exact add_comm _ _
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hprod
  rw [← Real.rpow_sum_of_pos hε, cut_exponent_sum p q hp hq S T,
    Finset.prod_pow_eq_pow_sum, hedges] at hprod
  exact hprod.trans (closed_walk_term_le_trace_ofFn _
    (fun i => counterexampleActivePair_nonnegative hε hz hz' (p i) (q i)) (cutWalk T))

theorem counterexample_actual_trace_lower {m : ℕ} {ε z : ℝ} (hε₀ : 0 < ε)
    (hε₁ : ε < 1) (hz : 0 < z) (hz' : z ≤ 1 / 8)
    (p q : Fin (m + 1) → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hsum : (∑ i, p i) = 1) (hqsum : (∑ i, q i) = 1)
    (S T : Finset (Fin (m + 1))) :
    (1 / 16 : ℝ) ^ (m + 1) * ε ^ (2 - cutMass p S - cutMass q T) *
        z ^ (cutEdges S T).card ≤
      ‖wordTrace (counterexampleA ε z) (counterexampleB ε)
        (pairWord (List.ofFn (fun i => (p i, q i))))‖ := by
  unfold wordTrace
  rw [← pairProduct_eq_matrixWord]
  unfold pairProduct
  rw [List.map_ofFn]
  simp only [Function.comp_def]
  rw [counterexample_paired_product_trace_norm hε₀ hε₁ hz hz' p q hp hq]
  exact counterexample_cut_trace_lower hε₀ hz hz' p q hsum hqsum S T

end ResearchMain.AHOConstants
