import MainTheorems.Corona.Basic
import MainTheorems.Corona.Shape
import MainTheorems.Hypercomb.Coefficients
import MainTheorems.Hypercomb.Unimodality

namespace ResearchMain.Corona

open Classical Polynomial
open ResearchMain.Hypercomb

theorem independencePolynomial_nonzero {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    independencePolynomial G ≠ 0 := by
  intro h
  have hc := independencePolynomial_constant G
  rw [h, coeff_zero] at hc
  norm_num at hc

theorem independencePolynomial_coeff_positive {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {k : ℕ} (hk : k ≤ (independencePolynomial G).natDegree) :
    0 < (independencePolynomial G).coeff k := by
  let e := (independencePolynomial G).natDegree
  have hc : (independencePolynomial G).coeff e ≠ 0 := leadingCoeff_ne_zero.mpr (independencePolynomial_nonzero G)
  have hcount : 0 < independentCount G e := by
    by_contra h
    have hzero : independentCount G e = 0 := by omega
    rw [independencePolynomial_coeff, hzero, Nat.cast_zero] at hc
    exact hc rfl
  obtain ⟨S, hS⟩ := Finset.card_pos.mp hcount
  obtain ⟨hSI, hSc⟩ := Finset.mem_filter.mp hS
  obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq (by omega : k ≤ S.card)
  have hTI := independent_mono G ((mem_independentSets _ _).mp hSI) hTS
  have hTmem : T ∈ (independentSets G).filter (fun R => R.card = k) :=
    Finset.mem_filter.mpr ⟨(mem_independentSets _ _).mpr hTI, hTc⟩
  rw [independencePolynomial_coeff]
  exact_mod_cast Finset.card_pos.mpr ⟨T, hTmem⟩

theorem logConcave_unimodal_of_interval {p : ℝ[X]} {e : ℕ}
    (hpositive : ∀ k ≤ e, 0 < p.coeff k) (hzero : ∀ k > e, p.coeff k = 0)
    (hLC : LogConcave (fun k => p.coeff k)) : Unimodal (fun k => p.coeff k) := by
  have hnonneg (k : ℕ) : 0 ≤ p.coeff k := by
    by_cases hk : k ≤ e
    · exact (hpositive k hk).le
    · rw [hzero k (by omega)]
  have hf : PositiveLC (coefficientSequence p) e := by
    constructor
    · intro k hk0 hke
      rw [coefficientSequence, ite_eq_left hk0]
      exact hpositive k.toNat (by omega)
    · intro k hk
      rcases hk with hk | hk
      · simp [coefficientSequence, show ¬0 ≤ k by omega]
      · by_cases hk0 : 0 ≤ k
        · rw [coefficientSequence, ite_eq_left hk0, hzero k.toNat (by omega)]
        · simp [coefficientSequence, hk0]
    · intro k
      by_cases hk : k ≤ 0
      · have hleft : coefficientSequence p (k - 1) = 0 := by
          rw [coefficientSequence, ite_eq_right (by omega)]
        rw [hleft, zero_mul]
        positivity
      · have hk0 : 0 ≤ k := by omega
        have hprev : 0 ≤ k - 1 := by omega
        have hnext : 0 ≤ k + 1 := by omega
        simp only [coefficientSequence, ite_eq_left hk0, ite_eq_left hprev, ite_eq_left hnext]
        rw [show (k - 1).toNat = k.toNat - 1 by omega,
          show (k + 1).toNat = k.toNat + 1 by omega]
        exact hLC k.toNat (by omega)
  obtain ⟨m, _, hup, hdown⟩ := hf.unimodal
  have he (k : ℕ) : coefficientSequence p (k : ℤ) = p.coeff k := by
    simp only [coefficientSequence, Nat.cast_nonneg, ite_true, Int.toNat_natCast]
  refine ⟨m, ?_, ?_⟩
  · intro k hk
    have h := hup k hk
    rw [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by omega, he, he] at h
    exact h
  · intro k hk
    have h := hdown k hk
    rw [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by omega, he, he] at h
    exact h

theorem independencePolynomial_scaled_unimodal {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {t : ℝ} (ht : 0 < t)
    (hLC : LogConcave (fun k => (independentCount G k : ℝ))) :
    Unimodal (fun k => ((independencePolynomial G).comp (C t * X)).coeff k) := by
  apply logConcave_unimodal_of_interval (e := (independencePolynomial G).natDegree)
  · intro k hk
    rw [comp_C_mul_X_coeff]
    exact mul_pos (independencePolynomial_coeff_positive G hk) (pow_pos ht k)
  · intro k hk
    rw [comp_C_mul_X_coeff, coeff_eq_zero_of_natDegree_lt hk, zero_mul]
  · have h := hLC.geometric_scale ht.le
    have he : (fun k => ((independencePolynomial G).comp (C t * X)).coeff k) =
        (fun k => t ^ k * (independentCount G k : ℝ)) := by
      funext k
      rw [comp_C_mul_X_coeff, independencePolynomial_coeff]
      ring
    rw [he]
    exact h

end ResearchMain.Corona
