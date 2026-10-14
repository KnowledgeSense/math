import MainTheorems.Hypercomb.Counting
import MainTheorems.Hypercomb.RootSector
import MainTheorems.Hypercomb.SectorLogConcavity

namespace ResearchMain.Hypercomb

open Polynomial

theorem combValue_polynomial_aeval (a : ℝ) (n : ℕ) (z : ℂ) :
    aeval z (combValue (C a) X n) = combValue (a : ℂ) z n := by
  simpa using combValue_map (aeval z).toRingHom (C a) X n

theorem combValue_polynomial_coeff_zero (a : ℝ) (n : ℕ) :
    (combValue (C a) X n).coeff 0 = 1 := by
  have h := combValue_map (constantCoeff : ℝ[X] →+* ℝ) (C a) X n
  simpa only [constantCoeff_apply, coeff_C_zero, coeff_X_zero, combValue_zero] using h

theorem hypercomb_root_arg (a n : ℕ) (ha : 2 ≤ a) (z : ℂ)
    (hz : aeval z (strongIndependencePolynomial a n) = 0) : 2 * Real.pi / 3 < |z.arg| := by
  rw [strongIndependencePolynomial_eq a (by omega), combValue_polynomial_aeval] at hz
  exact combValue_root_arg a (by exact_mod_cast ha) n z hz

theorem hypercomb_roots_leftCone (a n : ℕ) (ha : 2 ≤ a) :
    RootsInLeftCone (strongIndependencePolynomial a n) := by
  intro z hz
  have harg := hypercomb_root_arg a n ha z hz
  have hzne : z ≠ 0 := by
    intro he
    subst z
    rw [strongIndependencePolynomial_eq a (by omega), combValue_polynomial_aeval, combValue_zero] at hz
    norm_num at hz
  exact leftCone_of_arg hzne harg

theorem hypercomb_coeff_zero (a n : ℕ) (ha : 1 ≤ a) : (strongIndependencePolynomial a n).coeff 0 = 1 := by
  rw [strongIndependencePolynomial_eq a ha, combValue_polynomial_coeff_zero]

theorem coefficientSequence_nat (p : ℝ[X]) (k : ℕ) : coefficientSequence p k = p.coeff k := by
  simp [coefficientSequence]

theorem coefficientSequence_nat_succ (p : ℝ[X]) (k : ℕ) :
    coefficientSequence p ((k : ℤ) + 1) = p.coeff (k + 1) := by
  rw [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by omega, coefficientSequence_nat]

theorem hypercomb_logConcave (a n : ℕ) (ha : 2 ≤ a) (k : ℕ) (hk : 0 < k) :
    strongIndependenceCount a n (k - 1) * strongIndependenceCount a n (k + 1) ≤
      strongIndependenceCount a n k ^ 2 := by
  have h := sector_coefficients_logConcave (strongIndependencePolynomial a n)
    (hypercomb_coeff_zero a n (by omega)) (hypercomb_roots_leftCone a n ha) (k : ℤ)
  rw [show (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) by omega,
    coefficientSequence_nat_succ, coefficientSequence_nat, coefficientSequence_nat,
    strongIndependencePolynomial_coeff, strongIndependencePolynomial_coeff, strongIndependencePolynomial_coeff] at h
  exact_mod_cast h

theorem hypercomb_unimodal (a n : ℕ) (ha : 2 ≤ a) : ∃ m : ℕ,
    (∀ k < m, strongIndependenceCount a n k ≤ strongIndependenceCount a n (k + 1)) ∧
    (∀ k ≥ m, strongIndependenceCount a n (k + 1) ≤ strongIndependenceCount a n k) := by
  obtain ⟨m, hincr, hdecr⟩ := sector_coefficients_unimodal (strongIndependencePolynomial a n)
    (hypercomb_coeff_zero a n (by omega)) (hypercomb_roots_leftCone a n ha)
  refine ⟨m, ?_, ?_⟩
  · intro k hk
    have h := hincr k hk
    rw [coefficientSequence_nat, coefficientSequence_nat_succ,
      strongIndependencePolynomial_coeff, strongIndependencePolynomial_coeff] at h
    exact_mod_cast h
  · intro k hk
    have h := hdecr k hk
    rw [coefficientSequence_nat, coefficientSequence_nat_succ,
      strongIndependencePolynomial_coeff, strongIndependencePolynomial_coeff] at h
    exact_mod_cast h

theorem uniform_hypercomb (n ℓ : ℕ) (hℓ : 3 ≤ ℓ) :
    (∀ z : ℂ, aeval z (strongIndependencePolynomial (ℓ - 1) n) = 0 → 2 * Real.pi / 3 < |z.arg|) ∧
    (∀ k : ℕ, 0 < k → strongIndependenceCount (ℓ - 1) n (k - 1) * strongIndependenceCount (ℓ - 1) n (k + 1) ≤
      strongIndependenceCount (ℓ - 1) n k ^ 2) ∧
    (∃ m : ℕ, (∀ k < m, strongIndependenceCount (ℓ - 1) n k ≤ strongIndependenceCount (ℓ - 1) n (k + 1)) ∧
      (∀ k ≥ m, strongIndependenceCount (ℓ - 1) n (k + 1) ≤ strongIndependenceCount (ℓ - 1) n k)) := by
  have ha : 2 ≤ ℓ - 1 := by omega
  exact ⟨hypercomb_root_arg _ _ ha, hypercomb_logConcave _ _ ha, hypercomb_unimodal _ _ ha⟩

end ResearchMain.Hypercomb
