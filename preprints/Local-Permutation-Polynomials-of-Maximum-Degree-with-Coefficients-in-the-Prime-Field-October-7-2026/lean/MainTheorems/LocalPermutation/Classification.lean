import MainTheorems.LocalPermutation.CharacteristicTwo
import MainTheorems.LocalPermutation.CharacteristicThree
import MainTheorems.LocalPermutation.PrimeField
import MainTheorems.LocalPermutation.NormalBasisSwitch

namespace ResearchMain.LocalPermutation

open Classical MvPolynomial

variable {K : Type} [Field K] [Fintype K]

theorem maximum_degree (p : ℕ) [Fact p.Prime] [CharP K p]
    (hq : 3 < Fintype.card K) {n : ℕ} (hn : 1 ≤ n) : HasMaximumDegree K n := by
  by_cases hp2 : p = 2
  · subst p
    exact characteristic_two_maximum_degree (by omega) hn
  · by_cases hp3 : p = 3
    · subst p
      exact characteristic_three_maximum_degree hq hn
    · have hp : 3 < p := by have := (Fact.out : p.Prime).two_le; omega
      have hcard : p ≤ Fintype.card K := by
        simpa only [ZMod.card] using Fintype.card_le_of_injective
          (ZMod.castHom (dvd_refl p) K) (ZMod.castHom (dvd_refl p) K).injective
      by_cases heq : Fintype.card K = p
      · exact prime_field_maximum_degree p hp heq hn
      · exact extension_maximum_degree p hp (by omega) hn

omit [Fintype K] in
theorem exists_prime_polynomial (p : ℕ) [Fact p.Prime] [CharP K p] {n : ℕ}
    {P : MvPolynomial (Fin n) K} (hP : PrimeCoefficients P) :
    ∃ Q : MvPolynomial (Fin n) (ZMod p), map (ZMod.castHom (dvd_refl p) K) Q = P := by
  apply mem_range_map_iff_coeffs_subset.mpr
  intro c hc
  obtain ⟨d, _, hdc⟩ := mem_coeffs_iff.mp hc
  obtain ⟨m, hm⟩ := (mem_bot_iff_intCast p K).mp (hP d)
  refine ⟨(m : ZMod p), ?_⟩
  rw [map_intCast, hm, ← hdc]

theorem maximum_degree_over_prime_field (p : ℕ) [Fact p.Prime] [CharP K p]
    (hq : 3 < Fintype.card K) {n : ℕ} (hn : 1 ≤ n) :
    ∃ Q : MvPolynomial (Fin n) (ZMod p),
      IsLocalPermutation (fun x : Fin n → K => eval₂ (ZMod.castHom (dvd_refl p) K) x Q) ∧
      (∀ i, Q.degreeOf i ≤ Fintype.card K - 2) ∧ Q.totalDegree = n * (Fintype.card K - 2) := by
  obtain ⟨P, hP, hlocal, hcoord, hdegree⟩ := maximum_degree p hq hn
  obtain ⟨Q, hQ⟩ := exists_prime_polynomial p hP
  let φ := ZMod.castHom (dvd_refl p) K
  have hlocalQ : IsLocalPermutation (fun x : Fin n → K => eval₂ φ x Q) := by
    rw [← hQ] at hlocal
    simpa only [eval_map] using hlocal
  have hcoordQ (i : Fin n) : Q.degreeOf i ≤ Fintype.card K - 2 := by
    have h := hcoord i
    rw [← hQ, degreeOf_def, degrees_map_of_injective Q φ.injective, ← degreeOf_def] at h
    exact h
  have hdegreeQ : Q.totalDegree = n * (Fintype.card K - 2) := by
    rw [← hQ, totalDegree, support_map_of_injective Q φ.injective] at hdegree
    exact hdegree
  exact ⟨Q, hlocalQ, hcoordQ, hdegreeQ⟩

end ResearchMain.LocalPermutation
