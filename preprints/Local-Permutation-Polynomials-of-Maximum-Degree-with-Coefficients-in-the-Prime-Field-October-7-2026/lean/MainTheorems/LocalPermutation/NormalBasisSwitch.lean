import MainTheorems.LocalPermutation.BasisSupports
import MainTheorems.LocalPermutation.OrbitSwitch
import MainTheorems.LocalPermutation.OneVariable
import Mathlib.Algebra.Algebra.ZMod

namespace ResearchMain.LocalPermutation

open Classical Module

variable {K : Type} [Field K] [Fintype K] (p : ℕ) [Fact p.Prime] [CharP K p]

omit [Fintype K] [Fact p.Prime] in
theorem small_cast_ne_zero {k : ℕ} (hk : 0 < k) (hkp : k < p) : (k : K) ≠ 0 := by
  rw [ne_eq, CharP.cast_eq_zero_iff K p k]
  exact Nat.not_dvd_of_pos_of_lt hk hkp

theorem normalized_basis_maximum_degree [Algebra (ZMod p) K] [Nontrivial (K ≃ₐ[ZMod p] K)]
    (hp : 3 < p) (hq : 2 < Fintype.card K) (b : Basis (K ≃ₐ[ZMod p] K) (ZMod p) K)
    (hsum : (∑ i, b i) = 1) (hb : ∀ σ i, σ (b i) = b (σ * i))
    {n : ℕ} (hn : 1 ≤ n) : HasMaximumDegree K n := by
  have h2 : (2 : K) ≠ 0 := by exact_mod_cast small_cast_ne_zero (K := K) p (k := 2) (by omega) (by omega)
  have h2F : (2 : ZMod p) ≠ 0 := by exact_mod_cast small_cast_ne_zero (K := ZMod p) p (k := 2) (by omega) (by omega)
  have h3F : (3 : ZMod p) ≠ 0 := by exact_mod_cast small_cast_ne_zero (K := ZMod p) p (k := 3) (by omega) (by omega)
  let S := basisCosets b
  let A := basisSupport b
  have hA : A ⊆ S := basisSupport_subset b
  have houtside : ∀ x ∈ A, 2 * x ∉ S := by
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
    rw [← hi]
    exact twice_basis_not_mem_cosets b hsum h3F i
  have hdisj : ∀ x ∈ A, 2 * x ∉ A := fun x hx h => houtside x hx (hA h)
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K
  have hσ (x : K) : σ x = x ^ p := by
    change FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K x = x ^ p
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card]
  have hS : ∀ x, x ^ p ∈ S ↔ x ∈ S := fun x => by rw [← hσ]; exact basisCosets_map_iff b hb σ x
  have hAfrob : ∀ x, x ^ p ∈ A ↔ x ∈ A := fun x => by rw [← hσ]; exact basisSupport_map_iff b hb σ x
  by_cases hn1 : n = 1
  · subst n
    exact one_variable_maximum_degree p hq
  · apply switching_maximum_degree p hq (by omega : 2 ≤ n) S (exchangeSupport S A) (doubleExchange A h2 hdisj)
    · exact doubleExchange_image S A h2 hA houtside
    · exact basisCosets_shift b
    · exact exchangeSupport_frobenius p S A h2 hS hAfrob
    · exact doubleExchange_frobenius p A h2 hdisj hAfrob
    · rw [exchangeSupport_sum S A h2 hA houtside
        (basisCosets_sum b hsum h2F (by rw [ZMod.card]; omega)) (basisSupport_sum b hsum)]
      exact one_ne_zero

theorem extension_maximum_degree (hp : 3 < p) (hcard : p < Fintype.card K) {n : ℕ} (hn : 1 ≤ n) :
    HasMaximumDegree K n := by
  let : Algebra (ZMod p) K := ZMod.algebra K p
  have hpow := FiniteField.pow_finrank_eq_card p K
  have hrank : 2 ≤ finrank (ZMod p) K := by
    by_contra h
    have hr : finrank (ZMod p) K ≤ 1 := by omega
    by_cases h0 : finrank (ZMod p) K = 0
    · rw [h0, pow_zero] at hpow
      omega
    · have h1 : finrank (ZMod p) K = 1 := by omega
      rw [h1, pow_one] at hpow
      omega
  have hgal : 1 < Fintype.card (K ≃ₐ[ZMod p] K) := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]
    omega
  let : Nontrivial (K ≃ₐ[ZMod p] K) := Fintype.one_lt_card_iff_nontrivial.mp hgal
  obtain ⟨b, hsum, hb⟩ := exists_normalized_normalBasis (ZMod p) K
  exact normalized_basis_maximum_degree p hp (by omega) b hsum hb hn

end ResearchMain.LocalPermutation
