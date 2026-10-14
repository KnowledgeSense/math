import MainTheorems.LocalPermutation.SwitchingMoments
import MainTheorems.LocalPermutation.OneVariable
import Mathlib.Algebra.CharP.Two

namespace ResearchMain.LocalPermutation

open Classical

variable {K : Type} [Field K] [Fintype K] [CharP K 2]

noncomputable def binarySupport : Finset K := Finset.univ \ {0, 1}

omit [CharP K 2] in
theorem mem_binarySupport (a : K) : a ∈ binarySupport ↔ a ≠ 0 ∧ a ≠ 1 := by
  simp [binarySupport, not_or]

theorem binarySupport_shift (a : K) (ha : a ∈ binarySupport) : a + 1 ∈ binarySupport := by
  obtain ⟨ha0, ha1⟩ := (mem_binarySupport a).mp ha
  apply (mem_binarySupport _).mpr
  constructor
  · intro h
    have he : a = 1 := by
      have he := eq_neg_of_add_eq_zero_left h
      rwa [CharTwo.neg_eq] at he
    exact ha1 he
  · intro h
    apply ha0
    exact add_right_cancel (by simpa only [zero_add] using h)

theorem binarySupport_frobenius (a : K) : a ^ 2 ∈ binarySupport ↔ a ∈ binarySupport := by
  have h0 : a ^ 2 = 0 ↔ a = 0 := pow_eq_zero_iff (by decide : 2 ≠ 0)
  have h1 : a ^ 2 = 1 ↔ a = 1 := by
    constructor
    · intro h
      apply (frobenius K 2).injective
      simpa only [frobenius_def, one_pow] using h
    · intro h
      simp only [h, one_pow]
  simp only [mem_binarySupport, ne_eq, h0, h1]

theorem binarySupport_sum (hq : 2 < Fintype.card K) : (∑ a ∈ binarySupport (K := K), a) = 1 := by
  have hs : (∑ a : K, a) = 0 := by
    simpa only [pow_one] using FiniteField.sum_pow_lt_card_sub_one K 1 (by omega)
  rw [binarySupport, Finset.sum_sdiff_eq_sub (Finset.subset_univ {0, 1}), hs]
  simp [CharTwo.neg_eq]

theorem characteristic_two_maximum_degree (hq : 2 < Fintype.card K) {n : ℕ} (hn : 1 ≤ n) :
    HasMaximumDegree K n := by
  by_cases hn1 : n = 1
  · subst n
    exact one_variable_maximum_degree 2 hq
  · apply switching_maximum_degree 2 hq (by omega : 2 ≤ n) binarySupport binarySupport (Equiv.refl K)
    · exact fun _ => Iff.rfl
    · exact binarySupport_shift
    · exact binarySupport_frobenius
    · exact fun _ => rfl
    · rw [binarySupport_sum hq]
      exact one_ne_zero

end ResearchMain.LocalPermutation
