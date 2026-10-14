import MainTheorems.LocalPermutation.RecursiveExtension

namespace ResearchMain.LocalPermutation

open Classical

variable {K : Type} [Field K] [Fintype K]

theorem pairing_swap (G : K → K) {a b : K} (hab : a ≠ b) :
    (∑ z : K, Equiv.swap a b z * G z) = (∑ z : K, z * G z) + (b - a) * (G a - G b) := by
  have he (z : K) : Equiv.swap a b z * G z = z * G z +
      (if z = a then (b - a) * G a else 0) + (if z = b then (a - b) * G b else 0) := by
    by_cases hza : z = a
    · subst z
      rw [Equiv.swap_apply_left, ite_eq_left rfl, ite_eq_right hab]
      ring
    · by_cases hzb : z = b
      · subst z
        rw [Equiv.swap_apply_right, ite_eq_right hab.symm, ite_eq_left rfl]
        ring
      · rw [Equiv.swap_apply_of_ne_of_ne hza hzb, ite_eq_right hza, ite_eq_right hzb]
        ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem exists_permutation_pairing (G : K → K) (hG : ∃ a b, G a ≠ G b) :
    ∃ e : Equiv.Perm K, (∑ z : K, e z * G z) ≠ 0 := by
  by_cases hid : (∑ z : K, z * G z) ≠ 0
  · exact ⟨Equiv.refl K, hid⟩
  · obtain ⟨a, b, habG⟩ := hG
    have hab : a ≠ b := fun h => habG (congrArg G h)
    refine ⟨Equiv.swap a b, ?_⟩
    rw [pairing_swap G hab, not_not.mp hid, zero_add]
    exact mul_ne_zero (sub_ne_zero.mpr hab.symm) (sub_ne_zero.mpr habG)

noncomputable def inverseKernel {n : ℕ} (f : (Fin n → K) → K) (z : K) : K :=
  ∑ x, (∏ i, x i) * (z - f x)⁻¹

theorem inverseKernel_second_moment (hq : 3 < Fintype.card K) {n : ℕ} (f : (Fin n → K) → K) :
    (∑ z : K, z ^ 2 * inverseKernel f z) = -2 * weightedMoment f := by
  have hs (a : K) : (∑ z : K, z ^ 2 * (z - a)⁻¹) = -2 * a := by
    have he := Equiv.sum_comp (Equiv.addLeft a) (fun z : K => z ^ 2 * (z - a)⁻¹)
    change (∑ z : K, (a + z) ^ 2 * (a + z - a)⁻¹) = _ at he
    simp only [add_sub_cancel_left] at he
    rw [← he]
    have hterm (z : K) : (a + z) ^ 2 * z⁻¹ =
        a ^ 2 * z⁻¹ + (2 * a) * (z * z⁻¹) + z ^ 2 * z⁻¹ := by ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_inverse (by omega), sum_mul_inverse, sum_power_mul_inverse (by omega) (by omega : 2 < Fintype.card K)]
    norm_num
  unfold inverseKernel weightedMoment
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm (x : Fin n → K) : (∑ z : K, z ^ 2 * ((∏ i, x i) * (z - f x)⁻¹)) =
      -2 * (f x * ∏ i, x i) := by
    have he (z : K) : z ^ 2 * ((∏ i, x i) * (z - f x)⁻¹) =
        (∏ i, x i) * (z ^ 2 * (z - f x)⁻¹) := by ring
    simp_rw [he]
    rw [← Finset.mul_sum, hs]
    ring
  simp_rw [hterm]

theorem inverseKernel_nonconstant (hq : 3 < Fintype.card K) (h2 : (2 : K) ≠ 0)
    {n : ℕ} {f : (Fin n → K) → K} (hf : weightedMoment f ≠ 0) :
    ∃ a b, inverseKernel f a ≠ inverseKernel f b := by
  by_contra h
  have hc (a : K) : inverseKernel f a = inverseKernel f 0 := by
    exact not_not.mp (not_exists.mp (not_exists.mp h a) 0)
  have hs : (∑ z : K, z ^ 2 * inverseKernel f z) = 0 := by
    simp_rw [hc]
    rw [← Finset.sum_mul, FiniteField.sum_pow_lt_card_sub_one K 2 (by omega), zero_mul]
  rw [inverseKernel_second_moment hq] at hs
  exact (mul_ne_zero (neg_ne_zero.mpr h2) hf) hs

end ResearchMain.LocalPermutation
