import MainTheorems.LocalPermutation.SwitchingMoments

namespace ResearchMain.LocalPermutation

open Classical

variable {K : Type} [Field K]

noncomputable def doubleSwap (A : Finset K) (x : K) : K :=
  if x ∈ A then 2 * x else if (2 : K)⁻¹ * x ∈ A then (2 : K)⁻¹ * x else x

theorem doubleSwap_involutive (A : Finset K) (h2 : (2 : K) ≠ 0)
    (hdisj : ∀ x ∈ A, 2 * x ∉ A) : Function.Involutive (doubleSwap A) := by
  have hl (x : K) : (2 : K)⁻¹ * (2 * x) = x := by rw [← mul_assoc, inv_mul_cancel₀ h2, one_mul]
  have hr (x : K) : (2 : K) * ((2 : K)⁻¹ * x) = x := by rw [← mul_assoc, mul_inv_cancel₀ h2, one_mul]
  intro x
  by_cases hx : x ∈ A
  · simp only [doubleSwap, hx, hdisj x hx, hl, ite_true, ite_false]
  · by_cases hx' : (2 : K)⁻¹ * x ∈ A
    · simp only [doubleSwap, hx, hx', ite_true, ite_false, hr]
    · simp only [doubleSwap, ite_eq_right hx, ite_eq_right hx']

noncomputable def doubleExchange (A : Finset K) (h2 : (2 : K) ≠ 0)
    (hdisj : ∀ x ∈ A, 2 * x ∉ A) : Equiv.Perm K :=
  (doubleSwap_involutive A h2 hdisj).toPerm

theorem mem_double_image (A : Finset K) (h2 : (2 : K) ≠ 0) (x : K) :
    x ∈ A.image (fun a => 2 * a) ↔ (2 : K)⁻¹ * x ∈ A := by
  constructor
  · intro h
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp h
    rw [← he, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]
    exact ha
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨(2 : K)⁻¹ * x, h, ?_⟩
    rw [← mul_assoc, mul_inv_cancel₀ h2, one_mul]

noncomputable def exchangeSupport (S A : Finset K) : Finset K :=
  (S \ A) ∪ A.image (fun a => 2 * a)

theorem doubleExchange_image (S A : Finset K) (h2 : (2 : K) ≠ 0) (hA : A ⊆ S)
    (houtside : ∀ x ∈ A, 2 * x ∉ S) (x : K) :
    x ∈ exchangeSupport S A ↔ doubleExchange A h2 (fun x hx => fun h => houtside x hx (hA h)) x ∈ S := by
  change x ∈ exchangeSupport S A ↔ doubleSwap A x ∈ S
  simp only [exchangeSupport, Finset.mem_union, Finset.mem_sdiff, mem_double_image A h2]
  by_cases hx : x ∈ A
  · have hx' : (2 : K)⁻¹ * x ∉ A := by
      intro h
      have hout := houtside ((2 : K)⁻¹ * x) h
      rw [← mul_assoc, mul_inv_cancel₀ h2, one_mul] at hout
      exact hout (hA hx)
    simp only [hx, hx', not_true_eq_false, and_false, or_false, doubleSwap, ite_true, houtside x hx]
  · by_cases hx' : (2 : K)⁻¹ * x ∈ A
    · simp only [hx, hx', not_false_eq_true, and_true, or_true, doubleSwap, ite_false, ite_true, hA hx']
    · simp only [hx, hx', not_false_eq_true, and_true, or_false, doubleSwap, ite_false]

theorem doubleExchange_frobenius (p : ℕ) [Fact p.Prime] [CharP K p] (A : Finset K)
    (h2 : (2 : K) ≠ 0) (hdisj : ∀ x ∈ A, 2 * x ∉ A)
    (hA : ∀ x, x ^ p ∈ A ↔ x ∈ A) (x : K) :
    doubleExchange A h2 hdisj (x ^ p) = doubleExchange A h2 hdisj x ^ p := by
  have hpow : (2 : K) ^ p = 2 := by
    simpa only [frobenius_def, Nat.cast_ofNat] using map_natCast (frobenius K p) 2
  have he (x : K) : ((2 : K)⁻¹ * x) ^ p = (2 : K)⁻¹ * x ^ p := by
    rw [mul_pow, inv_pow, hpow]
  change doubleSwap A (x ^ p) = doubleSwap A x ^ p
  unfold doubleSwap
  simp only [← he, hA]
  split_ifs <;> simp only [he, mul_pow, hpow]

theorem exchangeSupport_frobenius (p : ℕ) [Fact p.Prime] [CharP K p] (S A : Finset K)
    (h2 : (2 : K) ≠ 0) (hS : ∀ x, x ^ p ∈ S ↔ x ∈ S) (hA : ∀ x, x ^ p ∈ A ↔ x ∈ A) (x : K) :
    x ^ p ∈ exchangeSupport S A ↔ x ∈ exchangeSupport S A := by
  have hpow : (2 : K) ^ p = 2 := by
    simpa only [frobenius_def, Nat.cast_ofNat] using map_natCast (frobenius K p) 2
  have he : ((2 : K)⁻¹ * x) ^ p = (2 : K)⁻¹ * x ^ p := by rw [mul_pow, inv_pow, hpow]
  simp only [exchangeSupport, Finset.mem_union, Finset.mem_sdiff, mem_double_image A h2,
    hS, ← he, hA]

theorem exchangeSupport_sum (S A : Finset K) (h2 : (2 : K) ≠ 0) (hA : A ⊆ S)
    (houtside : ∀ x ∈ A, 2 * x ∉ S) (hS : (∑ x ∈ S, x) = 0) (hsum : (∑ x ∈ A, x) = 1) :
    (∑ x ∈ exchangeSupport S A, x) = 1 := by
  have hdisj : Disjoint (S \ A) (A.image (fun a => 2 * a)) := by
    rw [Finset.disjoint_left]
    intro x hxS hxA
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hxA
    exact houtside a ha (he ▸ (Finset.mem_sdiff.mp hxS).1)
  rw [exchangeSupport, Finset.sum_union hdisj, Finset.sum_sdiff_eq_sub hA, hS, hsum]
  rw [Finset.sum_image (fun a _ b _ h => mul_left_cancel₀ h2 h), ← Finset.mul_sum, hsum]
  ring

end ResearchMain.LocalPermutation
