import MainTheorems.LocalPermutation.Moments
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace ResearchMain.LocalPermutation

open Classical

variable {K : Type} [Field K] [Fintype K]

noncomputable def setIndicator (T : Finset K) (a : K) : K := if a ∈ T then 1 else 0

noncomputable def switched (T : Finset K) (h : Equiv.Perm K) (a : K) : K := h a + setIndicator T a

theorem switched_bijective (S T : Finset K) (h : Equiv.Perm K)
    (himage : ∀ a, a ∈ T ↔ h a ∈ S) (hshift : ∀ a ∈ S, a + 1 ∈ S) :
    Function.Bijective (switched T h) := by
  have hinj : Function.Injective (switched T h) := by
    intro a b hab
    by_cases ha : a ∈ T <;> by_cases hb : b ∈ T
    · apply h.injective
      simpa only [switched, setIndicator, ite_eq_left ha, ite_eq_left hb, add_left_inj] using hab
    · have hsa : h a + 1 ∈ S := hshift (h a) ((himage a).mp ha)
      have hsb : h b ∉ S := fun hs => hb ((himage b).mpr hs)
      simp only [switched, setIndicator, ite_eq_left ha, ite_eq_right hb, add_zero] at hab
      exact (hsb (hab ▸ hsa)).elim
    · have hsa : h a ∉ S := fun hs => ha ((himage a).mpr hs)
      have hsb : h b + 1 ∈ S := hshift (h b) ((himage b).mp hb)
      simp only [switched, setIndicator, ite_eq_right ha, ite_eq_left hb, add_zero] at hab
      exact (hsa (hab.symm ▸ hsb)).elim
    · apply h.injective
      simpa only [switched, setIndicator, ite_eq_right ha, ite_eq_right hb, add_zero] using hab
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

noncomputable def switchFunction {n : ℕ} (T : Finset K) (h : Equiv.Perm K) (x : Fin n → K) : K :=
  (∑ i, h (x i)) + ∏ i, setIndicator T (x i)

omit [Fintype K] in
theorem indicator_product {σ : Type} [DecidableEq σ] (s : Finset σ) (T : Finset K) (x : σ → K) :
    (∏ i ∈ s, setIndicator T (x i)) = 0 ∨ (∏ i ∈ s, setIndicator T (x i)) = 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    by_cases hxi : x i ∈ T
    · simpa only [setIndicator, ite_eq_left hxi, one_mul] using ih
    · simp only [setIndicator, ite_eq_right hxi, zero_mul, true_or]

theorem switchFunction_localPermutation {n : ℕ} (S T : Finset K) (h : Equiv.Perm K)
    (himage : ∀ a, a ∈ T ↔ h a ∈ S) (hshift : ∀ a ∈ S, a + 1 ∈ S) :
    IsLocalPermutation (switchFunction (n := n) T h) := by
  intro i x
  let C : K := ∑ j ∈ Finset.univ \ {i}, h (x j)
  let D : K := ∏ j ∈ Finset.univ \ {i}, setIndicator T (x j)
  have hslice (a : K) : switchFunction T h (Function.update x i a) = h a + C + setIndicator T a * D := by
    have hs := Finset.sum_update_of_mem (s := Finset.univ) (Finset.mem_univ i) (h ∘ x) (h a)
    have hp := Finset.prod_update_of_mem (s := Finset.univ) (Finset.mem_univ i) (setIndicator T ∘ x) (setIndicator T a)
    rw [← Function.comp_update] at hs hp
    simp only [Function.comp_def] at hs hp
    exact congrArg₂ (· + ·) hs hp
  rcases indicator_product (Finset.univ \ {i}) T x with hD | hD
  · change D = 0 at hD
    have hfun : (fun a => switchFunction T h (Function.update x i a)) = fun a => h a + C := by
      funext a
      rw [hslice]
      rw [hD, mul_zero, add_zero]
    rw [hfun]
    exact (Equiv.addRight C).bijective.comp h.bijective
  · change D = 1 at hD
    have hfun : (fun a => switchFunction T h (Function.update x i a)) = fun a => switched T h a + C := by
      funext a
      rw [hslice]
      rw [hD, mul_one]
      dsimp [switched]
      ring
    rw [hfun]
    exact (Equiv.addRight C).bijective.comp (switched_bijective S T h himage hshift)

omit [Fintype K] in
theorem setIndicator_frobenius (p : ℕ) [Fact p.Prime] [CharP K p] (T : Finset K)
    (hT : ∀ a, a ^ p ∈ T ↔ a ∈ T) (a : K) : setIndicator T (a ^ p) = setIndicator T a ^ p := by
  unfold setIndicator
  simp only [hT a]
  split_ifs <;> simp [(Fact.out : p.Prime).ne_zero]

omit [Fintype K] in
theorem switchFunction_frobenius (p : ℕ) [Fact p.Prime] [CharP K p] {n : ℕ} (T : Finset K)
    (h : Equiv.Perm K) (hT : ∀ a, a ^ p ∈ T ↔ a ∈ T) (hh : ∀ a, h (a ^ p) = h a ^ p) :
    FrobeniusEquivariant p (switchFunction (n := n) T h) := by
  intro x
  change (∑ i, h (x i ^ p)) + (∏ i, setIndicator T (x i ^ p)) =
    frobenius K p ((∑ i, h (x i)) + ∏ i, setIndicator T (x i))
  rw [map_add, map_sum, map_prod]
  simp only [hh, setIndicator_frobenius p T hT, frobenius_def]

theorem setIndicator_sum (T : Finset K) : (∑ a : K, setIndicator T a * a) = ∑ a ∈ T, a := by
  simp only [setIndicator, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp

end ResearchMain.LocalPermutation
