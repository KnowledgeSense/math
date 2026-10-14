import MainTheorems.Domination.Compositions

namespace ResearchMain.Domination

open Classical

theorem antisymmetric_rectangle_nonneg {α : Type*} [DecidableEq α] (A B : Finset α)
    (hAB : A ⊆ B) (w : α → α → ℤ)
    (hswap : ∀ x ∈ A, ∀ y ∈ A, w x y = -w y x)
    (houtside : ∀ x ∈ A, ∀ y ∈ B \ A, 0 ≤ w x y) :
    0 ≤ ∑ x ∈ A, ∑ y ∈ B, w x y := by
  classical
  have hsmall : (∑ x ∈ A, ∑ y ∈ A, w x y) = 0 := by
    have heq : (∑ x ∈ A, ∑ y ∈ A, w x y) = -(∑ x ∈ A, ∑ y ∈ A, w x y) := by
      calc
        (∑ x ∈ A, ∑ y ∈ A, w x y) = ∑ y ∈ A, ∑ x ∈ A, w x y := Finset.sum_comm
        _ = ∑ y ∈ A, ∑ x ∈ A, -w y x := by
          apply Finset.sum_congr rfl
          intro y hy
          apply Finset.sum_congr rfl
          intro x hx
          exact hswap x hx y hy
        _ = -(∑ y ∈ A, ∑ x ∈ A, w y x) := by simp only [Finset.sum_neg_distrib]
    linarith
  have hsplit : (∑ x ∈ A, ∑ y ∈ B, w x y) =
      (∑ x ∈ A, ∑ y ∈ A, w x y) + ∑ x ∈ A, ∑ y ∈ B \ A, w x y := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    have h := Finset.sum_union (f := w x) (s₁ := A) (s₂ := B \ A)
      Finset.disjoint_sdiff
    rw [Finset.union_sdiff_of_subset hAB] at h
    exact h
  rw [hsplit, hsmall, zero_add]
  apply Finset.sum_nonneg
  intro x hx
  apply Finset.sum_nonneg
  intro y hy
  exact houtside x hx y hy

theorem endpoint_interior_weighted_difference_nonneg (q m : ℕ) (hqm : q ≤ m)
    (f : ℤ → ℤ) (hf : ∀ n, 0 ≤ f n) (N : ℤ) :
    0 ≤ ∑ a ∈ Finset.Icc 1 q, ∑ b ∈ Finset.Icc 1 m,
      ((b : ℤ) - a) * f (N - a - b) := by
  classical
  refine antisymmetric_rectangle_nonneg (Finset.Icc 1 q) (Finset.Icc 1 m) ?_
    (fun a b => ((b : ℤ) - a) * f (N - a - b)) ?_ ?_
  · intro a ha
    obtain ⟨ha1, haq⟩ := Finset.mem_Icc.mp ha
    exact Finset.mem_Icc.mpr ⟨ha1, haq.trans hqm⟩
  · intro a _ b _
    rw [show N - (a : ℤ) - b = N - b - a by ring]
    ring
  · intro a ha b hb
    obtain ⟨hbm, hbq⟩ := Finset.mem_sdiff.mp hb
    obtain ⟨hb1, _⟩ := Finset.mem_Icc.mp hbm
    obtain ⟨_, haq⟩ := Finset.mem_Icc.mp ha
    have hqb : q < b := by
      by_contra h
      exact hbq (Finset.mem_Icc.mpr ⟨hb1, by omega⟩)
    exact mul_nonneg (by omega) (hf _)

theorem endpoint_interior_composition_difference_nonneg {r : ℕ}
    (bounds : Fin r → ℕ) (q m : ℕ) (hqm : q ≤ m) (N : ℤ) :
    0 ≤ ∑ a ∈ Finset.Icc 1 q, ∑ b ∈ Finset.Icc 1 m,
      ((b : ℤ) - a) * compositionCountZ bounds (N - a - b) :=
  endpoint_interior_weighted_difference_nonneg q m hqm _ (compositionCountZ_nonneg bounds) N

end ResearchMain.Domination
