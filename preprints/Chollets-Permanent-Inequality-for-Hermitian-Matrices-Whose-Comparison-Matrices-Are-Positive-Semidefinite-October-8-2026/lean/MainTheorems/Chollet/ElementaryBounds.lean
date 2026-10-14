import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic

namespace ResearchMain.Chollet

theorem elementary_zero (s : Multiset ℝ) : s.esymm 0 = 1 := by
  simp [Multiset.esymm]

theorem elementary_one (s : Multiset ℝ) : s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]

theorem elementary_cons (s : Multiset ℝ) (x : ℝ) (k : ℕ) :
    (x ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + x * s.esymm k := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add, Multiset.map_map]
  simp only [Function.comp_def, Multiset.prod_cons]
  rw [Multiset.sum_map_mul_left]

theorem elementary_nonneg (s : Multiset ℝ) (hs : ∀ x ∈ s, 0 ≤ x) (k : ℕ) : 0 ≤ s.esymm k := by
  induction s using Multiset.induction_on generalizing k with
  | empty => cases k <;> simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons x s ih =>
    have hx : 0 ≤ x := hs x (Multiset.mem_cons_self x s)
    have ht : ∀ y ∈ s, 0 ≤ y := fun y hy => hs y (Multiset.mem_cons_of_mem hy)
    cases k with
    | zero => rw [elementary_zero]; norm_num
    | succ k =>
      rw [elementary_cons]
      exact add_nonneg (ih ht _) (mul_nonneg hx (ih ht _))

theorem elementary_mass (s : Multiset ℝ) (hs : ∀ x ∈ s, 0 ≤ x) (k : ℕ) :
    (k + 1 : ℕ) * s.esymm (k + 1) ≤ s.sum * s.esymm k := by
  induction s using Multiset.induction_on generalizing k with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons x s ih =>
    have hx : 0 ≤ x := hs x (Multiset.mem_cons_self x s)
    have ht : ∀ y ∈ s, 0 ≤ y := fun y hy => hs y (Multiset.mem_cons_of_mem hy)
    cases k with
    | zero => simp [elementary_one]
    | succ k =>
      have h₁ := ih ht (k + 1)
      have h₂ := mul_le_mul_of_nonneg_left (ih ht k) hx
      have h₃ := mul_nonneg (sq_nonneg x) (elementary_nonneg s ht k)
      rw [elementary_cons, elementary_cons, Multiset.sum_cons]
      push_cast at *
      nlinarith

theorem factorial_elementary_step (s : Multiset ℝ) (hs : ∀ x ∈ s, 0 ≤ x)
    (hm : s.sum ≤ 1) (k : ℕ) :
    ((k + 1).factorial : ℝ) * s.esymm (k + 1) ≤ (k.factorial : ℝ) * s.esymm k := by
  have h₁ := elementary_mass s hs k
  have h₂ := mul_le_mul_of_nonneg_right hm (elementary_nonneg s hs k)
  have h₃ := mul_le_mul_of_nonneg_left (h₁.trans (by simpa using h₂))
    (Nat.cast_nonneg k.factorial : (0 : ℝ) ≤ k.factorial)
  rw [Nat.factorial_succ]
  push_cast at h₃ ⊢
  nlinarith

theorem factorial_elementary_bound (s : Multiset ℝ) (hs : ∀ x ∈ s, 0 ≤ x)
    (hm : s.sum ≤ 1) (k : ℕ) (hk : 1 ≤ k) :
    (k.factorial : ℝ) * s.esymm k ≤ s.sum := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  induction j with
  | zero => simp [elementary_one]
  | succ j ih =>
    exact (factorial_elementary_step s hs hm (j + 1)).trans (ih (by omega))

end ResearchMain.Chollet
