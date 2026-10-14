import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace R34.SignExpansion

noncomputable section

/-- The two signs used in the interpolation formula. -/
def sign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem sign_false : sign false = -1 := rfl
@[simp] theorem sign_true : sign true = 1 := rfl

theorem affine_sign_identity (a b z : ℝ) :
    a + b * z = ∑ ε : Bool, (1 / 2 : ℝ) * (a + b * sign ε) * (1 + sign ε * z) := by
  simp [sign]
  ring

theorem product_sign_identity {E : Type*} [Fintype E] [DecidableEq E]
    (a b z : E → ℝ) :
    (∏ e, (a e + b e * z e)) =
      (1 / 2 : ℝ) ^ Fintype.card E *
        ∑ ε : E → Bool, (∏ e, (a e + b e * sign (ε e))) *
          ∏ e, (1 + sign (ε e) * z e) := by
  calc
    (∏ e, (a e + b e * z e)) =
        ∏ e, ∑ ε : Bool, (1 / 2 : ℝ) * (a e + b e * sign ε) *
          (1 + sign ε * z e) := by
      apply Finset.prod_congr rfl
      intro e he
      exact affine_sign_identity _ _ _
    _ = ∑ ε : E → Bool, ∏ e, ((1 / 2 : ℝ) *
        (a e + b e * sign (ε e)) * (1 + sign (ε e) * z e)) :=
      Fintype.prod_sum _
    _ = (1 / 2 : ℝ) ^ Fintype.card E *
        ∑ ε : E → Bool, (∏ e, (a e + b e * sign (ε e))) *
          ∏ e, (1 + sign (ε e) * z e) := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ε hε
      ring

/-- A sum of products with at most one affine factor for each edge. -/
def affineSum {O E : Type*} [Fintype O] [Fintype E]
    (c : O → ℝ) (a b : O → E → ℝ) (z : E → ℝ) : ℝ :=
  ∑ o, c o * ∏ e, (a o e + b o e * z e)

theorem affineSum_sign_identity {O E : Type*} [Fintype O] [Fintype E]
    [DecidableEq E] (c : O → ℝ) (a b : O → E → ℝ) (z : E → ℝ) :
    affineSum c a b z =
      (1 / 2 : ℝ) ^ Fintype.card E *
        ∑ ε : E → Bool, affineSum c a b (fun e => sign (ε e)) *
          ∏ e, (1 + sign (ε e) * z e) := by
  unfold affineSum
  calc
    (∑ o, c o * ∏ e, (a o e + b o e * z e)) =
        ∑ o, c o * ((1 / 2 : ℝ) ^ Fintype.card E *
          ∑ ε : E → Bool, (∏ e, (a o e + b o e * sign (ε e))) *
            ∏ e, (1 + sign (ε e) * z e)) := by
      apply Finset.sum_congr rfl
      intro o ho
      rw [product_sign_identity]
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ε hε
      apply Finset.sum_congr rfl
      intro o ho
      ring

/-- Interpolation commutes with any finite polynomial-valued coloring sum. -/
theorem weighted_sign_identity {O E K : Type*} [Fintype O] [Fintype E]
    [Fintype K] [DecidableEq E] {P : Type*} [CommRing P]
    (ι : ℝ →+* P) (w : K → P) (z : K → E → ℝ)
    (c : O → ℝ) (a b : O → E → ℝ) :
    (∑ k, w k * ι (affineSum c a b (z k))) =
      ι ((1 / 2 : ℝ) ^ Fintype.card E) *
        ∑ ε : E → Bool, ι (affineSum c a b (fun e => sign (ε e))) *
          ∑ k, w k * ∏ e, ι (1 + sign (ε e) * z k e) := by
  calc
    (∑ k, w k * ι (affineSum c a b (z k))) =
        ∑ k, w k * ι ((1 / 2 : ℝ) ^ Fintype.card E *
          ∑ ε : E → Bool, affineSum c a b (fun e => sign (ε e)) *
            ∏ e, (1 + sign (ε e) * z k e)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [affineSum_sign_identity]
    _ = _ := by
      simp only [map_mul, map_sum, map_prod, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ε hε
      apply Finset.sum_congr rfl
      intro k hk
      ring
end

end R34.SignExpansion



