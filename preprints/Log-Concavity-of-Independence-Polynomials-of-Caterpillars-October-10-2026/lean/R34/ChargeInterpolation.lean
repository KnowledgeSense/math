import R34.SignExpansion
import R34.ChargePath

open scoped BigOperators Classical

namespace R34.ChargeInterpolation

noncomputable section

open MvPolynomial

def equalityIndicator (sizes : List ℕ) (hs : ∀ a ∈ sizes, 0 < a)
    (χ : ChargeColorings sizes) (e : ChargeEdges sizes) : ℝ :=
  if (chargeEndpoints sizes hs χ e).1 = (chargeEndpoints sizes hs χ e).2 then 1 else 0

def affineColorSum {O : Type*} [Fintype O]
    (sizes : List ℕ) (hs : ∀ a ∈ sizes, 0 < a)
    (c : O → ℝ) (a b : O → ChargeEdges sizes → ℝ) : Poly :=
  ∑ χ : ChargeColorings sizes, chargeWeight sizes χ *
    C (SignExpansion.affineSum c a b (equalityIndicator sizes hs χ))

theorem edge_interpolation (sizes : List ℕ) (hs : ∀ a ∈ sizes, 0 < a)
    (χ : ChargeColorings sizes) (ε : ChargeEdges sizes → Bool) (e : ChargeEdges sizes) :
    1 + SignExpansion.sign (ε e) * equalityIndicator sizes hs χ e =
      edgeWeight (1 + SignExpansion.sign (ε e))
        (chargeEndpoints sizes hs χ e).1 (chargeEndpoints sizes hs χ e).2 := by
  by_cases h : (chargeEndpoints sizes hs χ e).1 = (chargeEndpoints sizes hs χ e).2
  · simp [equalityIndicator, edgeWeight, h]
  · simp [equalityIndicator, edgeWeight, h]

theorem affineColorSum_expansion {O : Type*} [Fintype O]
    (sizes : List ℕ) (hs : ∀ a ∈ sizes, 0 < a)
    [DecidableEq (ChargeEdges sizes)]
    (c : O → ℝ) (a b : O → ChargeEdges sizes → ℝ) :
    affineColorSum sizes hs c a b =
      C ((1 / 2 : ℝ) ^ Fintype.card (ChargeEdges sizes)) *
        ∑ ε : ChargeEdges sizes → Bool,
          C (SignExpansion.affineSum c a b (fun e => SignExpansion.sign (ε e))) *
            blockChainSum sizes hs (fun e => 1 + SignExpansion.sign (ε e)) := by
  unfold affineColorSum
  rw [SignExpansion.weighted_sign_identity (C : ℝ →+* Poly)
    (chargeWeight sizes) (equalityIndicator sizes hs) c a b]
  apply congrArg (fun p : Poly => C ((1 / 2 : ℝ) ^ Fintype.card (ChargeEdges sizes)) * p)
  apply Finset.sum_congr rfl
  intro ε hε
  apply congrArg (fun p : Poly =>
    C (SignExpansion.affineSum c a b (fun e => SignExpansion.sign (ε e))) * p)
  unfold blockChainSum chargeTerm
  apply Finset.sum_congr rfl
  intro χ hχ
  apply congrArg (fun p : Poly => chargeWeight sizes χ * p)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro e he
  rw [edge_interpolation]

theorem affineColorSum_schurPositive {O : Type*} [Fintype O]
    (sizes : List ℕ) (hs : ∀ a ∈ sizes, 0 < a)
    [DecidableEq (ChargeEdges sizes)]
    (c : O → ℝ) (a b : O → ChargeEdges sizes → ℝ)
    (hc : ∀ ε : ChargeEdges sizes → Bool,
      0 ≤ SignExpansion.affineSum c a b (fun e => SignExpansion.sign (ε e))) :
    SchurPositive (affineColorSum sizes hs c a b) := by
  rw [affineColorSum_expansion]
  apply schurPositive_scale _ (pow_nonneg (by norm_num) _)
  apply schurPositive_sum
  intro ε hε
  apply schurPositive_scale _ (hc ε)
  apply blockChainSum_schurPositive
  intro e
  cases h : ε e <;> norm_num [SignExpansion.sign, h]

end

end R34.ChargeInterpolation
