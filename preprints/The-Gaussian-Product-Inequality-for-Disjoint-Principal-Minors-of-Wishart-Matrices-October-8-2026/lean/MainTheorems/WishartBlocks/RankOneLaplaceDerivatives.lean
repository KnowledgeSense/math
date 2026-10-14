import MainTheorems.WishartBlocks.RankOneWishartLaw
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ResearchMain.WishartBlocks

open MeasureTheory
open scoped InnerProductSpace Topology

noncomputable def rankOneLaplaceExpectation {p : ℕ} (q : ℝ)
    (S T : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (θ : ℝ) : ℝ :=
  ∫ W, Real.exp (-Matrix.trace (T * W))
    ∂(oneRowWishartLaw q S (Real.sqrt θ • v))

noncomputable def rankOneLaplaceRate {p : ℕ}
    (S T : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ⟪v, (T * (1 + (2 : ℝ) • (S * T))⁻¹).toEuclideanLin v⟫_ℝ

theorem rankOneLaplaceExpectation_eq {p : ℕ} {q θ : ℝ} (hq : (p : ℝ) < q)
    (hθ : 0 ≤ θ) {S T : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hT : T.PosSemidef) (v : EuclideanSpace ℝ (Fin p)) :
    rankOneLaplaceExpectation q S T v θ =
      (1 + (2 : ℝ) • (S * T)).det ^ (-q / 2) *
        Real.exp (-rankOneLaplaceRate S T v * θ) := by
  rw [rankOneLaplaceExpectation, oneRowWishart_rankOne_laplace hq hθ hS hT]
  dsimp only [rankOneLaplaceRate]
  congr 2
  ring

theorem rankOneLaplaceExpectation_hasDerivAt {p : ℕ} {q θ : ℝ}
    (hq : (p : ℝ) < q) (hθ : 0 < θ)
    {S T : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (hT : T.PosSemidef)
    (v : EuclideanSpace ℝ (Fin p)) :
    HasDerivAt (rankOneLaplaceExpectation q S T v)
      (-rankOneLaplaceRate S T v * rankOneLaplaceExpectation q S T v θ) θ := by
  let a := rankOneLaplaceRate S T v
  let C := (1 + (2 : ℝ) • (S * T)).det ^ (-q / 2)
  have he : rankOneLaplaceExpectation q S T v =ᶠ[𝓝 θ]
      fun t : ℝ => C * Real.exp (-a * t) := by
    filter_upwards [eventually_gt_nhds hθ] with t ht
    exact rankOneLaplaceExpectation_eq hq ht.le hS hT v
  have hd := (((hasDerivAt_id' θ).const_mul (-a)).exp).const_mul C
  have hd' : HasDerivAt (fun t : ℝ => C * Real.exp (-a * t))
      (-a * rankOneLaplaceExpectation q S T v θ) θ := by
    rw [rankOneLaplaceExpectation_eq hq hθ.le hS hT v]
    convert hd using 1
    ring
  exact hd'.congr_of_eventuallyEq he

theorem rankOneLaplaceExpectation_hasSecondDerivAt {p : ℕ} {q θ : ℝ}
    (hq : (p : ℝ) < q) (hθ : 0 < θ)
    {S T : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (hT : T.PosSemidef)
    (v : EuclideanSpace ℝ (Fin p)) :
    HasDerivAt (deriv (rankOneLaplaceExpectation q S T v))
      ((rankOneLaplaceRate S T v) ^ 2 * rankOneLaplaceExpectation q S T v θ) θ := by
  let a := rankOneLaplaceRate S T v
  have he : deriv (rankOneLaplaceExpectation q S T v) =ᶠ[𝓝 θ]
      fun t : ℝ => -a * rankOneLaplaceExpectation q S T v t := by
    filter_upwards [eventually_gt_nhds hθ] with t ht
    exact (rankOneLaplaceExpectation_hasDerivAt hq ht hS hT v).deriv
  have hd := (rankOneLaplaceExpectation_hasDerivAt hq hθ hS hT v).const_mul (-a)
  have hd' : HasDerivAt (fun t : ℝ => -a * rankOneLaplaceExpectation q S T v t)
      (a ^ 2 * rankOneLaplaceExpectation q S T v θ) θ := by
    convert hd using 1
    ring
  exact hd'.congr_of_eventuallyEq he

theorem rankOneLaplaceExpectation_differential_identity {p : ℕ} {q θ : ℝ}
    (hq : (p : ℝ) < q) (hθ : 0 < θ)
    {S T : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (hT : T.PosSemidef)
    (v : EuclideanSpace ℝ (Fin p)) :
    2 * θ * deriv (deriv (rankOneLaplaceExpectation q S T v)) θ +
      q * deriv (rankOneLaplaceExpectation q S T v) θ =
      (-q * rankOneLaplaceRate S T v + 2 * θ * (rankOneLaplaceRate S T v) ^ 2) *
        rankOneLaplaceExpectation q S T v θ := by
  rw [(rankOneLaplaceExpectation_hasDerivAt hq hθ hS hT v).deriv,
    (rankOneLaplaceExpectation_hasSecondDerivAt hq hθ hS hT v).deriv]
  ring

end ResearchMain.WishartBlocks
