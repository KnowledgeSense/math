import TerminalLogConcavity.ChainLower
import TerminalLogConcavity.GaussianModel

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial BigOperators

theorem prod_map_range_poly (f : ℕ → ℕ[X]) (n : ℕ) :
    ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.prod_range_succ, ih]

theorem release_phase_lower {q : ℕ} (hq : 2 ≤ q) (t : ℕ) :
    CoeffLE (∏ i ∈ Finset.range q, chainPhasePolynomial q t (i + 1))
      (pathStateSum (releaseDecorations q t)).1 := by
  have h := (pathStateSum_bridge_product_bounds
    ((List.range q).map (fun i => chainDecorations q t (i + 1))) Block.leaf.decoration
    (by simp only [Block.decoration_A, Block.A_leaf]; exact CoeffLE.le_add_right _ _)).1
  simp only [List.map_map, Function.comp_def, prod_map_range_poly] at h
  apply CoeffLE.trans _ h
  apply CoeffLE.prod
  intro i _
  exact (chainPhase_le_lowerChain hq t (i + 1)).trans
    (lowerChain_le_exact (by omega) t (i + 1))

noncomputable def scaledGaussianPolynomial (q a : ℕ) : ℕ[X] :=
  C (a ^ (2 * baseCoupling q * q * (q - 1))) *
    gaussianPolynomial q a (a ^ (2 * massParameter q))

theorem phase_product_eq_scaledGaussian (q t : ℕ) :
    (∏ i ∈ Finset.range q, chainPhasePolynomial q t (i + 1)) =
      scaledGaussianPolynomial q (amplifier t) := by
  have hf (i : ℕ) : chainPhasePolynomial q t (i + 1) =
      C (amplifier t ^ (2 * baseCoupling q * (q - 1))) *
        gaussianFactor q (amplifier t) (amplifier t ^ (2 * massParameter q)) i := by
    unfold chainPhasePolynomial lowerSiteP gaussianFactor interfaceParameter
    rw [Nat.mul_add, pow_add]
  simp_rw [hf]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_range, ← C_pow, ← pow_mul]
  unfold scaledGaussianPolynomial gaussianPolynomial
  congr 3
  ring

theorem scaledGaussian_le_graph {q : ℕ} (hq : 2 ≤ q) (t : ℕ) :
    CoeffLE (scaledGaussianPolynomial q (amplifier t))
      (Polynomial.reflect (releaseForest q t).graph.indepNum
        (independencePolynomial (releaseForest q t).graph Finset.univ)) := by
  rw [← phase_product_eq_scaledGaussian, releaseForest, ← pathStateSum_graph]
  exact release_phase_lower hq t

end TerminalLogConcavity
