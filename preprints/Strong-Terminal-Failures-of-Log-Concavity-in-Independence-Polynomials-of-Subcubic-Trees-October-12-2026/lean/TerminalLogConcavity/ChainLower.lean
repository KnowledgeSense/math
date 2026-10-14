import TerminalLogConcavity.ChainModel
import TerminalLogConcavity.LowerWeights
import TerminalLogConcavity.ReleaseCounts

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial

noncomputable def lowerChain (q t i : ℕ) : ℕ[X] :=
  (weightedPath (((List.range q).map (fun k => lowerSiteWeight q t i (k + 1))).intersperse
    (lowerCouplerWeight q t))).1

theorem lowerChain_le_exact {q : ℕ} (hq : 1 ≤ q) (t i : ℕ) :
    CoeffLE (lowerChain q t i) (pathStateSum (chainDecorations q t i)).1 := by
  rw [pathStateSum_eq_weightedPath]
  unfold lowerChain chainDecorations
  rw [map_intersperse]
  simp only [List.map_map, Function.comp_def]
  apply (weightedPath_mono _).1
  apply forall₂_map_intersperse
  · exact coupler_lower_weights hq t
  · intro k _
    exact site_lower_weights hq t i (k + 1)

private theorem prod_constant_powers (a : ℕ) (f : ℕ → ℕ) (l : List ℕ) :
    (l.map (fun k => (C (a ^ f k) : ℕ[X]))).prod = C (a ^ (l.map f).sum) := by
  induction l with
  | nil => simp
  | cons k l ih => simp only [List.map_cons, List.prod_cons, List.sum_cons, ih, pow_add, C_mul]

theorem site_parameter_sum_nat {q : ℕ} (hq : 2 ≤ q) (i : ℕ) :
    ((List.range q).map (fun k => siteParameter q i (k + 1))).sum =
      2 * baseCoupling q * (q - 1) + i ^ 2 := by
  have h := site_parameter_sum hq i
  have he : (baseCoupling q : ℤ) * (2 * q - 2) + (i : ℤ)^2 =
      (2 * baseCoupling q * (q - 1) + i ^ 2 : ℕ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [he] at h
  have hl : (((List.range q).map (fun k => siteParameter q i (k + 1))).sum : ℤ) =
      ∑ k ∈ Finset.range q, (siteParameter q i (k + 1) : ℤ) := by
    rw [Nat.cast_list_sum, List.map_map]
    exact sum_map_range_int _ _
  rw [← hl] at h
  exact_mod_cast h

noncomputable def chainPhasePolynomial (q t i : ℕ) : ℕ[X] :=
  C (amplifier t ^ (2 * baseCoupling q * (q - 1))) *
    (C (amplifier t ^ (i ^ 2)) + lowerSiteP q t i ^ q)

theorem chainPhase_le_lowerChain {q : ℕ} (hq : 2 ≤ q) (t i : ℕ) :
    CoeffLE (chainPhasePolynomial q t i) (lowerChain q t i) := by
  let cs := (List.range q).map (fun k => (C (amplifier t ^ siteParameter q i (k + 1)) : ℕ[X]))
  have hn : cs ≠ [] := by
    intro h; have := congrArg List.length h; simp [cs] at this; omega
  have h := (chainModel_two_phases (lowerSiteP q t i)
    (C (amplifier t ^ (2 * baseCoupling q))) cs hn).1
  have hr : (chainModel (lowerSiteP q t i) (C (amplifier t ^ (2 * baseCoupling q))) cs).1 =
      lowerChain q t i := by
    simp only [chainModel, chainWeights, cs, List.map_map, Function.comp_def,
      lowerChain, lowerSiteWeight, lowerCouplerWeight]
  rw [hr] at h
  have hl : cs.length = q := by simp [cs]
  have hp : cs.prod = C (amplifier t ^ (2 * baseCoupling q * (q - 1) + i ^ 2)) := by
    rw [prod_constant_powers, site_parameter_sum_nat hq]
  rw [hl, hp] at h
  convert h using 1
  simp only [chainPhasePolynomial, mul_add, ← C_pow, ← C_mul, ← pow_mul, pow_add]

end TerminalLogConcavity
