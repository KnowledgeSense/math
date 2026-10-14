import HardCoreActivityThreshold.RootOdds
import Mathlib.Analysis.SpecificLimits.Basic

/-! Finite mixed-child trees used in the root-marginal approximation construction. -/
namespace HardCoreActivityThreshold
open Finset Polynomial Forest
attribute [local instance] Classical.propDecidable

@[simp] theorem forestTotal_union (A B : ForestExpr) (a : ℝ) :
    forestTotal (.union A B) a = forestTotal A a * forestTotal B a := by
  simp [forestTotal, ForestExpr.polynomials]

@[simp] theorem forestAvoid_union (A B : ForestExpr) (a : ℝ) :
    forestAvoid (.union A B) a = forestAvoid A a * forestAvoid B a := by
  simp [forestAvoid, ForestExpr.polynomials]

/-- A disjoint union of `n` copies of the tree with child forest `A`. -/
def rootCopies (A : ForestExpr) : ℕ → ForestExpr
  | 0 => .empty
  | n + 1 => .union (.root A) (rootCopies A n)

theorem forestRatio_root (A : ForestExpr) {a : ℝ} (ha : 0 < a) :
    forestAvoid (.root A) a / forestTotal (.root A) a = 1 / (1 + rootOdds A a) := by
  simp only [forestAvoid, forestTotal, ForestExpr.polynomials, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_X]
  change forestTotal A a / (forestTotal A a + a * forestAvoid A a) = _
  unfold rootOdds
  have hz := (forest_evaluations_pos A ha).1.ne'
  field_simp

theorem forestRatio_copies (A : ForestExpr) {a : ℝ} (ha : 0 < a) (n : ℕ) :
    forestAvoid (rootCopies A n) a / forestTotal (rootCopies A n) a =
      1 / (1 + rootOdds A a)^n := by
  induction n with
  | zero => norm_num [rootCopies, forestAvoid, forestTotal, ForestExpr.polynomials]
  | succ n ih =>
    simp only [rootCopies, forestAvoid_union, forestTotal_union]
    rw [mul_div_mul_comm, forestRatio_root A ha, ih, pow_succ]
    have hd : 1 + rootOdds A a ≠ 0 := by have := rootOdds_pos A ha; positivity
    field_simp

def mixedChildren (lower upper : ForestExpr) (b k : ℕ) : ForestExpr :=
  .union (rootCopies upper k) (rootCopies lower (b - k))

noncomputable def mixedOdds (a lower upper : ℝ) (b k : ℕ) : ℝ :=
  a / (1 + upper)^k / (1 + lower)^(b - k)

theorem rootOdds_mixedChildren (lower upper : ForestExpr) {a : ℝ} (ha : 0 < a)
    (b k : ℕ) :
    rootOdds (mixedChildren lower upper b k) a =
      mixedOdds a (rootOdds lower a) (rootOdds upper a) b k := by
  unfold rootOdds mixedChildren
  rw [forestAvoid_union, forestTotal_union]
  rw [mul_div_assoc, mul_div_mul_comm, forestRatio_copies upper ha, forestRatio_copies lower ha]
  unfold mixedOdds rootOdds
  ring

theorem mixedOdds_pos {a lower upper : ℝ} (ha : 0 < a) (hl : 0 ≤ lower)
    (hu : 0 ≤ upper) (b k : ℕ) : 0 < mixedOdds a lower upper b k := by
  unfold mixedOdds
  positivity

theorem mixedOdds_first {a lower upper omega : ℝ} (_ha : 0 < a) (hl : 0 ≤ lower)
    (hw : 0 < omega) (hlw : lower ≤ omega) (b : ℕ)
    (hfix : a = omega * (1 + omega)^b) : omega ≤ mixedOdds a lower upper b 0 := by
  simp only [mixedOdds, pow_zero, div_one, Nat.sub_zero]
  apply (le_div_iff₀ (by positivity : 0 < (1 + lower)^b)).mpr
  rw [hfix]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) b) hw.le

theorem mixedOdds_last {a lower upper omega : ℝ} (_ha : 0 < a) (hu : 0 ≤ upper)
    (hw : 0 < omega) (hwu : omega ≤ upper) (b : ℕ)
    (hfix : a = omega * (1 + omega)^b) : mixedOdds a lower upper b b ≤ omega := by
  simp only [mixedOdds, Nat.sub_self, pow_zero, div_one]
  apply (div_le_iff₀ (by positivity : 0 < (1 + upper)^b)).mpr
  rw [hfix]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) b) hw.le

theorem mixedOdds_adjacent_ratio {a lower upper : ℝ} (ha : 0 < a) (hl : 0 < lower)
    (hu : 0 < upper) {b k : ℕ} (hk : k < b) :
    mixedOdds a lower upper b k / mixedOdds a lower upper b (k+1) =
      (1 + upper) / (1 + lower) := by
  have he : b-k = (b-(k+1))+1 := by omega
  unfold mixedOdds
  rw [he, pow_succ, pow_succ]
  have hln : 1+lower ≠ 0 := by positivity
  have hun : 1+upper ≠ 0 := by positivity
  field_simp

theorem odds_ratio_contraction {a lower upper : ℝ} (ha : 0 < a) (hl : 0 < lower)
    (hlu : lower ≤ upper) (hla : lower ≤ a) :
    (1+upper)/(1+lower) - 1 ≤ (a/(1+a)) * (upper/lower - 1) := by
  have hl1 : 0 < 1 + lower := by positivity
  have ha1 : 0 < 1 + a := by positivity
  have hbase : lower/(1+lower) ≤ a/(1+a) := by
    apply (div_le_div_iff₀ hl1 ha1).mpr
    nlinarith
  have herr : 0 ≤ upper/lower - 1 := sub_nonneg.mpr ((one_le_div hl).mpr hlu)
  have hmul := mul_le_mul_of_nonneg_right hbase herr
  convert hmul using 1; field_simp; ring


end HardCoreActivityThreshold
