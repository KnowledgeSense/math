import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.Tactic

namespace ResearchMain.WishartBlocks

open scoped BigOperators

def OrderedPositive {n : ℕ} (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 < x i) ∧ StrictMono x

theorem orderedPositive_inf {n : ℕ} {x y : Fin n → ℝ}
    (hx : OrderedPositive x) (hy : OrderedPositive y) : OrderedPositive (x ⊓ y) := by
  constructor
  · intro i
    exact lt_min (hx.1 i) (hy.1 i)
  · intro i j hij
    change min (x i) (y i) < min (x j) (y j)
    exact lt_min ((min_le_left _ _).trans_lt (hx.2 hij))
      ((min_le_right _ _).trans_lt (hy.2 hij))

theorem orderedPositive_sup {n : ℕ} {x y : Fin n → ℝ}
    (hx : OrderedPositive x) (hy : OrderedPositive y) : OrderedPositive (x ⊔ y) := by
  constructor
  · intro i
    exact (hx.1 i).trans_le (le_max_left _ _)
  · intro i j hij
    change max (x i) (y i) < max (x j) (y j)
    exact max_lt ((hx.2 hij).trans_le (le_max_left _ _))
      ((hy.2 hij).trans_le (le_max_right _ _))

theorem gap_lattice {a b c d : ℝ} :
    (b - a) * (d - c) ≤
      (min b d - min a c) * (max b d - max a c) := by
  rcases le_total a c with hac | hca <;> rcases le_total b d with hbd | hdb
  · simp only [min_eq_left hac, max_eq_right hac, min_eq_left hbd, max_eq_right hbd]
    exact le_rfl
  · simp only [min_eq_left hac, max_eq_right hac, min_eq_right hdb, max_eq_left hdb]
    have hn := mul_nonneg (sub_nonneg.mpr hac) (sub_nonneg.mpr hdb)
    nlinarith
  · simp only [min_eq_right hca, max_eq_left hca, min_eq_left hbd, max_eq_right hbd]
    have hn := mul_nonneg (sub_nonneg.mpr hca) (sub_nonneg.mpr hbd)
    nlinarith
  · simp only [min_eq_right hca, max_eq_left hca, min_eq_right hdb, max_eq_left hdb]
    ring_nf
    exact le_rfl

noncomputable def gapProduct {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∏ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 < ij.2),
    (x ij.2 - x ij.1)

theorem gapProduct_nonneg {n : ℕ} {x : Fin n → ℝ} (hx : OrderedPositive x) :
    0 ≤ gapProduct x := by
  apply Finset.prod_nonneg
  intro ij hij
  exact (sub_pos.mpr (hx.2 (Finset.mem_filter.mp hij).2)).le

theorem gapProduct_lattice {n : ℕ} {x y : Fin n → ℝ}
    (hx : OrderedPositive x) (hy : OrderedPositive y) :
    gapProduct x * gapProduct y ≤ gapProduct (x ⊓ y) * gapProduct (x ⊔ y) := by
  unfold gapProduct
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro ij hij
    have hi := (Finset.mem_filter.mp hij).2
    exact mul_nonneg (sub_pos.mpr (hx.2 hi)).le (sub_pos.mpr (hy.2 hi)).le
  · intro ij hij
    exact gap_lattice

theorem single_factor_lattice {n : ℕ} (f : ℝ → ℝ) (x y : Fin n → ℝ) :
    (∏ i, f (x i)) * (∏ i, f (y i)) =
      (∏ i, f ((x ⊓ y) i)) * (∏ i, f ((x ⊔ y) i)) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rcases le_total (x i) (y i) with h | h
  · simp [Pi.inf_apply, Pi.sup_apply, min_eq_left h, max_eq_right h]
  · simp [Pi.inf_apply, Pi.sup_apply, min_eq_right h, max_eq_left h, mul_comm]

noncomputable def chamberWeight {n : ℕ} (f : ℝ → ℝ) (x : Fin n → ℝ) : ℝ := by
  classical
  exact if OrderedPositive x then (∏ i, f (x i)) * gapProduct x else 0

theorem chamberWeight_nonneg {n : ℕ} {f : ℝ → ℝ}
    (hf : ∀ t > 0, 0 ≤ f t) (x : Fin n → ℝ) : 0 ≤ chamberWeight f x := by
  classical
  unfold chamberWeight
  split_ifs with hx
  · exact mul_nonneg (Finset.prod_nonneg fun i _ => hf (x i) (hx.1 i))
      (gapProduct_nonneg hx)
  · exact le_rfl

theorem chamberWeight_lattice {n : ℕ} {f : ℝ → ℝ}
    (hf : ∀ t > 0, 0 ≤ f t) (x y : Fin n → ℝ) :
    chamberWeight f x * chamberWeight f y ≤
      chamberWeight f (x ⊓ y) * chamberWeight f (x ⊔ y) := by
  classical
  by_cases hx : OrderedPositive x
  · by_cases hy : OrderedPositive y
    · have hi := orderedPositive_inf hx hy
      have hs := orderedPositive_sup hx hy
      simp only [chamberWeight, hx, hy, hi, hs, ite_true]
      calc
        ((∏ i, f (x i)) * gapProduct x) * ((∏ i, f (y i)) * gapProduct y)
            = ((∏ i, f (x i)) * (∏ i, f (y i))) *
              (gapProduct x * gapProduct y) := by ring
        _ ≤ ((∏ i, f (x i)) * (∏ i, f (y i))) *
              (gapProduct (x ⊓ y) * gapProduct (x ⊔ y)) :=
          mul_le_mul_of_nonneg_left (gapProduct_lattice hx hy)
            (mul_nonneg (Finset.prod_nonneg fun i _ => hf (x i) (hx.1 i))
              (Finset.prod_nonneg fun i _ => hf (y i) (hy.1 i)))
        _ = ((∏ i, f ((x ⊓ y) i)) * gapProduct (x ⊓ y)) *
              ((∏ i, f ((x ⊔ y) i)) * gapProduct (x ⊔ y)) := by
          rw [single_factor_lattice f x y]
          ring
    · simp only [chamberWeight, hy, ite_false, mul_zero]
      exact mul_nonneg (chamberWeight_nonneg hf _) (chamberWeight_nonneg hf _)
  · simp only [chamberWeight, hx, ite_false, zero_mul]
    exact mul_nonneg (chamberWeight_nonneg hf _) (chamberWeight_nonneg hf _)

noncomputable def eigenvalueWeight (α : ℝ) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  chamberWeight (fun t => t ^ ((α - n - 1) / 2) * Real.exp (-t / 2)) x

theorem eigenvalueWeight_lattice (α : ℝ) {n : ℕ} (x y : Fin n → ℝ) :
    eigenvalueWeight α x * eigenvalueWeight α y ≤
      eigenvalueWeight α (x ⊓ y) * eigenvalueWeight α (x ⊔ y) := by
  apply chamberWeight_lattice
  intro t ht
  exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le

end ResearchMain.WishartBlocks
