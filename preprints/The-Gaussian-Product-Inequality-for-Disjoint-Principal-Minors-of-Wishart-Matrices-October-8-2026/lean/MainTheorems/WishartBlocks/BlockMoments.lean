import MainTheorems.WishartBlocks.BartlettSupport
import Mathlib.Algebra.BigOperators.Fin

namespace ResearchMain.WishartBlocks

open MeasureTheory
open scoped BigOperators

structure BlockPartition (p d : ℕ) where
  size : Fin d → ℕ
  size_pos : ∀ j, 0 < size j
  index : (Σ j : Fin d, Fin (size j)) ≃ Fin p

namespace BlockPartition

def standard {d : ℕ} (size : Fin d → ℕ) (hsize : ∀ j, 0 < size j) :
    BlockPartition (∑ j, size j) d where
  size := size
  size_pos := hsize
  index := finSigmaFinEquiv

def inclusion {p d : ℕ} (P : BlockPartition p d) (j : Fin d) : Fin (P.size j) → Fin p :=
  fun i => P.index ⟨j, i⟩

theorem inclusion_injective {p d : ℕ} (P : BlockPartition p d) (j : Fin d) :
    Function.Injective (P.inclusion j) := by
  intro i k h
  have he := P.index.injective h
  cases he
  rfl

def block {p d : ℕ} (P : BlockPartition p d) (W : Matrix (Fin p) (Fin p) ℝ) (j : Fin d) :
    Matrix (Fin (P.size j)) (Fin (P.size j)) ℝ :=
  W.submatrix (P.inclusion j) (P.inclusion j)

theorem block_positiveDefinite {p d : ℕ} (P : BlockPartition p d)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosDef) (j : Fin d) :
    (P.block W j).PosDef :=
  hW.submatrix (P.inclusion_injective j)

noncomputable def determinantPower {p d : ℕ} (P : BlockPartition p d) (ν : Fin d → ℝ)
    (W : Matrix (Fin p) (Fin p) ℝ) (j : Fin d) : ℝ :=
  (P.block W j).det ^ ν j

noncomputable def determinantProduct {p d : ℕ} (P : BlockPartition p d) (ν : Fin d → ℝ)
    (W : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  ∏ j, P.determinantPower ν W j

theorem determinantPower_nonneg {p d : ℕ} (P : BlockPartition p d) (ν : Fin d → ℝ)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) (j : Fin d) :
    0 ≤ P.determinantPower ν W j :=
  Real.rpow_nonneg (hW.submatrix (P.inclusion j)).det_nonneg _

theorem determinantProduct_nonneg {p d : ℕ} (P : BlockPartition p d) (ν : Fin d → ℝ)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) :
    0 ≤ P.determinantProduct ν W :=
  Finset.prod_nonneg fun j _ => P.determinantPower_nonneg ν hW j

theorem measurable_determinantPower {p d : ℕ} (P : BlockPartition p d) (ν : Fin d → ℝ)
    (j : Fin d) : Measurable (fun W => P.determinantPower ν W j) := by
  unfold determinantPower block
  fun_prop

theorem measurable_determinantProduct {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) : Measurable (P.determinantProduct ν) := by
  unfold determinantProduct
  exact Finset.measurable_prod _ fun j _ => P.measurable_determinantPower ν j

def ProductInequality {p d : ℕ} (P : BlockPartition p d) (α : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (ν : Fin d → ℝ) : Prop :=
  (∏ j, ∫ W, P.determinantPower ν W j ∂(bartlettLaw α S)) ≤
    ∫ W, P.determinantProduct ν W ∂(bartlettLaw α S)

theorem one_block {p : ℕ} (P : BlockPartition p 1) (α : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (ν : Fin 1 → ℝ) : P.ProductInequality α S ν := by
  simp [ProductInequality, determinantProduct]

end BlockPartition

end ResearchMain.WishartBlocks
