import MainTheorems.WishartBlocks.BlockSeparation

namespace ResearchMain.WishartBlocks

open Matrix MeasureTheory
open scoped BigOperators MatrixOrder

namespace BlockPartition

theorem determinantPower_integral_nonneg {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (j : Fin d) (α : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    0 ≤ ∫ W, P.determinantPower ν W j ∂(bartlettLaw α S) :=
  integral_nonneg_of_ae ((bartlettLaw_positiveSemidefinite α S).mono
    fun _W hW => P.determinantPower_nonneg ν hW j)

theorem product_inequality {p d : ℕ} (P : BlockPartition p d) (ν : Fin d → ℝ)
    (hν : ∀ j, 0 ≤ ν j) {α : ℝ} (hα : (p : ℝ) - 1 < α)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) : P.ProductInequality α S ν := by
  induction d generalizing p with
  | zero => exact P.zero_block hα S ν
  | succ d ih =>
    cases d with
    | zero => exact P.one_block α S ν
    | succ e =>
      let m := ∑ j : Fin (e + 1), P.size j.succ
      let Γ := S.submatrix P.headReindex.symm P.headReindex.symm
      have hΓ : Γ.PosDef := P.headReindex_covariance_positive hS
      have hB : (principalPair (k := P.size 0) (m := m) Γ).2.PosDef :=
        hΓ.submatrix (finSumFinEquiv.injective.comp Sum.inr_injective)
      have hm : m ≤ p := by
        have hd := P.head_tail_dimension
        dsimp [m]
        omega
      have hmR : (m : ℝ) ≤ p := by exact_mod_cast hm
      have hαB : (m : ℝ) - 1 < α := by linarith
      have ht : P.tail.ProductInequality α (principalPair (k := P.size 0) (m := m) Γ).2
          (fun j => ν j.succ) :=
        ih P.tail (fun j => ν j.succ) (fun j => hν j.succ) hαB hB
      have hs := P.tail.head_tail_separation (fun j => ν j.succ) (fun j => hν j.succ)
        (P.size_pos 0) (P.headReindex_shape hα) (hν 0) hΓ
      have hh : (∫ W, P.determinantPower ν W 0 ∂(bartlettLaw α S)) =
          ∫ A, A.det ^ ν 0 ∂(bartlettLaw α (principalPair (k := P.size 0) (m := m) Γ).1) := by
        rw [P.determinantPower_marginal_integral ν 0 hα hS.posSemidef]
        dsimp [Γ]
        rw [P.reindex_head_block]
      have hf : (∏ j : Fin (e + 1),
          ∫ W, P.determinantPower ν W j.succ ∂(bartlettLaw α S)) =
          ∏ j : Fin (e + 1), ∫ B, P.tail.determinantPower (fun i => ν i.succ) B j
            ∂(bartlettLaw α (principalPair (k := P.size 0) (m := m) Γ).2) := by
        apply Finset.prod_congr rfl
        intro j _
        exact P.tail_determinantPower_integral ν j hα hS.posSemidef
      have hw := P.determinantProduct_headReindex_integral ν hα hS.posSemidef
      change (∏ j, ∫ W, P.determinantPower ν W j ∂(bartlettLaw α S)) ≤
        ∫ W, P.determinantProduct ν W ∂(bartlettLaw α S)
      rw [Fin.prod_univ_succ, hf]
      calc
        (∫ W, P.determinantPower ν W 0 ∂(bartlettLaw α S)) *
            (∏ j, ∫ B, P.tail.determinantPower (fun i => ν i.succ) B j
              ∂(bartlettLaw α (principalPair (k := P.size 0) (m := m) Γ).2)) ≤
            (∫ W, P.determinantPower ν W 0 ∂(bartlettLaw α S)) *
              (∫ B, P.tail.determinantProduct (fun i => ν i.succ) B
                ∂(bartlettLaw α (principalPair (k := P.size 0) (m := m) Γ).2)) :=
          mul_le_mul_of_nonneg_left ht (P.determinantPower_integral_nonneg ν 0 α S)
        _ ≤ ∫ W, (principalPair (k := P.size 0) (m := m) W).1.det ^ ν 0 *
            P.tail.determinantProduct (fun j => ν j.succ) (principalPair W).2
              ∂(bartlettLaw α Γ) := by rw [hh]; exact hs
        _ = ∫ W, P.determinantProduct ν W ∂(bartlettLaw α S) := hw.symm

end BlockPartition

theorem wishart_block_determinant_product_inequality {p d : ℕ}
    (P : BlockPartition p d) (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j)
    {α : ℝ} (hα : (p : ℝ) - 1 < α)
    {S₀ : Matrix (Fin p) (Fin p) ℝ} (hS₀ : S₀.PosDef) :
    (∏ j, ∫ W, (P.block W j).det ^ ν j ∂(bartlettLaw α S₀)) ≤
      ∫ W, (∏ j, (P.block W j).det ^ ν j) ∂(bartlettLaw α S₀) :=
  P.product_inequality ν hν hα hS₀

end ResearchMain.WishartBlocks

