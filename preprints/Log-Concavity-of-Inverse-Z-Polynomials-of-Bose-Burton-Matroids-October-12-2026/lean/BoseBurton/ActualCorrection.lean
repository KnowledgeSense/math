import BoseBurton.ActualRankSum

noncomputable section
namespace BoseBurton
open Finset Submodule Module Polynomial MatroidInverseZ
open scoped Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Module.Finite K V] [Finite V]

omit [Fintype K] in
theorem spanY_unpunctured (hbot : (⊥ : Submodule K V) ≠ ⊤) :
    spanY (⊥ : Submodule K V) hbot = projectiveY K V := by
  let e := unpuncturedSpanOrderIso (K := K) (V := V)
  have h := inverseZ_interval_transport e.toOrderEmbedding
    (fun _ _ y _ _ => ⟨e.symm y, e.apply_symm_apply y⟩)
    (spanRank (⊥ : Submodule K V)) (fun U : Submodule K V => finrank K U)
    (fun _ _ => rfl) ⊥ (spanTop (⊥ : Submodule K V) hbot)
  change projectiveY K V = spanY (⊥ : Submodule K V) hbot at h
  exact h.symm

theorem correctionRow_zero_deleted (q : ℝ) (r d : ℕ) (hd : 1 ≤ d) :
    correctionRow q r 0 d = 0 := by
  unfold correctionRow
  apply sum_eq_zero
  intro i hi
  have hp : 0 < max i (d-i) := by have := mem_range.mp hi; omega
  rw [gaussian_outside q 0 (max i (d-i)) hp, zero_mul]
  simp

theorem restrictedRankRow_zero_deleted (q : ℝ) (r d : ℕ) (hd : 1 ≤ d) :
    restrictedRankRow q r 0 d = C (gaussian q r d) * gaussianRow q d := by
  rw [restrictedRankRow_decomposition, correctionRow_zero_deleted q r d hd, sub_zero]

/-- The complete projective incidence convolution, proved from its actual flat lattice. -/
theorem projectiveRow_actual_convolution (hbot : (⊥ : Submodule K V) ≠ ⊤) :
    projectiveRow (Fintype.card K : ℝ) (finrank K V) =
      -(∑ d ∈ Icc 1 (finrank K V), C ((-1 : ℝ)^d) *
        (C (gaussian (Fintype.card K : ℝ) (finrank K V) d) * gaussianRow (Fintype.card K : ℝ) d) *
          projectiveRow (Fintype.card K : ℝ) (finrank K V-d)) := by
  have h := spanY_rank_sum (⊥ : Submodule K V) hbot
  rw [spanY_unpunctured, projectiveY_eq_projectiveRow, finrank_bot] at h
  rw [h]
  congr 1
  apply sum_congr rfl
  intro d hd
  rw [restrictedRankRow_zero_deleted _ _ _ (mem_Icc.mp hd).1]

/-- Subtracting the full projective convolution leaves exactly the finite correction. -/
theorem actual_inverseZ_correction (W : Submodule K V) (hW : W ≠ ⊤) :
    (matroidInverseZ (matroid W)).map (Int.castRingHom ℝ) =
      projectiveRow (Fintype.card K : ℝ) (finrank K V) +
        ∑ d ∈ Icc 1 (finrank K V), C ((-1 : ℝ)^d) *
          correctionRow (Fintype.card K : ℝ) (finrank K V) (finrank K W) d *
            projectiveRow (Fintype.card K : ℝ) (finrank K V-d) := by
  have hbot : (⊥ : Submodule K V) ≠ ⊤ := by
    intro h
    apply hW
    apply top_le_iff.mp
    rw [← h]
    exact bot_le
  rw [actual_inverseZ_eq_spanY W hW, spanY_rank_sum,
    projectiveRow_actual_convolution hbot]
  simp_rw [restrictedRankRow_decomposition, mul_sub, sub_mul]
  rw [sum_sub_distrib]
  ring

end BoseBurton
