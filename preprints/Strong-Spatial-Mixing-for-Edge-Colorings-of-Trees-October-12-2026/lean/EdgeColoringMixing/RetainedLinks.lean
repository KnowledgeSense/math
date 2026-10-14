import EdgeColoringMixing.InjectionLinks
import EdgeColoringMixing.RetainedCandidate

set_option autoImplicit false

namespace EdgeColoringMixing.WeightedInjection
open Finset Matrix

variable {d q : ℕ}

/-- Exact zero-extension of the retained negative column blocks from a deleted law. -/
theorem deleted_retainedNegative_transfer (W : Fin (d + 1) → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s)
    (x : ActiveCell (law W hW.nonneg (partition_pos W hW))) :
    let μ := law W hW.nonneg (partition_pos W hW)
    let ν := law (deleteRowColor W x.val.1 x.val.2)
      (hW.deleteRowColor W x.val.1 x.val.2).nonneg
      (partition_pos _ (hW.deleteRowColor W x.val.1 x.val.2))
    remainingEmbedding μ x.val.1 * retainedNegative ν * (remainingEmbedding μ x.val.1)ᵀ =
      (Matrix.of fun (y z : ActiveCell μ) => if y.val.1 ≠ z.val.1 ∧ y.val.2 = z.val.2 then
        -posteriorMean μ x.val y.val * posteriorMean μ x.val z.val else 0) := by
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  have hx := (marginal_pos_iff W hW _ _).mp ((mem_active _ _).mp x.property)
  apply remainingEmbedding_congruence_eq μ x.val.1
  · intro y z hy
    have hp := posteriorMean_same_row μ x.val y.val x.property hy.symm
    simp only [Matrix.of_apply]
    split_ifs
    · change -posteriorMean μ x.val y.val * posteriorMean μ x.val z.val = 0
      rw [hp]; ring
    · rfl
  · intro y z hz
    have hp := posteriorMean_same_row μ x.val z.val x.property hz.symm
    simp only [Matrix.of_apply]
    split_ifs
    · change -posteriorMean μ x.val y.val * posteriorMean μ x.val z.val = 0
      rw [hp]; ring
    · rfl
  · intro y z a b hy hz
    simp only [Matrix.of_apply, hy, hz, liftRemainingCell, retainedNegative]
    have hrow : (Equiv.swap (0 : Fin (d + 1)) x.val.1) a.1.succ ≠
        (Equiv.swap 0 x.val.1) b.1.succ ↔ a.1 ≠ b.1 := by simp
    simp only [hrow]
    split_ifs
    · rw [deleteRowColor_mean W hW _ _ hx, deleteRowColor_mean W hW _ _ hx]
      rfl
    · rfl

/-- The parent-coordinate candidate is exactly the lifted candidate for the actual smaller law. -/
theorem deleted_retainedCandidate_transfer (W : Fin (d + 1) → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s)
    (x : ActiveCell (law W hW.nonneg (partition_pos W hW))) (b : ℝ) :
    let μ := law W hW.nonneg (partition_pos W hW)
    let ν := law (deleteRowColor W x.val.1 x.val.2)
      (hW.deleteRowColor W x.val.1 x.val.2).nonneg
      (partition_pos _ (hW.deleteRowColor W x.val.1 x.val.2))
    remainingEmbedding μ x.val.1 * retainedCandidate ν b * (remainingEmbedding μ x.val.1)ᵀ =
      (1 / ((d : ℝ) * ((d : ℝ) - 1))) •
        ((Matrix.of fun (y z : ActiveCell μ) => if y.val.1 ≠ z.val.1 ∧ y.val.2 = z.val.2 then
          -posteriorMean μ x.val y.val * posteriorMean μ x.val z.val else 0) +
          b • diagonal (fun y : ActiveCell μ => posteriorMean μ x.val y.val)) := by
  dsimp only
  simp only [retainedCandidate, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]
  rw [deleted_retainedNegative_transfer W hW x]
  unfold marginalVector
  rw [deleted_diagonal_transfer W hW x]

/-- Null marginal columns have zero candidate entries. -/
theorem retainedCandidate_zero_of_inactive (μ : FiniteLaw (Injection d q)) (b : ℝ)
    (x y : Fin d × Fin q) (hy : y ∉ active μ) : retainedCandidate μ b x y = 0 := by
  have hp := mean_eq_zero_of_not_active μ hy
  simp only [retainedCandidate, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    retainedNegative_zero_of_mean_zero μ x y hp, zero_add, diagonal_apply, marginalVector]
  by_cases hxy : x = y
  · subst x
    simp [hp]
  · simp [hxy]

/-- Null marginal columns have zero centered-target entries. -/
theorem covarianceTarget_zero_of_inactive (μ : FiniteLaw (Injection d q))
    (x y : Fin d × Fin q) (hy : y ∉ active μ) : covarianceTarget μ x y = 0 := by
  have hp := mean_eq_zero_of_not_active μ hy
  simp only [covarianceTarget, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
    covariance_eq_zero_of_mean_zero μ x y hp, diagonal_apply, marginalVector]
  by_cases hxy : x = y
  · subst x
    simp [hp]
  · simp [hxy]

/-- The full-cell covariance target agrees with the actual active-cell local walk. -/
theorem covarianceTarget_active (μ : FiniteLaw (Injection d q)) (hd : 2 ≤ d) :
    (covarianceTarget μ).submatrix Subtype.val Subtype.val =
      localConductance μ - ((d : ℝ) / ((d : ℝ) - 1)) • vecMulVec (localPi μ) (localPi μ) := by
  have hid := covariance_localWalk_identity μ hd
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  ext x y
  have hentry := congrFun (congrFun hid x) y
  simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hentry
  change (1 / ((d : ℝ) * ((d : ℝ) - 1))) *
    (covariance μ x.val y.val - diagonal (marginalVector μ) x.val y.val) = _
  rw [hentry]
  have hdiag : diagonal (fun x : ActiveCell μ => mean μ x.val.1 x.val.2) x y =
      diagonal (marginalVector μ) x.val y.val := by
    simp only [diagonal_apply, marginalVector, Subtype.ext_iff]
  rw [hdiag]
  field_simp [show (d : ℝ) - 1 ≠ 0 by linarith]
  ring


/-- Zero marginal coordinates can be restored after proving a PSD bound on active cells. -/
theorem posSemidef_of_active_submatrix (μ : FiniteLaw (Injection d q))
    (A : Matrix (Fin d × Fin q) (Fin d × Fin q) ℝ) (hA : A.IsHermitian)
    (hzero : ∀ x y, y ∉ active μ → A x y = 0)
    (hactive : (A.submatrix Subtype.val Subtype.val :
      Matrix (ActiveCell μ) (ActiveCell μ) ℝ).PosSemidef) : A.PosSemidef := by
  let E : Matrix (Fin d × Fin q) (ActiveCell μ) ℝ := Matrix.of fun x y => if x = y.val then 1 else 0
  have heq : E * A.submatrix Subtype.val Subtype.val * Eᵀ = A := by
    ext x y
    by_cases hx : x ∈ active μ
    · by_cases hy : y ∈ active μ
      · let ax : ActiveCell μ := ⟨x,hx⟩
        let ay : ActiveCell μ := ⟨y,hy⟩
        have hxi (z : ActiveCell μ) : x = z.val ↔ ax = z := by
          simp only [Subtype.ext_iff, ax]
        have hyi (z : ActiveCell μ) : y = z.val ↔ ay = z := by
          simp only [Subtype.ext_iff, ay]
        simp [Matrix.mul_apply, Matrix.transpose_apply, E, Matrix.of_apply, hxi, hyi,
          Matrix.submatrix_apply, ax, ay]
      · have hne (z : ActiveCell μ) : y ≠ z.val := by
          intro h; exact hy (h ▸ z.property)
        simp [Matrix.mul_apply, Matrix.transpose_apply, E, Matrix.of_apply, hne, hzero x y hy]
    · have hne (z : ActiveCell μ) : x ≠ z.val := by
        intro h; exact hx (h ▸ z.property)
      have hxy : A x y = 0 := by
        have hs : A x y = A y x := by simpa using congrFun (congrFun hA.eq y) x
        rw [hs, hzero y x hx]
      simp [Matrix.mul_apply, E, Matrix.of_apply, hne, hxy]
  rw [← heq]
  simpa only [conjTranspose_eq_transpose_of_trivial] using hactive.mul_mul_conjTranspose_same E

/-- Restricting the candidate pseudoinverse square loses only identically zero summands. -/
theorem retainedCandidate_active_square (μ : FiniteLaw (Injection d q)) (b : ℝ) :
    (retainedCandidate μ b *
      diagonal (fun x : Fin d × Fin q => (d : ℝ) / mean μ x.1 x.2) * retainedCandidate μ b).submatrix
        Subtype.val Subtype.val =
      (retainedCandidate μ b).submatrix Subtype.val Subtype.val *
        diagonal (fun x : ActiveCell μ => (localPi μ x)⁻¹) *
          (retainedCandidate μ b).submatrix Subtype.val Subtype.val := by
  ext x y
  simp only [Matrix.submatrix_apply]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.submatrix_apply]
  have hsum : (∑ z : ActiveCell μ,
      retainedCandidate μ b x.val z.val * ((d : ℝ) / mean μ z.val.1 z.val.2) *
        retainedCandidate μ b z.val y.val) =
      ∑ z : Fin d × Fin q, retainedCandidate μ b x.val z * ((d : ℝ) / mean μ z.1 z.2) *
        retainedCandidate μ b z y.val := by
    calc
      _ = ∑ z ∈ active μ, retainedCandidate μ b x.val z * ((d : ℝ) / mean μ z.1 z.2) *
          retainedCandidate μ b z y.val :=
        (Finset.sum_subtype (active μ) (fun _ => Iff.rfl)
          (fun z => retainedCandidate μ b x.val z * ((d : ℝ) / mean μ z.1 z.2) *
            retainedCandidate μ b z y.val)).symm
      _ = _ := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro z _ hz
        rw [retainedCandidate_zero_of_inactive μ b x.val z hz, zero_mul, zero_mul]
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro z _
  simp only [localPi, inv_div]

end EdgeColoringMixing.WeightedInjection

