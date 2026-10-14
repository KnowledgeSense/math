import EdgeColoringMixing.RetainedLinks
import EdgeColoringMixing.CandidateRecursion

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EdgeColoringMixing.WeightedInjection
open Finset Matrix

variable {d q : ℕ}

private theorem deleted_candidate_eq_posterior (W : Fin (d + 1) → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s)
    (x : ActiveCell (law W hW.nonneg (partition_pos W hW))) (b : ℝ) :
    let μ := law W hW.nonneg (partition_pos W hW)
    let ν := law (deleteRowColor W x.val.1 x.val.2)
      (hW.deleteRowColor W x.val.1 x.val.2).nonneg
      (partition_pos _ (hW.deleteRowColor W x.val.1 x.val.2))
    remainingEmbedding μ x.val.1 * retainedCandidate ν b * (remainingEmbedding μ x.val.1)ᵀ =
      (posteriorCandidateOf μ (retainedPosterior μ) b x.val).submatrix Subtype.val Subtype.val := by
  dsimp only
  rw [deleted_retainedCandidate_transfer W hW x b]
  ext y z
  simp only [posteriorCandidateOf, retainedPosterior, Matrix.submatrix_apply,
    Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, Matrix.diagonal_apply,
    Subtype.ext_iff, Nat.cast_add, Nat.cast_one, add_sub_cancel_right, smul_eq_mul]
  congr 2; ring

private theorem deleted_rawPi_transfer (W : Fin (d + 1) → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s)
    (x : ActiveCell (law W hW.nonneg (partition_pos W hW))) :
    let μ := law W hW.nonneg (partition_pos W hW)
    let ν := law (deleteRowColor W x.val.1 x.val.2)
      (hW.deleteRowColor W x.val.1 x.val.2).nonneg
      (partition_pos _ (hW.deleteRowColor W x.val.1 x.val.2))
    remainingEmbedding μ x.val.1 * rawPi ν * (remainingEmbedding μ x.val.1)ᵀ =
      diagonal (linkPi μ x) := by
  dsimp only
  simp only [rawPi, Matrix.mul_smul, Matrix.smul_mul]
  unfold marginalVector
  rw [deleted_diagonal_transfer W hW x]
  ext y z
  simp only [Matrix.smul_apply, diagonal_apply, smul_eq_mul, linkPi_eq_posteriorMean,
    Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  split_ifs <;> ring

private theorem covarianceTarget_hermitian (μ : FiniteLaw (Injection d q)) :
    (covarianceTarget μ).IsHermitian := by
  unfold covarianceTarget
  exact ((covariance_posSemidef μ).isHermitian.sub
    (Matrix.isHermitian_diagonal _)).smul (by simp [IsSelfAdjoint])

/-- Matrix trickle-down on the actual injection hierarchy.  The base, cap and
recursive estimates are exposed separately so each can be instantiated with the
original release's proved harmonic candidate. -/
theorem retainedCandidate_induction {s : ℝ} (Δ : ℕ) (b : ℕ → ℝ)
    (hbase : 10 / (s + 1)^2 ≤ b 2)
    (hcap : ∀ k, 2 ≤ k → k ≤ Δ →
      (b k + 1 / (s + 1)) / ((k : ℝ) - 1) ≤ ((k : ℝ) - 1) / (3 * (k : ℝ) - 1))
    (hrecursive : ∀ k (W : Fin k → Fin q → ℝ) (hW : RowSurplus W s), 3 ≤ k → k ≤ Δ →
      let μ := law W hW.nonneg (partition_pos W hW)
      (retainedCandidate μ (b k) - (((k : ℝ) - 1) / ((k : ℝ) - 2)) •
        (retainedCandidate μ (b k) * ((k : ℝ) • marginalInverse μ) * retainedCandidate μ (b k)) -
        ∑ x ∈ active μ, (mean μ x.1 x.2 / k) •
          posteriorCandidateOf μ (retainedPosterior μ) (b (k - 1)) x).PosSemidef) :
    ∀ k, 2 ≤ k → k ≤ Δ → ∀ (W : Fin k → Fin q → ℝ) (hW : RowSurplus W s),
      let μ := law W hW.nonneg (partition_pos W hW)
      (retainedCandidate μ (b k) - covarianceTarget μ).PosSemidef := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk hkΔ W hW
    by_cases hk2 : k = 2
    · subst k
      exact retainedCandidate_base W hW hbase
    have hk3 : 3 ≤ k := by omega
    cases k with
    | zero => omega
    | succ d =>
      have hd : 2 ≤ d := by omega
      let μ := law W hW.nonneg (partition_pos W hW)
      let M : Matrix (ActiveCell μ) (ActiveCell μ) ℝ := (retainedCandidate μ (b (d + 1))).submatrix Subtype.val Subtype.val
      let N : ActiveCell μ → Matrix (ActiveCell μ) (ActiveCell μ) ℝ := fun x =>
        (posteriorCandidateOf μ (retainedPosterior μ) (b d) x.val).submatrix Subtype.val Subtype.val
      let α : ℝ := (d : ℝ) / ((d : ℝ) - 1)
      have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
      have hα : 1 ≤ α := by dsimp [α]; apply (le_div_iff₀ (by linarith)).mpr; linarith
      have hM : M.IsHermitian := (retainedCandidate_hermitian μ (b (d + 1))).submatrix _
      have hlower (x : ActiveCell μ) :
          (N x - (linkConductance μ x - α • vecMulVec (linkPi μ x) (linkPi μ x))).PosSemidef := by
        let W' := deleteRowColor W x.val.1 x.val.2
        have hW' := hW.deleteRowColor W x.val.1 x.val.2
        have hi := ih d (by omega) hd (by omega) W' hW'
        have h := hi.mul_mul_conjTranspose_same (remainingEmbedding μ x.val.1)
        simp only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul] at h
        rw [deleted_candidate_eq_posterior W hW x (b d)] at h
        change (N x - remainingEmbedding μ x.val.1 *
          ((1 / ((d : ℝ) * ((d : ℝ) - 1))) •
            (covariance (law W' hW'.nonneg (partition_pos W' hW')) -
              diagonal (fun a : Fin d × Fin q => mean (law W' hW'.nonneg (partition_pos W' hW')) a.1 a.2))) *
            (remainingEmbedding μ x.val.1)ᵀ).PosSemidef at h
        rw [deleted_covarianceTarget_transfer W hW hd x] at h
        exact h
      have hupper (x : ActiveCell μ) :
          ((1 / (2 * α + 1)) • diagonal (linkPi μ x) - N x).PosSemidef := by
        let W' := deleteRowColor W x.val.1 x.val.2
        have hW' := hW.deleteRowColor W x.val.1 x.val.2
        have hc := retainedCandidate_spectral_cap W' hW' hd (hcap d hd (by omega))
        have h := hc.mul_mul_conjTranspose_same (remainingEmbedding μ x.val.1)
        simp only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul,
          Matrix.mul_smul, Matrix.smul_mul] at h
        rw [deleted_candidate_eq_posterior W hW x (b d), deleted_rawPi_transfer W hW x] at h
        have hcoef : ((d : ℝ) - 1) / (3 * (d : ℝ) - 1) = 1 / (2 * α + 1) := by
          dsimp [α]
          field_simp [show (d : ℝ) - 1 ≠ 0 by linarith]
          ring
        simpa only [hcoef] using h
      have hrec := (hrecursive (d + 1) W hW hk3 hkΔ).submatrix
        (fun x : ActiveCell μ => x.val)
      have hsq : (retainedCandidate μ (b (d + 1)) *
          ((d + 1 : ℕ) : ℝ) • marginalInverse μ * retainedCandidate μ (b (d + 1))).submatrix
          Subtype.val Subtype.val = M * diagonal (fun x : ActiveCell μ => (localPi μ x)⁻¹) * M := by
        have hdiag : ((d + 1 : ℕ) : ℝ) • marginalInverse μ =
            diagonal (fun x : Fin (d + 1) × Fin q => ((d + 1 : ℕ) : ℝ) / mean μ x.1 x.2) := by
          ext y z
          simp only [marginalInverse, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
          split_ifs <;> simp [div_eq_mul_inv]
        rw [hdiag]
        exact retainedCandidate_active_square μ (b (d + 1))
      have havg : (∑ x ∈ active μ, (mean μ x.1 x.2 / (((d + 1 : ℕ) : ℝ))) •
          posteriorCandidateOf μ (retainedPosterior μ) (b d) x).submatrix Subtype.val Subtype.val =
          ∑ x : ActiveCell μ, localPi μ x • N x := by
        ext y z
        simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply,
          smul_eq_mul, localPi, N]
        simpa only [Nat.cast_add, Nat.cast_one] using
          (Finset.sum_subtype (active μ) (fun _ => Iff.rfl)
            (fun x => (mean μ x.1 x.2 / (((d + 1 : ℕ) : ℝ))) *
              posteriorCandidateOf μ (retainedPosterior μ) (b d) x y.val z.val))
      have hrec' : (M - α • (M * diagonal (fun x => (localPi μ x)⁻¹) * M) -
          ∑ x, localPi μ x • N x).PosSemidef := by
        have hcoefα : ((((d + 1 : ℕ) : ℝ) - 1) / (((d + 1 : ℕ) : ℝ) - 2)) = α := by
          dsimp [α]
          push_cast
          congr 1 <;> ring
        change (M - ((((d + 1 : ℕ) : ℝ) - 1) / (((d + 1 : ℕ) : ℝ) - 2)) •
          (retainedCandidate μ (b (d + 1)) *
            (((d + 1 : ℕ) : ℝ) • marginalInverse μ) * retainedCandidate μ (b (d + 1))).submatrix
            Subtype.val Subtype.val -
          (∑ x ∈ active μ, (mean μ x.1 x.2 / (((d + 1 : ℕ) : ℝ))) •
            posteriorCandidateOf μ (retainedPosterior μ) (b d) x).submatrix Subtype.val Subtype.val).PosSemidef at hrec
        rw [hcoefα, hsq, havg] at hrec
        exact hrec

      have hresult := injection_matrix_trickle_down_step W hW hk3 M N hM hα hlower hupper hrec'
      have hcoef : 2 - 1 / α = ((d + 1 : ℕ) : ℝ) / (((d + 1 : ℕ) : ℝ) - 1) := by
        dsimp [α]
        push_cast
        field_simp [show (d : ℝ) ≠ 0 by linarith]
        ring
      rw [hcoef, ← covarianceTarget_active μ hk] at hresult
      apply posSemidef_of_active_submatrix μ
        (retainedCandidate μ (b (d + 1)) - covarianceTarget μ)
        ((retainedCandidate_hermitian μ _).sub (covarianceTarget_hermitian μ))
      · intro x y hy
        simp only [Matrix.sub_apply, retainedCandidate_zero_of_inactive μ _ x y hy,
          covarianceTarget_zero_of_inactive μ x y hy, sub_self]
      · exact hresult


/-- The original release's harmonic candidate satisfies matrix trickle-down for
every weighted injection under the three explicit uniform numerical conditions.
There is no unproved matrix-recursion or covariance premise. -/
theorem retainedCandidate_column_bound (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (Δ : ℕ) (hd : 2 ≤ d) (hdΔ : d ≤ Δ)
    (hfirst : 8 * harmonicHeight Δ ≤ s + 1)
    (hsecond : 4 * (22 + 8 * ((q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2)) *
      (Δ : ℝ) * (harmonicHeight Δ)^2 ≤ (s + 1)^2)
    (hthird : columnError (22 + 8 * ((q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2))
      (s + 1) Δ + 1 / (s + 1) ≤ 1 / 5) :
    let μ := law W hW.nonneg (partition_pos W hW)
    let L := 22 + 8 * ((q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2)
    (retainedCandidate μ (columnError L (s + 1) d) - covarianceTarget μ).PosSemidef := by
  let V : ℝ := (q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2
  let L : ℝ := 22 + 8 * V
  have hV : 0 ≤ V := by dsimp [V]; have := hW.positive; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  apply retainedCandidate_induction Δ (columnError L (s + 1)) (columnError_two hV)
    (fun k hk hkΔ => columnError_spectral_cap hL hk hkΔ hthird) ?_ d hd hdΔ W hW
  intro k W' hW' hk hkΔ
  exact retainedCandidate_column_recursion W' hW' Δ hk hkΔ hfirst hsecond

/-- Theorem 4.1 of the fixed original source: the full retained-column covariance
bound, with the original harmonic error and all zero weights included. -/
theorem retained_column_covariance (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (Δ : ℕ) (hd : 2 ≤ d) (hdΔ : d ≤ Δ)
    (hfirst : 8 * harmonicHeight Δ ≤ s + 1)
    (hsecond : 4 * (22 + 8 * ((q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2)) *
      (Δ : ℝ) * (harmonicHeight Δ)^2 ≤ (s + 1)^2)
    (hthird : columnError (22 + 8 * ((q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2))
      (s + 1) Δ + 1 / (s + 1) ≤ 1 / 5) :
    let μ := law W hW.nonneg (partition_pos W hW)
    let L := 22 + 8 * ((q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2)
    (((1 + columnError L (s + 1) d) • Matrix.diagonal (marginalVector μ)) +
      retainedNegative μ - covariance μ).PosSemidef :=
  retained_covariance_of_candidate W hW hd
    (retainedCandidate_column_bound W hW Δ hd hdΔ hfirst hsecond hthird)

end EdgeColoringMixing.WeightedInjection

