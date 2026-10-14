import Paving.TruncatedUpperIntervals
import Paving.InverseZSymmetry

namespace Paving
attribute [local instance] Classical.propDecidable
open Finset MatroidInverseZ Polynomial
variable {α : Type*} [Fintype α]

noncomputable def uniformQ (r : ℕ) : Polynomial ℤ := inverseKL (truncatedRank α r) ⊥ ⊤
noncomputable def uniformY (r : ℕ) : Polynomial ℤ := inverseZ (truncatedRank α r) ⊥ ⊤

noncomputable def uniformSummand (r : ℕ) (F : TruncatedFlat α r) : Polynomial ℤ :=
  C (((-1 : ℤ)^(r+1-truncatedRank α r F))*IncidenceAlgebra.mu ℤ F ⊤)*
    X^(r+1-truncatedRank α r F)*inverseKL (truncatedRank α r) ⊥ F

theorem uniformSummand_proper (r : ℕ) (hr : r+1 ≤ Fintype.card α)
    (F : TruncatedFlat α r) (hF : F ≠ ⊤) :
    uniformSummand r F = C (((Fintype.card α-F.1.card-1).choose (r-F.1.card):ℕ):ℤ)*
      X^(r+1-F.1.card) := by
  have hc := truncated_proper_card α r F hF
  rw [uniformSummand, truncatedRank_proper α r F hF, truncated_inverseKL_proper r F hF, mul_one]
  have hm := truncated_upper_mu r hr F.1 hc
  change IncidenceAlgebra.mu ℤ F ⊤ = _ at hm
  rw [hm, show r-F.1.card+1=r+1-F.1.card by omega]
  have hs : (-1 : ℤ)^(r+1-F.1.card)*((-1 : ℤ)^(r+1-F.1.card)*
      ((Fintype.card α-F.1.card-1).choose (r-F.1.card):ℤ)) =
      ((Fintype.card α-F.1.card-1).choose (r-F.1.card):ℤ) := by
    rw [← mul_assoc, ← mul_pow]
    simp
  rw [hs]

theorem uniformY_split (r : ℕ) (hr : r+1 ≤ Fintype.card α) :
    uniformY (α:=α) r = uniformQ (α:=α) r +
      ∑ F ∈ Ico (⊥ : TruncatedFlat α r) ⊤, uniformSummand r F := by
  rw [uniformY, inverseZ, Icc_eq_cons_Ico bot_le, sum_cons]
  rw [truncatedRank_top α r hr]
  simp only [Nat.sub_self, pow_zero, IncidenceAlgebra.mu_self, mul_one, map_one, one_mul]
  rfl

/-- A finite coefficient identity from the true uniform flat sum. -/
theorem uniformY_coeff_split (r j : ℕ) (hr : r+1 ≤ Fintype.card α)
    (hj : 1≤j) (hjr : j≤r+1) :
    (uniformY (α:=α) r).coeff j = (uniformQ (α:=α) r).coeff j +
      (Fintype.card α).choose (r+1-j) *
        ((Fintype.card α-(r+1-j)-1).choose (j-1):ℤ) := by
  rw [uniformY_split r hr, coeff_add, finsetSum_coeff]
  congr 1
  have hs : (∑ F ∈ Ico (⊥ : TruncatedFlat α r) ⊤, (uniformSummand r F).coeff j) =
      ∑ F ∈ Ico (⊥ : TruncatedFlat α r) ⊤,
        if j=r+1-F.1.card then ((Fintype.card α-F.1.card-1).choose (r-F.1.card):ℤ) else 0 := by
    apply sum_congr rfl
    intro F hF
    rw [uniformSummand_proper r hr F (mem_Ico.mp hF).2.ne, coeff_C_mul, coeff_X_pow]
    split_ifs <;> simp
  rw [hs, truncated_proper_sum r hr (fun k => if j=r+1-k then
    ((Fintype.card α-k-1).choose (r-k):ℤ) else 0)]
  rw [sum_eq_single (r+1-j)]
  · rw [ite_eq_left (by omega), show r-(r+1-j)=j-1 by omega]
  · intro k hk hne
    have hk' := mem_range.mp hk
    rw [ite_eq_right (by omega : ¬j=r+1-k), mul_zero]
  · intro hnot
    exact False.elim (hnot (mem_range.mpr (by omega)))

theorem uniformQ_high_coeff (r i : ℕ) (hr : r+1 ≤ Fintype.card α) (hi : r+1 ≤ 2*i) :
    (uniformQ (α:=α) r).coeff i = 0 := by
  have hne : (⊥ : TruncatedFlat α r) ≠ ⊤ := by
    intro he
    have h := congrArg (truncatedRank α r) he
    rw [truncatedRank_bot, truncatedRank_top α r hr] at h
    omega
  exact inverseKL_high_coeff (truncatedRank α r) (truncatedRank_strictMono α r).monotone
    ⊥ ⊤ bot_le hne i (by simpa only [truncatedRank_top α r hr, truncatedRank_bot, Nat.sub_zero] using hi)

/-- The reflected uniform coefficient formula, proved from its finite subset
flat lattice and the defining inverse-KL support condition. -/
theorem uniformY_coeff_lower (r k : ℕ) (hr : r+1 ≤ Fintype.card α) (hk : 2*k ≤ r+1) :
    (uniformY (α:=α) r).coeff k =
      (Fintype.card α).choose k * ((Fintype.card α-k-1).choose (r-k):ℤ) := by
  have hs := inverseZ_coeff_symm (truncatedRank α r) (truncatedRank_strictMono α r).monotone
    ⊥ ⊤ k (by simp only [truncatedRank_top α r hr, truncatedRank_bot, Nat.sub_zero]; omega)
  simp only [truncatedRank_top α r hr, truncatedRank_bot, Nat.sub_zero] at hs
  change (uniformY (α:=α) r).coeff k = (uniformY (α:=α) r).coeff (r+1-k) at hs
  rw [hs, uniformY_coeff_split r (r+1-k) hr (by omega) (by omega),
    uniformQ_high_coeff r (r+1-k) hr (by omega), zero_add,
    Nat.sub_sub_self (by omega : k ≤ r+1), show r+1-k-1=r-k by omega]

/-- The literal lower-half inverse-Q coefficient, derived by removing the
proper Boolean-flat contribution from the proved inverse-Z formula. -/
theorem uniformQ_coeff_lower (r k : ℕ) (hr : r+1 ≤ Fintype.card α)
    (hk : 2*k ≤ r+1) (hk0 : 1≤k) :
    (uniformQ (α:=α) r).coeff k =
      (Fintype.card α).choose k * ((Fintype.card α-k-1).choose (r-k):ℤ) -
      (Fintype.card α).choose (r+1-k) *
        ((Fintype.card α-(r+1-k)-1).choose (k-1):ℤ) := by
  have h := uniformY_coeff_split (α:=α) r k hr hk0 (by omega)
  rw [uniformY_coeff_lower r k hr hk] at h
  omega

end Paving
