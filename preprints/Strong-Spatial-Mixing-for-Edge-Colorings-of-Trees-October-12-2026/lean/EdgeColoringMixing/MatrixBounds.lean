import EdgeColoringMixing.ScalarTransfer
import EdgeColoringMixing.FiniteProbability
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

namespace EdgeColoringMixing
open Finset Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A weighted rank-one bound, also valid at zero diagonal weights. -/
theorem weighted_rank_one_bound (p v : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hv : ∀ i, p i = 0 → v i = 0) {B : ℝ} (hB : 0 ≤ B)
    (hs : ∑ i, v i ^ 2 / p i ≤ B) :
    (B • Matrix.diagonal p - Matrix.vecMulVec v v).PosSemidef := by
  let D := Matrix.diagonal p
  have hD : D.PosSemidef := Matrix.posSemidef_diagonal_iff.mpr hp
  have hV : (Matrix.vecMulVec v v).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star v
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((hD.smul hB).isHermitian.sub hV.isHermitian) ?_
  intro z
  let w := fun i => v i / p i
  have hpw (i : ι) : p i * w i = v i := by
    dsimp only [w]
    by_cases hi : p i = 0
    · simp [hi, hv i hi]
    · field_simp
  have hw (i : ι) : w i * (p i * w i) = v i ^ 2 / p i := by
    rw [hpw]
    dsimp only [w]
    ring
  have hmix : z ⬝ᵥ D *ᵥ w = z ⬝ᵥ v := by
    simp only [D, dotProduct, Matrix.mulVec_diagonal]
    simp_rw [hpw]
  have hwD : w ⬝ᵥ D *ᵥ w = ∑ i, v i ^ 2 / p i := by
    simp only [D, dotProduct, Matrix.mulVec_diagonal]
    simp_rw [hw]
  have hcs := semidefinite_cauchy_schwarz hD z w
  rw [hmix, hwD] at hcs
  have hz : 0 ≤ z ⬝ᵥ D *ᵥ z := by simpa using hD.dotProduct_mulVec_nonneg z
  have hbound := hcs.trans (mul_le_mul_of_nonneg_left hs hz)
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, Matrix.vecMulVec_mulVec]
  simp only [op_smul_eq_mul]
  rw [dotProduct_comm v z]
  change 0 ≤ B * (z ⬝ᵥ D *ᵥ z) - (z ⬝ᵥ v) * (z ⬝ᵥ v)
  nlinarith

/-- Absolute row-sum domination implies a Loewner bound for every symmetric real matrix. -/
theorem diagonal_dominance_bound (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (a : ι → ℝ) (ha : ∀ i, ∑ j, |A i j| ≤ a i) :
    (Matrix.diagonal a - A).PosSemidef := by
  have hD : (Matrix.diagonal a).IsHermitian := by simp
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hD.sub hA) ?_
  intro z
  have hsymm (i j : ι) : A i j = A j i := by
    have h := congrArg (fun M : Matrix ι ι ℝ => M i j) hA.eq
    simpa using h.symm
  have hterm (i j : ι) : z i * (A i j * z j) ≤
      |A i j| * ((z i)^2 + (z j)^2) / 2 := by
    have h₁ := mul_le_mul_of_nonneg_left (neg_abs_le (A i j)) (sq_nonneg (z i - z j))
    have h₂ := mul_le_mul_of_nonneg_left (le_abs_self (A i j)) (sq_nonneg (z i + z j))
    nlinarith [sq_nonneg (z i + z j), sq_nonneg (z i - z j), abs_nonneg (A i j)]
  have hrow : (∑ i, ∑ j, |A i j| * ((z i)^2 + (z j)^2) / 2) =
      ∑ i, (z i)^2 * ∑ j, |A i j| := by
    simp only [mul_add, add_div, Finset.sum_add_distrib, ← Finset.sum_div]
    have hc : (∑ i, ∑ j, |A i j| * (z j)^2) = ∑ i, ∑ j, |A i j| * (z i)^2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hsymm j i]
    rw [hc]
    calc
      _ = ∑ i, ∑ j, |A i j| * (z i)^2 := by ring
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_mul]
        ring
  have hbound : z ⬝ᵥ A *ᵥ z ≤ z ⬝ᵥ Matrix.diagonal a *ᵥ z := by
    calc
      _ = ∑ i, ∑ j, z i * (A i j * z j) := by
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
      _ ≤ ∑ i, ∑ j, |A i j| * ((z i)^2 + (z j)^2) / 2 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
      _ = ∑ i, (z i)^2 * ∑ j, |A i j| := hrow
      _ ≤ ∑ i, (z i)^2 * a i :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (ha i) (sq_nonneg _))
      _ = _ := by
        simp only [dotProduct, Matrix.mulVec_diagonal]
        apply Finset.sum_congr rfl
        intro i _
        ring
  simpa only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] using hbound

end EdgeColoringMixing
