import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

/-!
# The full matrix trickle-down step

This file proves the matrix conclusion of Abdolazimi--Liu--Oveis Gharan,
arXiv:2106.03845v2, Theorem 3.2, used as Theorem 2.5 of the manuscript.
All matrix comparisons mean positive semidefiniteness of the difference.
-/
namespace EdgeColoringMixing.MatrixTrickleDown
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
private theorem symmetric_dot {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (x y : n → ℝ) : x ⬝ᵥ A *ᵥ y = (A *ᵥ x) ⬝ᵥ y := by
  simpa only [star_trivial, dotProduct_comm] using
    hA.star_dotProduct_mulVec_comm x y

/-- Polynomial-order inversion, proved directly with eigenvectors, without a
commutativity hypothesis or an assumed operator-monotonicity theorem. -/
theorem polynomial_order_inversion {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    {α : ℝ} (hα : 0 < α)
    (hcap : ((1 / (2 * α)) • (1 : Matrix n n ℝ) - A).PosSemidef)
    (hpoly : ((B - α • (B * B)) - (A - α • (A * A))).PosSemidef) :
    (B - A).PosSemidef := by
  let hD : (B - A).IsHermitian := hB.sub hA
  rw [hD.posSemidef_iff_eigenvalues_nonneg]
  intro i
  let v : n → ℝ := ⇑(hD.eigenvectorBasis i)
  let t : ℝ := hD.eigenvalues i
  have hv : (B - A) *ᵥ v = t • v := hD.mulVec_eigenvectorBasis i
  have hvnorm : v ⬝ᵥ v = 1 := by
    have h := real_inner_self_eq_norm_sq (hD.eigenvectorBasis i)
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      hD.eigenvectorBasis.orthonormal.1 i, one_pow] using h
  have hBv : B *ᵥ v = A *ᵥ v + t • v := by
    rw [sub_mulVec] at hv
    exact (sub_eq_iff_eq_add.mp hv).trans (add_comm _ _)
  have hAA : v ⬝ᵥ (A * A) *ᵥ v = (A *ᵥ v) ⬝ᵥ (A *ᵥ v) := by
    rw [← mulVec_mulVec, symmetric_dot hA]
  have hBB : v ⬝ᵥ (B * B) *ᵥ v =
      (A *ᵥ v) ⬝ᵥ (A *ᵥ v) + 2 * t * (v ⬝ᵥ A *ᵥ v) + t ^ 2 := by
    rw [← mulVec_mulVec, symmetric_dot hB, hBv]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hvnorm]
    rw [dotProduct_comm (A *ᵥ v) v]
    ring
  have hq := hcap.dotProduct_mulVec_nonneg v
  simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, hvnorm] at hq
  have hp := hpoly.dotProduct_mulVec_nonneg v
  simp only [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul] at hp
  rw [hAA, hBB, hBv, dotProduct_add, dotProduct_smul, hvnorm] at hp
  simp only [smul_eq_mul, mul_one] at hp
  change 0 ≤ t
  by_contra ht
  have htneg : t < 0 := lt_of_not_ge ht
  have hcap' : 2 * α * (v ⬝ᵥ A *ᵥ v) ≤ 1 := by
    have := mul_nonneg (show 0 ≤ 2 * α by positivity) hq
    field_simp at this
    nlinarith
  have hm := mul_le_mul_of_nonpos_left hcap' (le_of_lt htneg)
  have hs : 0 < α * t ^ 2 := mul_pos hα (sq_pos_of_neg htneg)
  nlinarith


omit [DecidableEq n] in
private theorem rank_one_hermitian (u : n → ℝ) : (vecMulVec u u).IsHermitian := by
  simpa using (Matrix.posSemidef_vecMulVec_self_star u).isHermitian

omit [DecidableEq n] in
/-- Remove the arbitrary rank-one coefficient in a link by centering its test vector. -/
theorem center_link_bound {D L : Matrix n n ℝ} {u v : n → ℝ}
    (hD : D.IsHermitian) (hL : L.IsHermitian)
    (hDu : D *ᵥ u = v) (hLu : L *ᵥ u = v) (hvu : v ⬝ᵥ u = 1)
    {α ℓ : ℝ} (hbound : (ℓ • D - (L - α • vecMulVec v v)).PosSemidef) :
    (ℓ • D + (1 - ℓ) • vecMulVec v v - L).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (((hD.smul (by simp [IsSelfAdjoint])).add
      ((rank_one_hermitian v).smul (by simp [IsSelfAdjoint]))).sub hL)
  intro x
  let a : ℝ := v ⬝ᵥ x
  let z : n → ℝ := x - a • u
  have hvz : v ⬝ᵥ z = 0 := by simp [z, dotProduct_sub, dotProduct_smul, hvu, a]
  have hq := hbound.dotProduct_mulVec_nonneg z
  simp only [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul, vecMulVec_mulVec, op_smul_eq_smul, hvz, zero_smul, dotProduct_zero, mul_zero,
    sub_zero] at hq
  have hDx : u ⬝ᵥ D *ᵥ x = a := by rw [symmetric_dot hD, hDu]
  have hLx : u ⬝ᵥ L *ᵥ x = a := by rw [symmetric_dot hL, hLu]
  have hDz : z ⬝ᵥ D *ᵥ z = x ⬝ᵥ D *ᵥ x - a ^ 2 := by
    simp only [z, mulVec_sub, mulVec_smul, hDu, sub_dotProduct, smul_dotProduct,
      dotProduct_sub, dotProduct_smul, smul_eq_mul, hDx]
    rw [dotProduct_comm x v, dotProduct_comm u v, hvu]
    change x ⬝ᵥ D *ᵥ x - a * a - a * (a - a * 1) = _
    ring
  have hLz : z ⬝ᵥ L *ᵥ z = x ⬝ᵥ L *ᵥ x - a ^ 2 := by
    simp only [z, mulVec_sub, mulVec_smul, hLu, sub_dotProduct, smul_dotProduct,
      dotProduct_sub, dotProduct_smul, smul_eq_mul, hLx]
    rw [dotProduct_comm x v, dotProduct_comm u v, hvu]
    change x ⬝ᵥ L *ᵥ x - a * a - a * (a - a * 1) = _
    ring
  rw [hDz, hLz] at hq
  simp only [star_trivial, sub_mulVec, add_mulVec, smul_mulVec, dotProduct_sub,
    dotProduct_add, dotProduct_smul, smul_eq_mul, vecMulVec_mulVec]
  rw [dotProduct_comm x v]
  change 0 ≤ ℓ * (x ⬝ᵥ D *ᵥ x) + (1 - ℓ) * (a * a) - x ⬝ᵥ L *ᵥ x
  nlinarith


/-- The scalar trickle-down estimate is derived from Garland's quadratic inequality
and the simple stationary eigenspace. Its result is a full matrix inequality. -/
theorem scalar_trickle_down {S : Matrix n n ℝ} {u : n → ℝ}
    (hS : S.IsHermitian) (hSu : S *ᵥ u = u) (hu : u ⬝ᵥ u = 1)
    (hcontract : ((1 : Matrix n n ℝ) - S).PosSemidef)
    (hconnected : ∀ v : n → ℝ, u ⬝ᵥ v = 0 → S *ᵥ v = v → v = 0)
    {ℓ β : ℝ} (hℓ : 0 ≤ ℓ) (hℓ1 : ℓ < 1) (hβ : 1 ≤ β)
    (hstep : (ℓ • (1 : Matrix n n ℝ) + (1 - ℓ) • (S * S) - S).PosSemidef) :
    ((ℓ / (1 - ℓ)) • (1 : Matrix n n ℝ) -
      (S - β • vecMulVec u u)).PosSemidef := by
  let c : ℝ := ℓ / (1 - ℓ)
  have hc : 0 ≤ c := div_nonneg hℓ (by linarith)
  let A : Matrix n n ℝ := S - β • vecMulVec u u
  have hA : A.IsHermitian := hS.sub ((rank_one_hermitian u).smul (by simp [IsSelfAdjoint]))
  have hH : (c • (1 : Matrix n n ℝ) - A).IsHermitian :=
    (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])).sub hA
  rw [hH.posSemidef_iff_eigenvalues_nonneg]
  intro i
  let v : n → ℝ := ⇑(hH.eigenvectorBasis i)
  let t : ℝ := hH.eigenvalues i
  have hv : (c • (1 : Matrix n n ℝ) - A) *ᵥ v = t • v :=
    hH.mulVec_eigenvectorBasis i
  have hvnorm : v ⬝ᵥ v = 1 := by
    have h := real_inner_self_eq_norm_sq (hH.eigenvectorBasis i)
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      hH.eigenvectorBasis.orthonormal.1 i, one_pow] using h
  change 0 ≤ t
  by_contra ht
  have htneg : t < 0 := lt_of_not_ge ht
  let z : ℝ := c - t
  have hz : 0 < z := by dsimp [z]; linarith
  have hAv : A *ᵥ v = z • v := by
    simp only [sub_mulVec, smul_mulVec, one_mulVec] at hv
    calc
      A *ᵥ v = c • v - t • v := by linear_combination -hv
      _ = z • v := by rw [← sub_smul]
  have huv : u ⬝ᵥ v = 0 := by
    have h := congrArg (fun w : n → ℝ => u ⬝ᵥ w) hAv
    simp only [A, sub_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
      dotProduct_sub, dotProduct_smul, smul_eq_mul] at h
    rw [symmetric_dot hS, hSu] at h
    rw [hu] at h
    have hcne : 1 - β - z ≠ 0 := by linarith
    have hprod : (1 - β - z) * (u ⬝ᵥ v) = 0 := by nlinarith [h]
    exact (mul_eq_zero.mp hprod).resolve_left hcne
  have hSv : S *ᵥ v = z • v := by
    simpa [A, sub_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, huv] using hAv
  have hq := hcontract.dotProduct_mulVec_nonneg v
  simp only [star_trivial, sub_mulVec, one_mulVec, dotProduct_sub, hSv,
    dotProduct_smul, smul_eq_mul, hvnorm, mul_one] at hq
  have hz1 : z < 1 := by
    apply lt_of_le_of_ne (by linarith)
    intro heq
    have hvzero := hconnected v huv (by simpa [heq] using hSv)
    simp [hvzero] at hvnorm
  have hp := hstep.dotProduct_mulVec_nonneg v
  simp only [star_trivial, sub_mulVec, add_mulVec, smul_mulVec, one_mulVec,
    dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul,
    ← mulVec_mulVec, hSv, mulVec_smul, hvnorm, mul_one] at hp
  have hfactor : (1 - z) * ((1 - ℓ) * z - ℓ) ≤ 0 := by nlinarith
  have hroot : (1 - ℓ) * z ≤ ℓ := by
    have := nonpos_of_mul_nonpos_right hfactor (by linarith : 0 < 1 - z)
    linarith
  have hzc : z ≤ c := (le_div_iff₀ (by linarith : 0 < 1 - ℓ)).mpr (by nlinarith)
  dsimp [z] at hzc
  linarith


omit [DecidableEq n] in
/-- The adjusted walk has exactly the same quadratic polynomial as the walk. -/
theorem adjusted_polynomial {S : Matrix n n ℝ} {u : n → ℝ}
    (hS : S.IsHermitian) (hSu : S *ᵥ u = u) (hu : u ⬝ᵥ u = 1)
    {α : ℝ} (hα : α ≠ 0) :
    let A := S - (2 - 1 / α) • vecMulVec u u
    A - α • (A * A) = S - α • (S * S) := by
  dsimp only
  have hSR : S * vecMulVec u u = vecMulVec u u := by rw [mul_vecMulVec, hSu]
  have huS : u ᵥ* S = u := by
    rw [← mulVec_transpose, show Sᵀ = S by simpa using hS.eq, hSu]
  have hRS : vecMulVec u u * S = vecMulVec u u := by rw [vecMulVec_mul, huS]
  have hRR : vecMulVec u u * vecMulVec u u = vecMulVec u u := by
    rw [vecMulVec_mul_vecMulVec, hu, one_smul]
  simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, hSR, hRS, hRR]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

variable {m : Type*} [Fintype m]

omit [Fintype n] [DecidableEq n] in
private theorem average_posSemidef (w : m → ℝ) (hw : ∀ x, 0 ≤ w x)
    (F : m → Matrix n n ℝ) (hF : ∀ x, (F x).PosSemidef) :
    (∑ x, w x • F x).PosSemidef :=
  Matrix.posSemidef_sum _ (fun x _ => (hF x).smul (hw x))

/-- The full matrix trickle-down step from local link moments and recursive matrix
hypotheses. This is the normalized form of the actual ALG conclusion, not merely
an eigenvalue estimate. `hconnected` says that the stationary eigenspace is simple.
The three average identities are precisely the local-walk/link identities. -/
theorem matrix_trickle_down_step
    {S M : Matrix n n ℝ} {u : n → ℝ}
    (hS : S.IsHermitian) (hM : M.IsHermitian)
    (hSu : S *ᵥ u = u) (hu : u ⬝ᵥ u = 1)
    (hcontract : ((1 : Matrix n n ℝ) - S).PosSemidef)
    (hconnected : ∀ v : n → ℝ, u ⬝ᵥ v = 0 → S *ᵥ v = v → v = 0)
    (w : m → ℝ) (hw : ∀ x, 0 ≤ w x)
    (D L N : m → Matrix n n ℝ) (v : m → n → ℝ)
    (hD : ∀ x, (D x).IsHermitian) (hL : ∀ x, (L x).IsHermitian)
    (hDu : ∀ x, D x *ᵥ u = v x) (hLu : ∀ x, L x *ᵥ u = v x)
    (hvu : ∀ x, v x ⬝ᵥ u = 1)
    (havgD : ∑ x, w x • D x = 1)
    (havgL : ∑ x, w x • L x = S)
    (havgR : ∑ x, w x • vecMulVec (v x) (v x) = S * S)
    {α : ℝ} (hα : 1 ≤ α)
    (hlower : ∀ x, (N x - (L x - α • vecMulVec (v x) (v x))).PosSemidef)
    (hupper : ∀ x, ((1 / (2 * α + 1)) • D x - N x).PosSemidef)
    (hrecursive : (M - α • (M * M) - ∑ x, w x • N x).PosSemidef) :
    (M - (S - (2 - 1 / α) • vecMulVec u u)).PosSemidef := by
  have hαpos : 0 < α := by linarith
  let ℓ : ℝ := 1 / (2 * α + 1)
  have hlocal x : (ℓ • D x - (L x - α • vecMulVec (v x) (v x))).PosSemidef := by
    convert (hupper x).add (hlower x) using 1; abel
  have hcenter x := center_link_bound (hD x) (hL x) (hDu x) (hLu x) (hvu x) (hlocal x)
  have havg := average_posSemidef w hw _ hcenter
  have hsum : (∑ x, w x • (ℓ • D x + (1 - ℓ) • vecMulVec (v x) (v x) - L x)) =
      ℓ • (∑ x, w x • D x) +
      (1 - ℓ) • (∑ x, w x • vecMulVec (v x) (v x)) - ∑ x, w x • L x := by
    simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.smul_sum]
    congr 2 <;> apply Finset.sum_congr rfl <;> intro x _ <;> exact smul_comm _ _ _
  rw [hsum, havgD, havgR, havgL] at havg
  have hℓ : 0 ≤ ℓ := by dsimp [ℓ]; positivity
  have hℓ1 : ℓ < 1 := by dsimp [ℓ]; apply (div_lt_one (by positivity)).mpr; linarith
  have hβ : 1 ≤ 2 - 1 / α := by
    have : 1 / α ≤ 1 := (div_le_one hαpos).mpr hα
    linarith
  have hAcap := scalar_trickle_down hS hSu hu hcontract hconnected hℓ hℓ1 hβ havg
  have hratio : ℓ / (1 - ℓ) = 1 / (2 * α) := by
    dsimp [ℓ]
    field_simp
    ring
  rw [hratio] at hAcap
  have havgLower := average_posSemidef w hw _ hlower
  have hsumLower : (∑ x, w x • (N x - (L x - α • vecMulVec (v x) (v x)))) =
      (∑ x, w x • N x) - (S - α • (S * S)) := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [havgL, ← havgR, Finset.smul_sum]
    congr 2
    apply Finset.sum_congr rfl
    intro x _
    exact smul_comm _ _ _
  rw [hsumLower] at havgLower
  have hpoly : ((M - α • (M * M)) - (S - α • (S * S))).PosSemidef := by
    convert hrecursive.add havgLower using 1; abel
  have hpolyA := adjusted_polynomial hS hSu hu (ne_of_gt hαpos)
  rw [← hpolyA] at hpoly
  exact polynomial_order_inversion
    (hS.sub ((rank_one_hermitian u).smul (by simp [IsSelfAdjoint]))) hM hαpos hAcap hpoly


omit [DecidableEq n] in
/-- Transport the full normalized conclusion back to any original coordinates.
For the local walk, `H = diagonal (sqrt π)`, `H S Hᵀ = Π P`, and `H u = π`. -/
theorem unnormalize_conclusion {S M : Matrix n n ℝ} {u : n → ℝ} {β : ℝ}
    (H : Matrix m n ℝ)
    (h : (M - (S - β • vecMulVec u u)).PosSemidef) :
    (H * M * Hᵀ - (H * S * Hᵀ - β • vecMulVec (H *ᵥ u) (H *ᵥ u))).PosSemidef := by
  have htransport := h.mul_mul_conjTranspose_same H
  have hrank : H * vecMulVec u u * Hᵀ = vecMulVec (H *ᵥ u) (H *ᵥ u) := by
    rw [mul_vecMulVec, vecMulVec_mul, vecMul_transpose]
  simpa only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, hrank] using htransport

/-- A hierarchy of normalized local walks.  The average identities are Garland's
identities; `restriction` embeds a child link into its parent's coordinates.
No covariance bound or matrix trickle-down conclusion is part of these data. -/
structure WalkHierarchy (F : Type*) (V : F → Type*) (C : F → Type*)
    [∀ f, Fintype (V f)] [∀ f, DecidableEq (V f)] [∀ f, Fintype (C f)] where
  depth : F → ℕ
  depth_ge_two : ∀ f, 2 ≤ depth f
  child : (f : F) → C f → F
  child_depth : ∀ f, 3 ≤ depth f → ∀ x, depth (child f x) + 1 = depth f
  walk : (f : F) → Matrix (V f) (V f) ℝ
  stationary : (f : F) → V f → ℝ
  hermitian : ∀ f, (walk f).IsHermitian
  walk_stationary : ∀ f, walk f *ᵥ stationary f = stationary f
  stationary_unit : ∀ f, stationary f ⬝ᵥ stationary f = 1
  contractive : ∀ f, ((1 : Matrix (V f) (V f) ℝ) - walk f).PosSemidef
  connected : ∀ f (v : V f → ℝ), stationary f ⬝ᵥ v = 0 → walk f *ᵥ v = v → v = 0
  weight : (f : F) → C f → ℝ
  weight_nonneg : ∀ f x, 0 ≤ weight f x
  restriction : (f : F) → (x : C f) → Matrix (V f) (V (child f x)) ℝ
  restriction_stationary : ∀ f x,
    (restriction f x)ᵀ *ᵥ stationary f = stationary (child f x)
  average_identity : ∀ f, 3 ≤ depth f →
    ∑ x, weight f x • (restriction f x * (restriction f x)ᵀ) = 1
  average_walk : ∀ f, 3 ≤ depth f →
    ∑ x, weight f x • (restriction f x * walk (child f x) * (restriction f x)ᵀ) = walk f
  average_rank_one : ∀ f, 3 ≤ depth f →
    (∑ x, weight f x • vecMulVec (restriction f x *ᵥ stationary (child f x))
      (restriction f x *ᵥ stationary (child f x))) = walk f * walk f



/-- Dirichlet-form identity for a finite nonnegative symmetric conductance matrix. -/
theorem conductance_energy {A : Matrix n n ℝ} (hA : A.IsHermitian) (x : n → ℝ) :
    x ⬝ᵥ (diagonal (fun i => ∑ j, A i j) - A) *ᵥ x =
      (∑ i, ∑ j, A i j * (x i - x j) ^ 2) / 2 := by
  have hsym i j : A j i = A i j := by simpa using congrFun (congrFun hA.eq i) j
  have hq : x ⬝ᵥ (diagonal (fun i => ∑ j, A i j) - A) *ᵥ x =
      ∑ i, ∑ j, A i j * (x i * x i - x i * x j) := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
    simp only [dotProduct, mulVec_diagonal]
    change (∑ i, x i * ((∑ j, A i j) * x i)) -
      (∑ i, x i * (∑ j, A i j * x j)) = _
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hq, ← add_self_div_two (∑ i, ∑ j, A i j * (x i * x i - x i * x j))]
  conv_lhs => enter [1, 2]; rw [Finset.sum_comm]
  simp only [← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hsym]
  ring

/-- Every reversible finite nonnegative walk is contractive after normalization. -/
theorem conductance_laplacian_posSemidef {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (hnonneg : ∀ i j, 0 ≤ A i j) :
    (diagonal (fun i => ∑ j, A i j) - A).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((Matrix.isHermitian_diagonal (fun i => ∑ j, A i j)).sub hA)
  intro x
  rw [star_trivial, conductance_energy hA]
  exact div_nonneg (Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => mul_nonneg (hnonneg i j) (sq_nonneg _)))) (by norm_num)

/-- A zero Dirichlet form is constant across every positive-conductance edge. -/
theorem eq_on_positive_edges_of_energy_zero {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (hnonneg : ∀ i j, 0 ≤ A i j) {x : n → ℝ}
    (hx : x ⬝ᵥ (diagonal (fun i => ∑ j, A i j) - A) *ᵥ x = 0) :
    ∀ i j, 0 < A i j → x i = x j := by
  rw [conductance_energy hA, div_eq_zero_iff] at hx
  have hsum := hx.resolve_right (by norm_num)
  have hterm i j : 0 ≤ A i j * (x i - x j) ^ 2 := mul_nonneg (hnonneg i j) (sq_nonneg _)
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg (fun j _ => hterm i j))).mp hsum
  intro i j hij
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm i j)).mp (hi i (Finset.mem_univ i))
  have hs := (mul_eq_zero.mp (hj j (Finset.mem_univ j))).resolve_left (ne_of_gt hij)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)


/-- Connectivity turns zero Dirichlet energy into a constant vector. -/
theorem conductance_energy_zero_constant {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hconnected : ∀ i j, Relation.ReflTransGen (fun i j => 0 < A i j) i j)
    {x : n → ℝ}
    (hx : x ⬝ᵥ (diagonal (fun i => ∑ j, A i j) - A) *ᵥ x = 0) :
    ∀ i j, x i = x j := by
  have hedge := eq_on_positive_edges_of_energy_zero hA hnonneg hx
  intro i j
  induction hconnected i j with
  | refl => rfl
  | @tail b c _ hbc ih => exact ih.trans (hedge b c hbc)

/-- The connected walk's only weighted-mean-zero zero-energy vector is zero. -/
theorem conductance_energy_zero_of_orthogonal {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hconnected : ∀ i j, Relation.ReflTransGen (fun i j => 0 < A i j) i j)
    {x p : n → ℝ} (hp : ∑ i, p i = 1) (hpx : p ⬝ᵥ x = 0)
    (hx : x ⬝ᵥ (diagonal (fun i => ∑ j, A i j) - A) *ᵥ x = 0) : x = 0 := by
  have hconstant := conductance_energy_zero_constant hA hnonneg hconnected hx
  ext i
  have hsum : p ⬝ᵥ x = x i := by
    unfold dotProduct
    simp_rw [← hconstant i]
    rw [← Finset.sum_mul, hp, one_mul]
  exact hsum.symm.trans hpx

namespace WalkHierarchy

variable {F : Type*} {V : F → Type*} {C : F → Type*}
  [∀ f, Fintype (V f)] [∀ f, DecidableEq (V f)] [∀ f, Fintype (C f)]

/-- The inductive matrix conclusion of Theorem 2.5.  The hypotheses on `M` are
exactly its upper bound, codimension-two base case, and recursive matrix bound.
The complete matrix estimate, retaining its rank-one term, is proved for every face. -/
theorem matrix_trickle_down (H : WalkHierarchy F V C)
    (M : (f : F) → Matrix (V f) (V f) ℝ)
    (hM : ∀ f, (M f).IsHermitian)
    (hcap : ∀ f, ((((H.depth f : ℝ) - 1) / (3 * H.depth f - 1)) •
      (1 : Matrix (V f) (V f) ℝ) - M f).PosSemidef)
    (hbase : ∀ f, H.depth f = 2 →
      (M f - (H.walk f - (2 : ℝ) • vecMulVec (H.stationary f) (H.stationary f))).PosSemidef)
    (hrecursive : ∀ f, 3 ≤ H.depth f →
      (M f - (((H.depth f : ℝ) - 1) / ((H.depth f : ℝ) - 2)) • (M f * M f) -
        ∑ x, H.weight f x •
          (H.restriction f x * M (H.child f x) * (H.restriction f x)ᵀ)).PosSemidef) :
    ∀ f, (M f - (H.walk f - ((H.depth f : ℝ) / ((H.depth f : ℝ) - 1)) •
      vecMulVec (H.stationary f) (H.stationary f))).PosSemidef := by
  suffices h : ∀ k : ℕ, ∀ f, H.depth f = k →
      (M f - (H.walk f - ((H.depth f : ℝ) / ((H.depth f : ℝ) - 1)) •
        vecMulVec (H.stationary f) (H.stationary f))).PosSemidef by
    exact fun f => h _ f rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro f hdepth
    by_cases hk2 : k = 2
    · have hf2 : H.depth f = 2 := hdepth.trans hk2
      simpa only [hf2, Nat.cast_ofNat, show (2 : ℝ) / (2 - 1) = 2 by norm_num] using hbase f hf2
    have hf3 : 3 ≤ H.depth f := by have := H.depth_ge_two f; omega
    have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (hdepth ▸ hf3)
    let α : ℝ := ((k : ℝ) - 1) / ((k : ℝ) - 2)
    have hα : 1 ≤ α := by dsimp [α]; apply (le_div_iff₀ (by linarith)).mpr; linarith
    let T := H.restriction f
    let D : C f → Matrix (V f) (V f) ℝ := fun x => T x * (T x)ᵀ
    let L : C f → Matrix (V f) (V f) ℝ :=
      fun x => T x * H.walk (H.child f x) * (T x)ᵀ
    let N : C f → Matrix (V f) (V f) ℝ := fun x => T x * M (H.child f x) * (T x)ᵀ
    let v : C f → V f → ℝ := fun x => T x *ᵥ H.stationary (H.child f x)
    have hD x : (D x).IsHermitian := by
      simpa [D] using Matrix.isHermitian_mul_conjTranspose_self (T x)
    have hL x : (L x).IsHermitian := by
      simpa [L] using Matrix.isHermitian_mul_mul_conjTranspose (T x) (H.hermitian _)
    have hDu x : D x *ᵥ H.stationary f = v x := by
      simp only [D, v, ← mulVec_mulVec, T, H.restriction_stationary]
    have hLu x : L x *ᵥ H.stationary f = v x := by
      simp only [L, v, ← mulVec_mulVec, T, H.restriction_stationary, H.walk_stationary]
    have hvu x : v x ⬝ᵥ H.stationary f = 1 := by
      dsimp [v]
      rw [dotProduct_comm, ← dotProduct_transpose_mulVec,
        show (T x)ᵀ *ᵥ H.stationary f = H.stationary (H.child f x) from
          H.restriction_stationary f x, H.stationary_unit]
    have hchildDepth x : (H.depth (H.child f x) : ℝ) = (k : ℝ) - 1 := by
      have hc := H.child_depth f hf3 x
      rw [hdepth] at hc
      have hr : (H.depth (H.child f x) : ℝ) + 1 = k := by exact_mod_cast hc
      linarith
    have hlower x : (N x - (L x - α • vecMulVec (v x) (v x))).PosSemidef := by
      have hc := H.child_depth f hf3 x
      have hi := ih (H.depth (H.child f x)) (by omega) (H.child f x) rfl
      have hi' := unnormalize_conclusion (T x) hi
      have hcoef : (H.depth (H.child f x) : ℝ) / ((H.depth (H.child f x) : ℝ) - 1) = α := by
        rw [hchildDepth]
        dsimp [α]
        congr 1; ring
      simpa only [hcoef] using hi'
    have hupper x : ((1 / (2 * α + 1)) • D x - N x).PosSemidef := by
      have hc := (hcap (H.child f x)).mul_mul_conjTranspose_same (T x)
      have hcoef : ((H.depth (H.child f x) : ℝ) - 1) /
          (3 * H.depth (H.child f x) - 1) = 1 / (2 * α + 1) := by
        rw [hchildDepth]
        dsimp [α]
        field_simp [show (k : ℝ) - 2 ≠ 0 by linarith]
        ring
      simpa only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
        Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hcoef] using hc
    have hresult := matrix_trickle_down_step (H.hermitian f) (hM f)
      (H.walk_stationary f) (H.stationary_unit f) (H.contractive f) (H.connected f)
      (H.weight f) (H.weight_nonneg f) D L N v hD hL hDu hLu hvu
      (H.average_identity f hf3) (H.average_walk f hf3) (H.average_rank_one f hf3)
      hα hlower hupper (by simpa [N, T, α, hdepth] using hrecursive f hf3)
    have hcoef : 2 - 1 / α = (H.depth f : ℝ) / ((H.depth f : ℝ) - 1) := by
      rw [hdepth]
      dsimp [α]
      field_simp [show (k : ℝ) - 1 ≠ 0 by linarith]
      ring
    simpa only [hcoef] using hresult

end WalkHierarchy

end EdgeColoringMixing.MatrixTrickleDown





