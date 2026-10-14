import MainTheorems.WishartBlocks.NoncentralResponseGrowth

namespace ResearchMain.WishartBlocks

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

namespace BlockPartition

noncomputable def oneBlockEquiv {p : ℕ} (P : BlockPartition p 1) : Fin (P.size 0) ≃ Fin p :=
  Equiv.ofBijective (P.inclusion 0) ⟨P.inclusion_injective 0, by
    intro i
    obtain ⟨⟨j, k⟩, hk⟩ := P.index.surjective i
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact ⟨k, hk⟩⟩

theorem oneBlock_determinant {p : ℕ} (P : BlockPartition p 1) (W : Matrix (Fin p) (Fin p) ℝ) :
    (P.block W 0).det = W.det := by
  exact Matrix.det_submatrix_equiv_self (P.oneBlockEquiv) W

theorem oneBlock_product {p : ℕ} (P : BlockPartition p 1) (ν : Fin 1 → ℝ)
    (W : Matrix (Fin p) (Fin p) ℝ) : P.determinantProduct ν W = W.det ^ ν 0 := by
  simp only [determinantProduct, determinantPower, Fin.prod_univ_one, P.oneBlock_determinant]

theorem oneBlock_response {p k : ℕ} (P : BlockPartition p 1) (α : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (K : Matrix (Fin k) (Fin p) ℝ) (ν : Fin 1 → ℝ) :
    P.noncentralProductResponse α S K ν = noncentralDeterminantResponse α S K (ν 0) := by
  funext W
  unfold noncentralProductResponse noncentralDeterminantResponse
  simp_rw [P.oneBlock_product]

def single (p : ℕ) (hp : 0 < p) : BlockPartition p 1 where
  size := fun _ => p
  size_pos := fun _ => hp
  index := {
    toFun := fun x => x.2
    invFun := fun i => ⟨0, i⟩
    left_inv := by intro x; rcases x with ⟨j, i⟩; have h : j = 0 := Subsingleton.elim _ _; subst j; rfl
    right_inv := fun _ => rfl }

theorem single_block (p : ℕ) (hp : 0 < p) (W : Matrix (Fin p) (Fin p) ℝ) (j : Fin 1) :
    (single p hp).block W j = W := by
  ext i k
  rfl

theorem single_product (p : ℕ) (hp : 0 < p) (b : ℝ) (W : Matrix (Fin p) (Fin p) ℝ) :
    (single p hp).determinantProduct (fun _ => b) W = W.det ^ b := by
  simp only [determinantProduct, determinantPower, Fin.prod_univ_one, single_block]
  rfl

theorem single_response {p k : ℕ} (hp : 0 < p) (α b : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (K : Matrix (Fin k) (Fin p) ℝ)
    (W : Matrix (Fin k) (Fin k) ℝ) :
    (single p hp).noncentralProductResponse α S K (fun _ => b) W =
      noncentralDeterminantResponse α S K b W := by
  unfold noncentralProductResponse noncentralDeterminantResponse
  simp_rw [single_product]

end BlockPartition

theorem noncentralDeterminantResponse_continuousOn {p r : ℕ} (hp : 0 < p)
    {α b : ℝ} (hα : (p : ℝ) - 1 < α - (r : ℝ)) (hb : 0 ≤ b)
    (S : Matrix (Fin p) (Fin p) ℝ) (K : Matrix (Fin r) (Fin p) ℝ) :
    ContinuousOn (noncentralDeterminantResponse α S K b) {W | W.PosDef} := by
  have he : noncentralDeterminantResponse α S K b =
      (BlockPartition.single p hp).noncentralProductResponse α S K (fun _ => b) := by
    funext W
    exact (BlockPartition.single_response hp α b S K W).symm
  rw [he]
  exact (BlockPartition.single p hp).noncentralProductResponse_continuousOn _ (fun _ => hb) hα S K

theorem noncentralDeterminantResponse_measurable {p r : ℕ} (hp : 0 < p)
    {α b : ℝ} (hα : (p : ℝ) - 1 < α - (r : ℝ)) (hb : 0 ≤ b)
    (S : Matrix (Fin p) (Fin p) ℝ) (K : Matrix (Fin r) (Fin p) ℝ) :
    Measurable (noncentralDeterminantResponse α S K b) := by
  have he : noncentralDeterminantResponse α S K b =
      (BlockPartition.single p hp).noncentralProductResponse α S K (fun _ => b) := by
    funext W
    exact (BlockPartition.single_response hp α b S K W).symm
  rw [he]
  exact (BlockPartition.single p hp).noncentralProductResponse_measurable _ (fun _ => hb) hα S K

theorem noncentralDeterminantResponse_growth {p r : ℕ} (hp : 0 < p)
    {α b : ℝ} (hα : (p : ℝ) - 1 < α - (r : ℝ)) (hb : 0 ≤ b)
    (S : Matrix (Fin p) (Fin p) ℝ) (K : Matrix (Fin r) (Fin p) ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ β : ℝ, ∀ W : Matrix (Fin r) (Fin r) ℝ, W.PosDef →
      ‖noncentralDeterminantResponse α S K b W‖ ≤ D * (1 + ‖W‖) ^ β := by
  have h := (BlockPartition.single p hp).noncentralProductResponse_growth (fun _ => b) (fun _ => hb) hα S K
  simpa only [BlockPartition.single_response] using h

theorem noncentralDeterminantResponse_nonneg {p r : ℕ} (α b : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (K : Matrix (Fin r) (Fin p) ℝ)
    (W : Matrix (Fin r) (Fin r) ℝ) : 0 ≤ noncentralDeterminantResponse α S K b W := by
  apply integral_nonneg_of_ae
  filter_upwards [noncentralWishart_positiveSemidefinite α S (covarianceMeanRows W K)] with B hB
  exact Real.rpow_nonneg hB.det_nonneg b

end ResearchMain.WishartBlocks

