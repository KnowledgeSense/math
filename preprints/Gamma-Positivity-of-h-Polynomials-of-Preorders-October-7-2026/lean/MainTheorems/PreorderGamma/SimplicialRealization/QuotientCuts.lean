import MainTheorems.PreorderGamma.SimplicialRealization.CanonicalDegree

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators Pointwise

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

def NoCutEdge (A K : Finset E) : Prop := ∀ a ∈ A, ∀ b ∈ K, ¬b ≤ a

def quotientCutMap (A K : Finset E) : (E → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun x => (∑ i ∈ A, x i) - ∑ i ∈ K, x i
  map_add' := by
    intro x y
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro c x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

omit [Fintype E] [Preorder E] in
theorem quotientCutMap_single (A K : Finset E) (i : E) :
    quotientCutMap A K (Pi.single i 1) =
      (if i ∈ A then 1 else 0) - (if i ∈ K then 1 else 0) := by
  classical
  simp [quotientCutMap, Pi.single_apply, eq_comm]

omit [Fintype E] in
theorem quotientCutMap_vertex_le (A K : Finset E) (hcut : NoCutEdge A K)
    {v : E → ℝ} (hv : v ∈ quotientVertices (E := E)) : quotientCutMap A K v ≤ 1 := by
  classical
  rcases (mem_quotientVertices _).mp hv with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩ |
    ⟨a, b, hab, rfl⟩
  · simp
  · rw [quotientCutMap_single]
    split_ifs <;> norm_num
  · rw [map_neg, quotientCutMap_single]
    split_ifs <;> norm_num
  · rw [map_sub, quotientCutMap_single, quotientCutMap_single]
    by_cases ha : a ∈ A <;> by_cases hak : a ∈ K <;>
      by_cases hba : b ∈ A <;> by_cases hb : b ∈ K
    all_goals first | exact (hcut a ha b hb hab).elim | norm_num [ha, hak, hba, hb]

omit [Fintype E] in
theorem quotientCutMap_le (A K : Finset E) (hcut : NoCutEdge A K)
    {x : E → ℝ} (hx : x ∈ quotientPolytope (E := E)) : quotientCutMap A K x ≤ 1 := by
  apply convexHull_min ?_ (convex_halfSpace_le (quotientCutMap A K).isLinear 1) hx
  intro v hv
  exact quotientCutMap_vertex_le A K hcut hv

def QuotientIntegerPoint (t : ℕ) (z : E → ℤ) : Prop :=
  (fun i => (z i : ℝ)) ∈ (t : ℝ) • quotientPolytope (E := E)

omit [Fintype E] in
theorem quotientIntegerPoint_cut (A K : Finset E) (hcut : NoCutEdge A K)
    {t : ℕ} {z : E → ℤ} (hz : QuotientIntegerPoint t z) :
    (∑ i ∈ A, z i) - (∑ i ∈ K, z i) ≤ (t : ℤ) := by
  obtain ⟨x, hx, heq⟩ := Set.mem_smul_set.mp hz
  have h := mul_le_mul_of_nonneg_left (quotientCutMap_le A K hcut hx) (Nat.cast_nonneg t)
  have he := congrArg (quotientCutMap A K) heq
  simp only [map_smul, smul_eq_mul] at he
  rw [he, mul_one] at h
  change (∑ i ∈ A, (z i : ℝ)) - (∑ i ∈ K, (z i : ℝ)) ≤ (t : ℝ) at h
  exact_mod_cast h

end ResearchMain.PreorderGamma.SimplicialRealization
