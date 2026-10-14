import EmbeddingDimensionStrata.TopologyVanKampen
import Mathlib.Geometry.Manifold.Instances.Sphere

noncomputable section
namespace EmbeddingDimensionStrata
namespace TopologyObstructions
open Set Metric Module
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Stereographic projection makes a once-punctured unit sphere contractible. -/
def spherePunctureHomeomorph (v : sphere (0 : E) 1) :
    ({v}ᶜ : Set (sphere (0 : E) 1)) ≃ₜ (ℝ ∙ v.val)ᗮ :=
  (stereographic (norm_eq_of_mem_sphere v)).toHomeomorphSourceTarget.trans
    (Homeomorph.Set.univ _)

theorem spherePuncture_simplyConnected (v : sphere (0 : E) 1) :
    IsSimplyConnected ({v}ᶜ : Set (sphere (0 : E) 1)) :=
  (spherePunctureHomeomorph v).toHomotopyEquiv.simplyConnectedSpace

/-- Removing antipodal points from a sphere leaves a path-connected space,
provided the tangent hyperplane has dimension at least two. -/
theorem sphereDoublePuncture_pathConnected (v : sphere (0 : E) 1)
    (hdim : 1 < Module.rank ℝ (ℝ ∙ v.val)ᗮ) :
    IsPathConnected (({v}ᶜ : Set (sphere (0 : E) 1)) ∩ {-v}ᶜ) := by
  let e := stereographic (norm_eq_of_mem_sphere v)
  have hc : Continuous e.symm := (isOpenEmbedding_stereographic_symm
    (norm_eq_of_mem_sphere v)).continuous
  have hp := (isPathConnected_compl_singleton_of_one_lt_rank hdim (0 : (ℝ ∙ v.val)ᗮ)).image hc
  have he : e.symm '' ({0}ᶜ : Set (ℝ ∙ v.val)ᗮ) =
      ({v}ᶜ : Set (sphere (0 : E) 1)) ∩ {-v}ᶜ := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨e.map_target (Set.mem_univ z), ?_⟩
      intro h
      have heq : e.symm z = -v := h
      have hh := congrArg e heq
      rw [e.right_inv (Set.mem_univ z)] at hh
      have hn : e (-v) = 0 := stereographic_apply_neg v
      exact hz (hh.trans hn)
    · rintro ⟨hw, hwn⟩
      refine ⟨e w, ?_, e.left_inv hw⟩
      intro h
      have hn : e (-v) = 0 := stereographic_apply_neg v
      have hvn : -v ∈ e.source := by
        exact (ne_neg_of_mem_unit_sphere ℝ v).symm
      exact hwn (e.injOn hw hvn (h.trans hn.symm))
  rwa [he] at hp

/-- Unit spheres in real inner-product spaces are simply connected as soon as
the orthogonal hyperplane has dimension at least two. -/
theorem unitSphere_simplyConnected_of_orthogonal_rank (v : sphere (0 : E) 1)
    (hdim : 1 < Module.rank ℝ (ℝ ∙ v.val)ᗮ) :
    SimplyConnectedSpace (sphere (0 : E) 1) := by
  apply simplyConnected_of_two_open_cover ({v}ᶜ) ({-v}ᶜ)
    isOpen_compl_singleton isOpen_compl_singleton
    (spherePuncture_simplyConnected v) (spherePuncture_simplyConnected (-v))
    (sphereDoublePuncture_pathConnected v hdim)
  ext w
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  by_cases hw : w = v
  · right
    rw [hw]
    exact ne_neg_of_mem_unit_sphere ℝ v
  · exact Or.inl hw

/-- The standard real dimension criterion for a simply connected sphere. -/
theorem unitSphere_simplyConnected_of_finrank [FiniteDimensional ℝ E]
    (hdim : 2 < Module.finrank ℝ E) : SimplyConnectedSpace (sphere (0 : E) 1) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ E)
  obtain ⟨v, hv⟩ := NormedSpace.sphere_nonempty (E := E) (x := (0 : E)) |>.mpr
    (show (0 : ℝ) ≤ 1 by norm_num)
  apply unitSphere_simplyConnected_of_orthogonal_rank ⟨v, hv⟩
  have hn : v ≠ 0 := by
    intro h
    subst v
    simp at hv
  have hf := (ℝ ∙ v).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hn] at hf
  rw [← finrank_eq_rank]
  exact_mod_cast (show 1 < Module.finrank ℝ (ℝ ∙ v)ᗮ by omega)

/-- The complement of the origin in a real inner-product space of dimension
at least three is simply connected. -/
theorem puncturedInnerProductSpace_simplyConnected [FiniteDimensional ℝ E]
    (hdim : 2 < Module.finrank ℝ E) : SimplyConnectedSpace {z : E // z ≠ 0} := by
  have : SimplyConnectedSpace (sphere (0 : E) 1) :=
    unitSphere_simplyConnected_of_finrank hdim
  have : ContractibleSpace (Set.Ioi (0 : ℝ)) :=
    (convex_Ioi (0 : ℝ)).contractibleSpace ⟨1, by norm_num⟩
  let e := (homeomorphUnitSphereProd E).toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl _).prodCongr
      (ContractibleSpace.hequiv_unit (Set.Ioi (0 : ℝ))).some).trans
      (Homeomorph.prodUnique _ Unit).toHomotopyEquiv)
  exact e.simplyConnectedSpace

/-- The ordinary punctured complex three-space is simply connected. -/
theorem puncturedComplexTriple_simplyConnected :
    SimplyConnectedSpace {z : Fin 3 → ℂ // z ≠ 0} := by
  let F := EuclideanSpace ℂ (Fin 3)
  have : SimplyConnectedSpace {z : F // z ≠ 0} :=
    puncturedInnerProductSpace_simplyConnected (by
      rw [finrank_real_of_complex]
      simp [F])
  let e : {z : Fin 3 → ℂ // z ≠ 0} ≃ₜ {z : F // z ≠ 0} :=
    (EuclideanSpace.equiv (Fin 3) ℂ).symm.toHomeomorph.subtype
      (fun x => by
        exact not_congr ((EuclideanSpace.equiv (Fin 3) ℂ).symm.map_eq_zero_iff).symm)
  exact e.toHomotopyEquiv.simplyConnectedSpace

/-- Simple connectivity of the exact punctured product in its classical topology. -/
theorem classicalPuncturedProduct_simplyConnected (m : ℕ) :
    SimplyConnectedSpace (ClassicalPuncturedProduct m) := by
  have : SimplyConnectedSpace {z : Fin 3 → ℂ // z ≠ 0} :=
    puncturedComplexTriple_simplyConnected
  let e := ((ContractibleSpace.hequiv_unit (Fin m → ℂ)).some.prodCongr
      (ContinuousMap.HomotopyEquiv.refl {z : Fin 3 → ℂ // z ≠ 0})).trans
      (Homeomorph.uniqueProd Unit _).toHomotopyEquiv
  exact e.simplyConnectedSpace

/-- Simple connectivity also holds in the unsplit affine coordinate description. -/
theorem puncturedProduct_simplyConnected (m : ℕ) :
    SimplyConnectedSpace (GeometryObstructions.puncturedProduct (K := ℂ) m) := by
  have := classicalPuncturedProduct_simplyConnected m
  exact (puncturedProductHomeomorph m).toHomotopyEquiv.simplyConnectedSpace

/-- The exact dimensions of the proposed answer are topologically impossible. -/
theorem puncturedProduct54_not_homeomorphic_predicted :
    IsEmpty (ClassicalPuncturedProduct 54 ≃ₜ ClassicalPredictedProduct 56) := by
  constructor
  intro e
  have := classicalPuncturedProduct_simplyConnected 54
  exact predictedProduct_not_simply_connected 56 e.symm.toHomotopyEquiv.simplyConnectedSpace

/-- The same no-homeomorphism theorem on the original unsplit coordinates. -/
theorem puncturedCoordinates54_not_homeomorphic_predicted :
    IsEmpty (GeometryObstructions.puncturedProduct (K := ℂ) 54 ≃ₜ ClassicalPredictedProduct 56) := by
  constructor
  intro e
  exact (puncturedProduct54_not_homeomorphic_predicted.false
    ((puncturedProductHomeomorph 54).symm.trans e))

end TopologyObstructions
end EmbeddingDimensionStrata
