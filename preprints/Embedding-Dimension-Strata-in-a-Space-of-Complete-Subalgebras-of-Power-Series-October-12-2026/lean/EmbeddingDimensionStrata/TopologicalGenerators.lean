import EmbeddingDimensionStrata.FiniteJetGenerators
import EmbeddingDimensionStrata.NormalGenerators

/-! # Algebraic jet generation and genuine topological generation -/
noncomputable section
namespace EmbeddingDimensionStrata
open scoped PowerSeries.WithPiTopology
variable {K : Type*} [Field K] [TopologicalSpace K] [DiscreteTopology K]

/-- The image of a subalgebra in a discrete finite jet is unchanged by closure. -/
theorem topologicalClosure_map_jet (T : Subalgebra K (PowerSeries K)) (c : ℕ) :
    T.topologicalClosure.map (jetMap K c) = T.map (jetMap K c) := by
  apply le_antisymm _ (Subalgebra.map_mono T.le_topologicalClosure)
  have hle : T.topologicalClosure ≤ (T.map (jetMap K c)).comap (jetMap K c) := by
    apply Subalgebra.topologicalClosure_minimal _ (isClosed_comap_jetMap _)
    intro f hf
    exact ⟨f, hf, rfl⟩
  rintro x ⟨f, hf, rfl⟩
  exact hle hf

/-- For the actual complete Γ-subalgebra, conductor-60 generation is equivalent
to density. The converse uses the five semigroup generators below the conductor. -/
theorem topologicalClosure_eq_iff_jet_map_eq
    (S : CompleteGammaSubalgebra (K := K)) (T : Subalgebra K (PowerSeries K))
    (hTS : T ≤ S.val) :
    T.topologicalClosure = S.val ↔ T.map (jetMap K 60) = S.val.map (jetMap K 60) := by
  constructor
  · intro h
    rw [← h, topologicalClosure_map_jet]
  · intro h
    have hv : ∀ i : Fin 5, HasValue T (generatorValue i) := by
      intro i
      apply (jetHasValue_map_iff (generatorValue_lt i) T).mp
      rw [h]
      apply (jetHasValue_map_iff (generatorValue_lt i) S.val).mpr
      exact (S.property.2 _).mpr (generatorValue_gamma i)
    apply le_antisymm (Subalgebra.topologicalClosure_minimal hTS S.property.1)
    apply le_closure_of_same_values T S.val hTS
    intro n hn
    exact hasValue_of_gamma T (hv 0) (hv 1) (hv 2) (hv 3) (hv 4)
      ((S.property.2 n).mp hn)

/-- Actual topological generation by a family of elements of the complete algebra. -/
def TopologicallyGenerates (S : CompleteGammaSubalgebra (K := K))
    {ι : Type*} (g : ι → S.val) : Prop :=
  (Algebra.adjoin K (Set.range fun i => (g i : PowerSeries K))).topologicalClosure = S.val

/-- The actual finite-cardinality set, independent of any dimension formula. -/
def topologicalGeneratorNumbers (S : CompleteGammaSubalgebra (K := K)) : Set ℕ :=
  {n | ∃ g : Fin n → S.val, TopologicallyGenerates S g}

/-- The genuine quotient map restricted to the complete algebra. -/
def completeJetMap (S : CompleteGammaSubalgebra (K := K)) :
    S.val →ₐ[K] S.val.map (jetMap K 60) :=
  (jetMap K 60).domRestrict S.val |>.codRestrict _ (by intro f; exact ⟨f,f.property,rfl⟩)

omit [DiscreteTopology K] in
theorem completeJetMap_surjective (S : CompleteGammaSubalgebra (K := K)) :
    Function.Surjective (completeJetMap S) := by
  rintro ⟨x, f, hf, rfl⟩
  exact ⟨⟨f,hf⟩,rfl⟩

omit [TopologicalSpace K] [DiscreteTopology K] in
/-- Intrinsic algebra generation agrees with generation in the ambient algebra. -/
theorem subalgebra_adjoin_eq_top_iff {R : Type*} [CommRing R] [Algebra K R]
    (T : Subalgebra K R) {ι : Type*} (g : ι → T) :
    Algebra.adjoin K (Set.range g) = ⊤ ↔
      Algebra.adjoin K (Set.range fun i => (g i : R)) = T := by
  have hm : (Algebra.adjoin K (Set.range g)).map T.val =
      Algebra.adjoin K (Set.range fun i => (g i : R)) := by
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  have htop : (⊤ : Subalgebra K T).map T.val = T := by ext x; simp
  constructor
  · intro h
    rw [← hm, h, htop]
  · intro h
    apply (Subalgebra.map_injective (f := T.val) Subtype.val_injective)
    rw [hm, h, htop]

/-- A family topologically generates precisely when its actual jets generate. -/
theorem topologicallyGenerates_iff_jet_generates
    (S : CompleteGammaSubalgebra (K := K)) {ι : Type*} (g : ι → S.val) :
    TopologicallyGenerates S g ↔
      Algebra.adjoin K (Set.range fun i => completeJetMap S (g i)) = ⊤ := by
  rw [TopologicallyGenerates, topologicalClosure_eq_iff_jet_map_eq S _
    (Algebra.adjoin_le (by rintro x ⟨i,rfl⟩; exact (g i).property)),
    subalgebra_adjoin_eq_top_iff]
  rw [AlgHom.map_adjoin, ← Set.range_comp]
  rfl

/-- Truncation preserves every possible finite generator cardinality. -/
theorem topologicalGeneratorNumbers_eq_jet_generatorNumbers
    (S : CompleteGammaSubalgebra (K := K)) :
    topologicalGeneratorNumbers S =
      NilpotentGenerators.generatorNumbers (K := K) (A := S.val.map (jetMap K 60)) := by
  ext n
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨fun i => completeJetMap S (g i), (topologicallyGenerates_iff_jet_generates S g).mp hg⟩
  · rintro ⟨g, hg⟩
    choose f hf using fun i => completeJetMap_surjective S (g i)
    refine ⟨f, (topologicallyGenerates_iff_jet_generates S f).mpr ?_⟩
    simpa only [hf] using hg


/-- The minimum number of topological generators of an actual complete algebra
is the actual cotangent dimension of its conductor quotient. -/
theorem complete_isLeast_topologicalGeneratorNumbers
    (S : CompleteGammaSubalgebra (K := K)) :
    IsLeast (topologicalGeneratorNumbers S) (embeddingDimension (toParameterSpace S)) := by
  rw [topologicalGeneratorNumbers_eq_jet_generatorNumbers,
    ← parameterJetAlgebra_normalCoordinates]
  exact parameter_isLeast_generatorNumbers (toParameterSpace S)

/-- The same minimum for the complete algebra corresponding to a parameter. -/
theorem parameter_isLeast_topologicalGeneratorNumbers (p : ParameterSpace (K := K)) :
    IsLeast (topologicalGeneratorNumbers (fromParameterSpace p)) (embeddingDimension p) := by
  have h := complete_isLeast_topologicalGeneratorNumbers (fromParameterSpace p)
  have hp : toParameterSpace (fromParameterSpace p) = p :=
    (completeGammaParameterEquiv (K := K)).apply_symm_apply p
  rwa [hp] at h


/-- The at-most-n topological generator locus is exactly the actual cotangent bound. -/
theorem complete_exists_n_topologicalGenerators_iff
    (S : CompleteGammaSubalgebra (K := K)) (n : ℕ) :
    (∃ g : Fin n → S.val, TopologicallyGenerates S g) ↔
      embeddingDimension (toParameterSpace S) ≤ n := by
  change n ∈ topologicalGeneratorNumbers S ↔ _
  rw [topologicalGeneratorNumbers_eq_jet_generatorNumbers,
    ← parameterJetAlgebra_normalCoordinates]
  exact parameter_exists_n_generators_iff (toParameterSpace S) n

/-- At most n topological generators on the corresponding complete algebra. -/
theorem parameter_exists_n_topologicalGenerators_iff
    (p : ParameterSpace (K := K)) (n : ℕ) :
    (∃ g : Fin n → (fromParameterSpace p).val,
      TopologicallyGenerates (fromParameterSpace p) g) ↔ embeddingDimension p ≤ n := by
  rw [complete_exists_n_topologicalGenerators_iff]
  have hp : toParameterSpace (fromParameterSpace p) = p :=
    (completeGammaParameterEquiv (K := K)).apply_symm_apply p
  rw [hp]

end EmbeddingDimensionStrata
