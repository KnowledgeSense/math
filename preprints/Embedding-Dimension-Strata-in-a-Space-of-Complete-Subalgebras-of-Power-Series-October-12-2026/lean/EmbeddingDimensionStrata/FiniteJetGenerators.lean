import EmbeddingDimensionStrata.NilpotentGenerators

/-! # The actual finite-jet algebra's minimum generator number -/
noncomputable section
namespace EmbeddingDimensionStrata
variable {K : Type*} [Field K]

lemma monomialWeight_ge_ten_degree (a : Exponent) :
    10 * monomialDegree a ≤ monomialWeight a := by
  rcases a with ⟨a,b,c,d,e⟩
  dsimp [monomialDegree, monomialWeight]
  omega

theorem degreeSpace_six_eq_bot (p : NormalCoordinate → K) :
    monomialDegreeSpace p 6 = ⊥ := by
  apply eq_bot_iff.mpr
  apply Submodule.span_le.mpr
  rintro x ⟨a, ha, rfl⟩
  have hw := (mem_smallExponents_iff a).mp ha.1
  have hd := ha.2
  have hwd := monomialWeight_ge_ten_degree a
  omega

/-- The true augmentation ideal is nilpotent of exponent at most six. -/
theorem augmentationIdeal_pow_six (p : NormalCoordinate → K) :
    augmentationIdeal p ^ 6 = ⊥ := by
  have himage : ∀ n : ℕ,
      ((augmentationIdeal p ^ (n+1)).restrictScalars K).map
        (parameterJetAlgebra p).val.toLinearMap ≤ monomialDegreeSpace p (n+1) := by
    intro n
    induction n with
    | zero => simp only [Nat.zero_add, Submodule.pow_one, augmentationIdeal_image, le_refl]
    | succ n ih =>
      rw [Submodule.pow_succ, Ideal.restrictScalars_mul, Submodule.map_mul, augmentationIdeal_image]
      exact (mul_le_mul' ih le_rfl).trans (degreeSpace_mul_le p (n+1) 1)
  apply eq_bot_iff.mpr
  intro x hx
  have hv := himage 5 (Submodule.mem_map_of_mem hx)
  rw [degreeSpace_six_eq_bot] at hv
  have heq : (x : Jet K 60) = 0 := hv
  exact Subtype.ext heq

/-- Exact generator criterion for the actual finite quotient algebra. -/
theorem parameter_generates_iff_cotangent_span (p : NormalCoordinate → K)
    {ι : Type*} (g : ι → parameterJetAlgebra p) :
    Algebra.adjoin K (Set.range g) = ⊤ ↔
      Submodule.span K (Set.range fun i =>
        NilpotentGenerators.cotangentClass (parameterAugmentation p) (g i)) = ⊤ :=
  NilpotentGenerators.adjoin_eq_top_iff_cotangent_span (parameterAugmentation p) g
    ⟨6, augmentationIdeal_pow_six p⟩

/-- Existence of a genuine generating family with exactly the embedding dimension. -/
theorem parameter_exists_generators_embeddingDimension (p : ParameterSpace (K := K)) :
    ∃ g : Fin (embeddingDimension p) → parameterJetAlgebra p.val,
      Algebra.adjoin K (Set.range g) = ⊤ :=
  NilpotentGenerators.exists_generators_finrank (parameterAugmentation p.val)
    ⟨6, augmentationIdeal_pow_six p.val⟩

/-- Minimality among all finite algebra-generating families, without a
zero-constant restriction on those families. -/
theorem parameter_embeddingDimension_le_generators (p : ParameterSpace (K := K))
    {n : ℕ} (g : Fin n → parameterJetAlgebra p.val)
    (hg : Algebra.adjoin K (Set.range g) = ⊤) : embeddingDimension p ≤ n :=
  NilpotentGenerators.cotangent_finrank_le_generators (parameterAugmentation p.val) g hg

/-- The minimum actual algebra generator number equals the actual cotangent finrank. -/
theorem parameter_isLeast_generatorNumbers (p : ParameterSpace (K := K)) :
    IsLeast (NilpotentGenerators.generatorNumbers (K := K) (A := parameterJetAlgebra p.val))
      (embeddingDimension p) :=
  NilpotentGenerators.isLeast_generatorNumbers (parameterAugmentation p.val)
    ⟨6, augmentationIdeal_pow_six p.val⟩


/-- Actual generation by at most n algebra generators is the cotangent bound. -/
theorem parameter_exists_n_generators_iff (p : ParameterSpace (K := K)) (n : ℕ) :
    (∃ g : Fin n → parameterJetAlgebra p.val,
      Algebra.adjoin K (Set.range g) = ⊤) ↔ embeddingDimension p ≤ n :=
  NilpotentGenerators.mem_generatorNumbers_iff (parameterAugmentation p.val)
    ⟨6, augmentationIdeal_pow_six p.val⟩ n

end EmbeddingDimensionStrata
