import EmbeddingDimensionStrata.AugmentationIdeal

/-! # Actual powers of the augmentation ideal as monomial spans -/
noncomputable section
namespace EmbeddingDimensionStrata

lemma monomialDegree_add (a b : Exponent) : monomialDegree (a+b) = monomialDegree a + monomialDegree b := by
  rcases b with ⟨a',b',c',d',e'⟩
  rcases a with ⟨a,b,c,d,e⟩
  simp only [monomialDegree, Prod.fst_add, Prod.snd_add]
  omega

lemma monomialDegree_eq_zero (a : Exponent) : monomialDegree a = 0 ↔ a = (0,0,0,0,0) := by
  rcases a with ⟨a,b,c,d,e⟩
  simp only [monomialDegree, Prod.mk.injEq]
  omega

lemma monomialWeight_pos_of_degree (a : Exponent) (ha : 0 < monomialDegree a) : 0 < monomialWeight a := by
  rcases a with ⟨a,b,c,d,e⟩
  dsimp [monomialDegree, monomialWeight] at *
  omega

/-- Every monomial of degree at least two is a product of two positive-degree
monomials; this statement has no finite search cutoff. -/
lemma exponent_split_degree_two (a : Exponent) (ha : 2 ≤ monomialDegree a) :
    ∃ b c : Exponent, a = b+c ∧ 1 ≤ monomialDegree b ∧ 1 ≤ monomialDegree c := by
  rcases a with ⟨a,b,c,d,e⟩
  dsimp [monomialDegree] at ha
  by_cases ha0 : 0 < a
  · refine ⟨(1,0,0,0,0),(a-1,b,c,d,e),?_,by decide,?_⟩
    · simp only [Prod.mk_add_mk, Prod.mk.injEq]; omega
    · dsimp [monomialDegree]; omega
  · by_cases hb0 : 0 < b
    · refine ⟨(0,1,0,0,0),(a,b-1,c,d,e),?_,by decide,?_⟩
      · simp only [Prod.mk_add_mk, Prod.mk.injEq]; omega
      · dsimp [monomialDegree]; omega
    · by_cases hc0 : 0 < c
      · refine ⟨(0,0,1,0,0),(a,b,c-1,d,e),?_,by decide,?_⟩
        · simp only [Prod.mk_add_mk, Prod.mk.injEq]; omega
        · dsimp [monomialDegree]; omega
      · by_cases hd0 : 0 < d
        · refine ⟨(0,0,0,1,0),(a,b,c,d-1,e),?_,by decide,?_⟩
          · simp only [Prod.mk_add_mk, Prod.mk.injEq]; omega
          · dsimp [monomialDegree]; omega
        · refine ⟨(0,0,0,0,1),(a,b,c,d,e-1),?_,by decide,?_⟩
          · simp only [Prod.mk_add_mk, Prod.mk.injEq]; omega
          · dsimp [monomialDegree]; omega

variable {K : Type*} [Field K]

/-- The subspace of actual jets spanned by monomials of total degree at least d. -/
def monomialDegreeSpace (p : NormalCoordinate → K) (d : ℕ) : Submodule K (Jet K 60) :=
  Submodule.span K (jetMonomial p '' {a | a ∈ smallExponents ∧ d ≤ monomialDegree a})

theorem jetMonomial_mem_degreeSpace (p : NormalCoordinate → K) (d : ℕ) (a : Exponent)
    (ha : d ≤ monomialDegree a) : jetMonomial p a ∈ monomialDegreeSpace p d := by
  by_cases hs : a ∈ smallExponents
  · exact Submodule.subset_span ⟨a,⟨hs,ha⟩,rfl⟩
  · rw [jetMonomial_eq_zero p a (by
      have hh := (mem_smallExponents_iff a).not.mp hs
      omega)]
    exact Submodule.zero_mem _

theorem degreeSpace_le_algebra (p : NormalCoordinate → K) (d : ℕ) :
    monomialDegreeSpace p d ≤ (parameterJetAlgebra p).toSubmodule := by
  apply Submodule.span_le.mpr
  rintro x ⟨a,_,rfl⟩
  exact jetMonomial_mem p a

theorem augmentation_jetMonomial_pos (p : NormalCoordinate → K) (a : Exponent)
    (ha : 0 < monomialDegree a) : jetAugmentation (jetMonomial p a) = 0 := by
  change PowerSeries.coeff 0 (seriesMonomial p a) = 0
  exact (seriesMonomial_monic p a).1 0 (monomialWeight_pos_of_degree a ha)

/-- Removing the constant coefficient is a linear operation on genuine jets. -/
def removeJetConstant : Jet K 60 →ₗ[K] Jet K 60 :=
  LinearMap.id - (jetAugmentation (K := K)).toLinearMap.smulRight 1

theorem removeJetConstant_apply (x : Jet K 60) :
    removeJetConstant x = x - jetAugmentation x • (1 : Jet K 60) := rfl

theorem removeConstant_algebra_mem (p : NormalCoordinate → K) (x : Jet K 60)
    (hx : x ∈ parameterJetAlgebra p) : removeJetConstant x ∈ monomialDegreeSpace p 1 := by
  have hle : (parameterJetAlgebra p).toSubmodule ≤
      (monomialDegreeSpace p 1).comap removeJetConstant := by
    rw [parameterJetAlgebra_span]
    apply Submodule.span_le.mpr
    rintro y ⟨a,ha,rfl⟩
    change removeJetConstant (jetMonomial p a) ∈ monomialDegreeSpace p 1
    by_cases hz : monomialDegree a = 0
    · rw [(monomialDegree_eq_zero a).mp hz, jetMonomial_zero, removeJetConstant_apply, map_one,
        one_smul, sub_self]
      exact Submodule.zero_mem _
    · rw [removeJetConstant_apply, augmentation_jetMonomial_pos p a (by omega), zero_smul, sub_zero]
      exact jetMonomial_mem_degreeSpace p 1 a (by omega)
  exact hle hx

/-- The degree-positive monomial space is precisely the actual algebra's
augmentation ideal after embedding into the jet algebra. -/
theorem mem_degreeSpace_one_iff (p : NormalCoordinate → K) (x : Jet K 60) :
    x ∈ monomialDegreeSpace p 1 ↔ x ∈ parameterJetAlgebra p ∧ jetAugmentation x = 0 := by
  constructor
  · intro hx
    refine ⟨degreeSpace_le_algebra p 1 hx, ?_⟩
    have hle : monomialDegreeSpace p 1 ≤ LinearMap.ker (jetAugmentation (K := K)).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro y ⟨a,ha,rfl⟩
      exact augmentation_jetMonomial_pos p a (by have hd := ha.2; omega)
    exact hle hx
  · rintro ⟨hx,hzero⟩
    have hm := removeConstant_algebra_mem p x hx
    rwa [removeJetConstant_apply, hzero, zero_smul, sub_zero] at hm

/-- The equality is with the image of the real maximal ideal, not a surrogate
subspace introduced as its definition. -/
theorem augmentationIdeal_image (p : NormalCoordinate → K) :
    ((augmentationIdeal p).restrictScalars K).map (parameterJetAlgebra p).val.toLinearMap =
      monomialDegreeSpace p 1 := by
  ext x
  rw [mem_degreeSpace_one_iff]
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y.property,hy⟩
  · rintro ⟨hx,hzero⟩
    exact ⟨⟨x,hx⟩,hzero,rfl⟩

theorem degreeSpace_mul_le (p : NormalCoordinate → K) (d e : ℕ) :
    monomialDegreeSpace p d * monomialDegreeSpace p e ≤ monomialDegreeSpace p (d+e) := by
  rw [monomialDegreeSpace, monomialDegreeSpace, Submodule.span_mul_span]
  apply Submodule.span_le.mpr
  rintro x ⟨y,⟨a,ha,rfl⟩,z,⟨b,hb,rfl⟩,rfl⟩
  change jetMonomial p a * jetMonomial p b ∈ monomialDegreeSpace p (d+e)
  rw [← jetMonomial_add]
  apply jetMonomial_mem_degreeSpace
  rw [monomialDegree_add]
  have hd := ha.2
  have he := hb.2
  omega

/-- The square of the positive monomial space is exactly the span of the 25
monomials of degree at least two. -/
theorem degreeSpace_one_sq (p : NormalCoordinate → K) :
    monomialDegreeSpace p 1 * monomialDegreeSpace p 1 = monomialDegreeSpace p 2 := by
  apply le_antisymm (degreeSpace_mul_le p 1 1)
  apply Submodule.span_le.mpr
  rintro x ⟨a,ha,rfl⟩
  obtain ⟨b,c,hab,hb,hc⟩ := exponent_split_degree_two a ha.2
  rw [hab,jetMonomial_add]
  exact Submodule.mul_mem_mul (jetMonomial_mem_degreeSpace p 1 b hb)
    (jetMonomial_mem_degreeSpace p 1 c hc)

/-- The span computation is the image of the actual ideal square in the
actual quotient algebra. -/
theorem augmentationIdeal_square_image (p : NormalCoordinate → K) :
    ((augmentationIdeal p ^ 2).restrictScalars K).map (parameterJetAlgebra p).val.toLinearMap =
      monomialDegreeSpace p 2 := by
  rw [pow_two, Ideal.restrictScalars_mul, Submodule.map_mul,
    augmentationIdeal_image, degreeSpace_one_sq]

end EmbeddingDimensionStrata
