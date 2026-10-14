import EmbeddingDimensionStrata.BasisDivision

/-! # The exact image of the genuine ideal square in generator coordinates -/
noncomputable section
namespace EmbeddingDimensionStrata
variable {K : Type*} [Field K]

def relationVectorSpace (p : NormalCoordinate → K) : Submodule K (Fin 5 → K) :=
  Submodule.span K {linearTerms p (jetMap K 60 (relationF p)),
    linearTerms p (jetMap K 60 (relationG p))}

theorem linearTerms_basis_decomposable (p : NormalCoordinate → K) (n : ℕ)
    (hn : n ∈ decomposableValues) : linearTerms p (jetMap K 60 (basisSeries p n)) = 0 :=
  decomposableJetSpace_le_ker p (Submodule.subset_span ⟨⟨n,hn⟩,rfl⟩)

theorem linearTerms_mul_X_basis_tail (p : NormalCoordinate → K) (k : ℕ)
    (hk : k ∈ valuesBelowConductor) (hk45 : 45 ≤ k) :
    linearTerms p (jetMap K 60 (normalSeries p 0) * jetMap K 60 (basisSeries p k)) = 0 := by
  by_cases hk50 : 50 ≤ k
  · rw [mul_basisJet_vanish p 0 k hk (by change 60 ≤ 10+k; omega), map_zero]
  · have hall : ∀ n ∈ valuesBelowConductor, 45 ≤ n → n < 50 → n = 45 ∨ n = 46 := by decide
    rcases hall k hk hk45 (by omega) with rfl | rfl
    · have heq : jetMap K 60 (normalSeries p 0) * jetMap K 60 (basisSeries p 45) =
          jetMap K 60 (basisSeries p 55) := by
        simp only [basisSeries, basisExponent, seriesMonomial, pow_zero, pow_one,
          one_mul, mul_one, map_mul]
        ring
      rw [heq]
      exact linearTerms_basis_decomposable p 55 (by decide)
    · have heq : jetMap K 60 (normalSeries p 0) * jetMap K 60 (basisSeries p 46) =
          jetMap K 60 (basisSeries p 56) := by
        simp [basisSeries, basisExponent, seriesMonomial, map_mul]
      rw [heq]
      exact linearTerms_basis_decomposable p 56 (by decide)

theorem linearTerms_mul_H_basis_tail (p : NormalCoordinate → K) (k : ℕ)
    (hk : k ∈ valuesBelowConductor) (hk45 : 45 ≤ k) :
    linearTerms p (jetMap K 60 (normalSeries p 1) * jetMap K 60 (basisSeries p k)) ∈
      relationVectorSpace p := by
  by_cases hk50 : 50 ≤ k
  · rw [mul_basisJet_vanish p 1 k hk (by change 60 ≤ 11+k; omega), map_zero]
    exact Submodule.zero_mem _
  · have hall : ∀ n ∈ valuesBelowConductor, 45 ≤ n → n < 50 → n = 45 ∨ n = 46 := by decide
    rcases hall k hk hk45 (by omega) with rfl | rfl
    · have heq : jetMap K 60 (normalSeries p 1) * jetMap K 60 (basisSeries p 45) =
          jetMap K 60 (basisSeries p 56) + jetMap K 60 (relationG p) := by
        simp only [relationG, basisSeries, basisExponent, seriesMonomial, pow_zero, pow_one,
          one_mul, mul_one, map_sub, map_mul, map_pow]
        ring
      rw [heq, map_add, linearTerms_basis_decomposable p 56 (by decide), zero_add]
      exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · have heq : jetMap K 60 (normalSeries p 1) * jetMap K 60 (basisSeries p 46) =
          jetMap K 60 (basisSeries p 57) := by
        simp [basisSeries, basisExponent, seriesMonomial, map_mul]
      rw [heq, linearTerms_basis_decomposable p 57 (by decide)]
      exact Submodule.zero_mem _

theorem linearTerms_mul_X_F (p : ParameterSpace (K := K)) :
    linearTerms p.val (jetMap K 60 (normalSeries p.val 0) * jetMap K 60 (relationF p.val)) = 0 := by
  have hle : basisJetTailSpace p.val 45 ≤ LinearMap.ker
      ((linearTerms p.val).comp (LinearMap.mulLeft K (jetMap K 60 (normalSeries p.val 0)))) := by
    apply Submodule.span_le.mpr
    rintro x ⟨k,rfl⟩
    exact linearTerms_mul_X_basis_tail p.val k.val k.property.1 k.property.2
  exact hle (relationF_mem_tail_of_remainder_zero p.val
    (parameterSpace_remainder_zero p _ (relationF_mem p.val)))

theorem linearTerms_mul_H_F (p : ParameterSpace (K := K)) :
    linearTerms p.val (jetMap K 60 (normalSeries p.val 1) * jetMap K 60 (relationF p.val)) ∈
      relationVectorSpace p.val := by
  have hle : basisJetTailSpace p.val 45 ≤ (relationVectorSpace p.val).comap
      ((linearTerms p.val).comp (LinearMap.mulLeft K (jetMap K 60 (normalSeries p.val 1)))) := by
    apply Submodule.span_le.mpr
    rintro x ⟨k,rfl⟩
    exact linearTerms_mul_H_basis_tail p.val k.val k.property.1 k.property.2
  exact hle (relationF_mem_tail_of_remainder_zero p.val
    (parameterSpace_remainder_zero p _ (relationF_mem p.val)))

theorem relationF_mem_square (p : NormalCoordinate → K) :
    jetMap K 60 (relationF p) ∈ monomialDegreeSpace p 2 := by
  have hh := Submodule.sub_mem (monomialDegreeSpace p 2)
    (jetMonomial_mem_degreeSpace p 2 (0,4,0,0,0) (by decide))
    (jetMonomial_mem_degreeSpace p 2 (1,0,1,0,0) (by decide))
  simpa only [jetMonomial, seriesMonomial, relationF, pow_zero, pow_one, one_mul,
    mul_one, map_sub] using hh

theorem relationG_mem_square (p : NormalCoordinate → K) :
    jetMap K 60 (relationG p) ∈ monomialDegreeSpace p 2 := by
  have hh := Submodule.sub_mem (monomialDegreeSpace p 2)
    (jetMonomial_mem_degreeSpace p 2 (0,2,1,0,0) (by decide))
    (jetMonomial_mem_degreeSpace p 2 (1,0,0,1,0) (by decide))
  simpa only [jetMonomial, seriesMonomial, relationG, pow_zero, pow_one, one_mul,
    mul_one, map_sub] using hh

/-- Precisely the two paper relation vectors occur in the image of the
actual ideal square. The higher coincidences contribute no new relation. -/
theorem square_linearTerms_image (p : ParameterSpace (K := K)) :
    (monomialDegreeSpace p.val 2).map (linearTerms p.val) = relationVectorSpace p.val := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro x ⟨a,ha,rfl⟩
    change linearTerms p.val (jetMonomial p.val a) ∈ relationVectorSpace p.val
    rcases smallExponents_partition a ha.1 with heq | rfl | rfl | rfl | rfl
    · have hw : monomialWeight a ∈ valuesBelowConductor := by
        apply (gamma_below_conductor ((mem_smallExponents_iff a).mp ha.1)).mp
        exact ⟨a.1,a.2.1,a.2.2.1,a.2.2.2.1,a.2.2.2.2,rfl⟩
      have hd : monomialWeight a ∈ decomposableValues := by
        have hall : ∀ n ∈ valuesBelowConductor,
            2 ≤ monomialDegree (basisExponent n) → n ∈ decomposableValues := by decide
        apply hall _ hw
        rw [← heq]
        exact ha.2
      rw [heq]
      change linearTerms p.val (jetMap K 60 (basisSeries p.val (monomialWeight a))) ∈ _
      rw [linearTerms_basis_decomposable p.val _ hd]
      exact Submodule.zero_mem _
    · have heq : jetMonomial p.val (0,4,0,0,0) =
          jetMap K 60 (basisSeries p.val 44) + jetMap K 60 (relationF p.val) := by
        simp only [jetMonomial, relationF, basisSeries, basisExponent, seriesMonomial,
          pow_zero, pow_one, one_mul, mul_one, map_sub, map_mul, map_pow]
        ring
      rw [heq, map_add, linearTerms_basis_decomposable p.val 44 (by decide), zero_add]
      exact Submodule.subset_span (Set.mem_insert _ _)
    · have heq : jetMonomial p.val (1,4,0,0,0) =
          jetMap K 60 (basisSeries p.val 54) +
            jetMap K 60 (normalSeries p.val 0) * jetMap K 60 (relationF p.val) := by
        simp only [jetMonomial, relationF, basisSeries, basisExponent, seriesMonomial,
          pow_zero, pow_one, mul_one, map_sub, map_mul, map_pow]
        ring
      rw [heq, map_add, linearTerms_basis_decomposable p.val 54 (by decide),
        linearTerms_mul_X_F p, add_zero]
      exact Submodule.zero_mem _
    · have heq : jetMonomial p.val (0,5,0,0,0) =
          jetMap K 60 (basisSeries p.val 55) +
            jetMap K 60 (normalSeries p.val 1) * jetMap K 60 (relationF p.val) := by
        simp only [jetMonomial, relationF, basisSeries, basisExponent, seriesMonomial,
          pow_zero, pow_one, one_mul, mul_one, map_sub, map_mul, map_pow]
        ring
      rw [heq, map_add, linearTerms_basis_decomposable p.val 55 (by decide), zero_add]
      exact linearTerms_mul_H_F p
    · have heq : jetMonomial p.val (0,2,1,0,0) =
          jetMap K 60 (basisSeries p.val 56) + jetMap K 60 (relationG p.val) := by
        simp only [jetMonomial, relationG, basisSeries, basisExponent, seriesMonomial,
          pow_zero, pow_one, one_mul, mul_one, map_sub, map_mul, map_pow]
        ring
      rw [heq, map_add, linearTerms_basis_decomposable p.val 56 (by decide), zero_add]
      exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ⟨jetMap K 60 (relationF p.val),relationF_mem_square p.val,rfl⟩
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨jetMap K 60 (relationG p.val),relationG_mem_square p.val,rfl⟩

end EmbeddingDimensionStrata
