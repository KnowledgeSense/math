import EmbeddingDimensionStrata.CotangentCoordinates

/-! # Linear division coordinates on the actual quotient algebra -/
set_option maxRecDepth 4096
noncomputable section
namespace EmbeddingDimensionStrata
variable {K : Type*} [Field K]

/-- Any initial portion of division descends to the semantic jet quotient. -/
def jetReduction (p : NormalCoordinate → K) (N : ℕ) (hN : N ≤ 60) : Jet K 60 →ₗ[K] Jet K 60 where
  toFun := Quotient.lift (fun f : PowerSeries K => jetMap K 60 (reduceSeries p N f)) (by
    intro f g hfg
    exact jet_reduceSeries_eq p f g N hN (Quotient.sound hfg))
  map_add' := by
    intro x y
    obtain ⟨f,rfl⟩ := jetMap_surjective 60 x
    obtain ⟨g,rfl⟩ := jetMap_surjective 60 y
    change jetMap K 60 (reduceSeries p N (f+g)) = _
    rw [map_add, map_add]
    rfl
  map_smul' := by
    intro a x
    obtain ⟨f,rfl⟩ := jetMap_surjective 60 x
    change jetMap K 60 (reduceSeries p N (a • f)) = _
    rw [map_smul, map_smul]
    rfl

@[simp]
theorem jetReduction_jetMap (p : NormalCoordinate → K) (N : ℕ) (hN : N ≤ 60) (f : PowerSeries K) :
    jetReduction p N hN (jetMap K 60 f) = jetMap K 60 (reduceSeries p N f) := rfl

/-- The coefficient c_k in the monic division basis, defined on actual jets. -/
def divisionCoefficient (p : NormalCoordinate → K) (k : Fin 60) : Jet K 60 →ₗ[K] K :=
  (jetCoeff 60 k).comp (jetReduction p k.val (Nat.le_of_lt k.isLt))

@[simp]
theorem divisionCoefficient_jetMap (p : NormalCoordinate → K) (k : Fin 60) (f : PowerSeries K) :
    divisionCoefficient p k (jetMap K 60 f) = PowerSeries.coeff k.val (reduceSeries p k.val f) := rfl

theorem divisionCoefficient_basis (p : NormalCoordinate → K) (k : Fin 60) (n : ℕ)
    (hn : n ∈ valuesBelowConductor) :
    divisionCoefficient p k (jetMap K 60 (basisSeries p n)) = if k.val = n then 1 else 0 := by
  rw [divisionCoefficient_jetMap]
  by_cases hkn : k.val ≤ n
  · rw [reduceSeries_eq_self_of_low_zero p _ k.val (fun i hi =>
      (basisSeries_monic p n hn).1 i (by omega))]
    split_ifs with heq
    · rw [heq]
      exact (basisSeries_monic p n hn).2
    · exact (basisSeries_monic p n hn).1 k.val (by omega)
  · rw [reduceSeries_basisSeries p n k.val hn (by omega), map_zero,
      ite_eq_right (by omega : k.val ≠ n)]

/-- The five generator components in the actual monic basis. -/
def linearTerms (p : NormalCoordinate → K) : Jet K 60 →ₗ[K] (Fin 5 → K) :=
  LinearMap.pi fun i => divisionCoefficient p ⟨generatorValue i,generatorValue_lt i⟩

theorem linearTerms_jetMap (p : NormalCoordinate → K) (f : PowerSeries K) (i : Fin 5) :
    linearTerms p (jetMap K 60 f) i =
      PowerSeries.coeff (generatorValue i) (reduceSeries p (generatorValue i) f) := rfl

/-- The two actual relation vectors have exactly the paper's coefficients. -/
theorem linearTerms_relationF (p : NormalCoordinate → K) :
    linearTerms p (jetMap K 60 (relationF p)) =
      ![0,0,0,relationCoordinate p 0,relationCoordinate p 2] := by
  funext i
  fin_cases i
  · exact reduceSeries_low_zero p _ 45 10 (relationF_low p) 10 (by omega)
  · exact reduceSeries_low_zero p _ 45 11 (relationF_low p) 11 (by omega)
  · exact reduceSeries_low_zero p _ 45 34 (relationF_low p) 34 (by omega)
  · rfl
  · rfl

theorem linearTerms_relationG (p : NormalCoordinate → K) :
    linearTerms p (jetMap K 60 (relationG p)) = ![0,0,0,0,relationCoordinate p 1] := by
  funext i
  fin_cases i
  · exact reduceSeries_low_zero p _ 57 10 (relationG_low p) 10 (by omega)
  · exact reduceSeries_low_zero p _ 57 11 (relationG_low p) 11 (by omega)
  · exact reduceSeries_low_zero p _ 57 34 (relationG_low p) 34 (by omega)
  · exact reduceSeries_low_zero p _ 57 46 (relationG_low p) 46 (by omega)
  · rfl

end EmbeddingDimensionStrata
