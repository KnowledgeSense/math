import EmbeddingDimensionStrata.MonomialIdeal
import EmbeddingDimensionStrata.JetBasis

/-! # Coordinates in the actual monic division basis -/
noncomputable section
namespace EmbeddingDimensionStrata
open Module
variable {K : Type*} [Field K]

def basisJetBasis (p : NormalCoordinate → K) : Basis ValueIndex K (basisJetSpace p) :=
  Basis.span (basisJets_linearIndependent p)

@[simp]
theorem basisJetBasis_coe (p : NormalCoordinate → K) (i : ValueIndex) :
    (basisJetBasis p i : Jet K 60) = jetMap K 60 (basisSeries p i.val) := by
  exact Basis.coe_span_apply _ _

theorem basisJetBasis_coord (p : NormalCoordinate → K) (i : ValueIndex) :
    (basisJetBasis p).coord i =
      (divisionCoefficient p ⟨i.val,valueIndex_lt i⟩).comp (basisJetSpace p).subtype := by
  classical
  apply (basisJetBasis p).ext
  intro j
  simp only [Basis.coord_apply, Basis.repr_self_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, basisJetBasis_coe, divisionCoefficient_basis p _ j.val j.property]
  congr 1
  exact propext ⟨fun h => (congrArg Subtype.val h).symm, fun h => Subtype.ext h.symm⟩

theorem basisJetExpansion (p : NormalCoordinate → K) (x : Jet K 60)
    (hx : x ∈ basisJetSpace p) :
    (∑ i : ValueIndex, divisionCoefficient p ⟨i.val,valueIndex_lt i⟩ x •
      jetMap K 60 (basisSeries p i.val)) = x := by
  have hh := congrArg (fun y : basisJetSpace p => (y : Jet K 60))
    ((basisJetBasis p).sum_repr (⟨x,hx⟩ : basisJetSpace p))
  simpa only [Submodule.coe_sum, Submodule.coe_smul, ← Basis.coord_apply,
    basisJetBasis_coord, LinearMap.comp_apply, Submodule.subtype_apply, basisJetBasis_coe] using hh

/-- Selected nonconstant, non-generator basis values are the 21 decomposable
basis monomials. -/
def decomposableValues : Finset ℕ := valuesBelowConductor.filter fun n =>
  n ≠ 0 ∧ n ∉ Finset.univ.image generatorValue

abbrev DecomposableIndex := {n : ℕ // n ∈ decomposableValues}

theorem decomposableValues_card : Fintype.card DecomposableIndex = 21 := by decide

def decomposableJetSpace (p : NormalCoordinate → K) : Submodule K (Jet K 60) :=
  Submodule.span K (Set.range fun i : DecomposableIndex => jetMap K 60 (basisSeries p i.val))

theorem decomposableJetSpace_finrank (p : NormalCoordinate → K) :
    Module.finrank K (decomposableJetSpace p) = 21 := by
  have hli : LinearIndependent K (fun i : DecomposableIndex => jetMap K 60 (basisSeries p i.val)) :=
    (basisJets_linearIndependent p).comp
    (fun i : DecomposableIndex => (⟨i.val,(Finset.mem_filter.mp i.property).1⟩ : ValueIndex))
    (by intro i j hij; exact Subtype.ext (congrArg (fun k : ValueIndex => k.val) hij))
  rw [decomposableJetSpace, finrank_span_eq_card hli]
  exact decomposableValues_card

theorem decomposable_basis_degree (n : ℕ) (hn : n ∈ decomposableValues) :
    2 ≤ monomialDegree (basisExponent n) := by
  have hall : ∀ n ∈ decomposableValues, 2 ≤ monomialDegree (basisExponent n) := by decide
  exact hall n hn

theorem decomposableJetSpace_le_square (p : NormalCoordinate → K) :
    decomposableJetSpace p ≤ monomialDegreeSpace p 2 := by
  apply Submodule.span_le.mpr
  rintro x ⟨i,rfl⟩
  exact jetMonomial_mem_degreeSpace p 2 (basisExponent i.val)
    (decomposable_basis_degree i.val i.property)

theorem linearTerms_basis (p : NormalCoordinate → K) (n : ℕ)
    (hn : n ∈ valuesBelowConductor) (i : Fin 5) :
    linearTerms p (jetMap K 60 (basisSeries p n)) i = if generatorValue i = n then 1 else 0 :=
  divisionCoefficient_basis p _ n hn

theorem decomposableJetSpace_le_ker (p : NormalCoordinate → K) :
    decomposableJetSpace p ≤ LinearMap.ker (linearTerms p) := by
  classical
  apply Submodule.span_le.mpr
  rintro x ⟨n,rfl⟩
  apply LinearMap.mem_ker.mpr
  funext i
  rw [linearTerms_basis p n.val (Finset.mem_filter.mp n.property).1]
  apply ite_eq_right
  intro hi
  have hn := (Finset.mem_filter.mp n.property).2.2
  apply hn
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,hi⟩

theorem degreeSpace_antitone (p : NormalCoordinate → K) {d e : ℕ} (hde : d ≤ e) :
    monomialDegreeSpace p e ≤ monomialDegreeSpace p d := by
  apply Submodule.span_le.mpr
  rintro x ⟨a,ha,rfl⟩
  exact jetMonomial_mem_degreeSpace p d a (hde.trans ha.2)

theorem divisionCoefficient_zero (p : NormalCoordinate → K) (x : Jet K 60) :
    divisionCoefficient p 0 x = jetAugmentation x := by
  obtain ⟨f,rfl⟩ := jetMap_surjective 60 x
  rfl

/-- The kernel of the five linear components on the actual maximal ideal is
exactly the span of the 21 selected decomposable basis monomials. -/
theorem degreeSpace_one_inf_ker (p : ParameterSpace (K := K)) :
    monomialDegreeSpace p.val 1 ⊓ LinearMap.ker (linearTerms p.val) = decomposableJetSpace p.val := by
  classical
  apply le_antisymm
  · intro x hx
    have hmem := (mem_degreeSpace_one_iff p.val x).mp hx.1
    have hxV : x ∈ basisJetSpace p.val := by
      rw [← parameterSpace_eq_basisJetSpace p]
      exact hmem.1
    rw [← basisJetExpansion p.val x hxV]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : i.val ∈ decomposableValues
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i.val,hi⟩,rfl⟩)
    · have hc : divisionCoefficient p.val ⟨i.val,valueIndex_lt i⟩ x = 0 := by
        by_cases hz : i.val = 0
        · have heq : (⟨i.val,valueIndex_lt i⟩ : Fin 60) = 0 := Fin.ext hz
          rw [heq, divisionCoefficient_zero]
          exact hmem.2
        · have hgen : i.val ∈ Finset.univ.image generatorValue := by
            by_contra hh
            exact hi (Finset.mem_filter.mpr ⟨i.property,hz,hh⟩)
          obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hgen
          have heq : (⟨i.val,valueIndex_lt i⟩ : Fin 60) =
              ⟨generatorValue j,generatorValue_lt j⟩ := Fin.ext hj.symm
          rw [heq]
          exact congrFun (LinearMap.mem_ker.mp hx.2) j
      rw [hc,zero_smul]
      exact Submodule.zero_mem _
  · exact le_inf ((decomposableJetSpace_le_square p.val).trans
      (degreeSpace_antitone p.val (by omega))) (decomposableJetSpace_le_ker p.val)

theorem degreeSpace_two_inf_ker (p : ParameterSpace (K := K)) :
    monomialDegreeSpace p.val 2 ⊓ LinearMap.ker (linearTerms p.val) = decomposableJetSpace p.val := by
  apply le_antisymm
  · exact (inf_le_inf (degreeSpace_antitone p.val (by omega)) le_rfl).trans
      (degreeSpace_one_inf_ker p).le
  · exact le_inf (decomposableJetSpace_le_square p.val) (decomposableJetSpace_le_ker p.val)

end EmbeddingDimensionStrata
