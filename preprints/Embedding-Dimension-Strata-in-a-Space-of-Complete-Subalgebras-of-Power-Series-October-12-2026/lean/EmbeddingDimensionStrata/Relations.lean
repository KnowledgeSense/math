import EmbeddingDimensionStrata.JetBasis
import Mathlib.Algebra.Algebra.Bilinear

/-! # The two actual binomial relations and the five defining equations -/
set_option maxRecDepth 4096
noncomputable section
namespace EmbeddingDimensionStrata
section Universal
variable {A : Type*} [CommRing A]

def relationF (p : NormalCoordinate → A) : PowerSeries A :=
  normalSeries p 1 ^ 4 - normalSeries p 0 * normalSeries p 2

def relationG (p : NormalCoordinate → A) : PowerSeries A :=
  normalSeries p 1 ^ 2 * normalSeries p 2 - normalSeries p 0 * normalSeries p 3

theorem MonicAt.sub_low {f g : PowerSeries A} {m : ℕ}
    (hf : MonicAt f m) (hg : MonicAt g m) :
    ∀ i < m+1, PowerSeries.coeff i (f-g) = 0 := by
  intro i hi
  by_cases him : i < m
  · simp [hf.1 i him, hg.1 i him]
  · have heq : i = m := by omega
    subst i
    simp [hf.2, hg.2]

theorem relationF_low (p : NormalCoordinate → A) :
    ∀ i < 45, PowerSeries.coeff i (relationF p) = 0 :=
  ((monicAt_normalSeries p 1).pow 4).sub_low
    ((monicAt_normalSeries p 0).mul (monicAt_normalSeries p 2))

theorem relationG_low (p : NormalCoordinate → A) :
    ∀ i < 57, PowerSeries.coeff i (relationG p) = 0 :=
  (((monicAt_normalSeries p 1).pow 2).mul (monicAt_normalSeries p 2)).sub_low
    ((monicAt_normalSeries p 0).mul (monicAt_normalSeries p 3))

/-- The equations in the paper's triangular order: r47, r48, q59, r49, r59.
They are defined by actual universal ring operations in the reduction. -/
def definingEquation (p : NormalCoordinate → A) (i : Fin 5) : A :=
  match i.val with
  | 0 => PowerSeries.coeff 47 (reduceSeries p 60 (relationF p))
  | 1 => PowerSeries.coeff 48 (reduceSeries p 60 (relationF p))
  | 2 => PowerSeries.coeff 59 (reduceSeries p 60 (relationG p))
  | 3 => PowerSeries.coeff 49 (reduceSeries p 60 (relationF p))
  | _ => PowerSeries.coeff 59 (reduceSeries p 60 (relationF p))

end Universal
section Field
variable {K : Type*} [Field K]

theorem equations_iff_remainders (p : NormalCoordinate → K) :
    (∀ i : Fin 5, definingEquation p i = 0) ↔
      jetRemainder p (jetMap K 60 (relationF p)) = 0 ∧
      jetRemainder p (jetMap K 60 (relationG p)) = 0 := by
  constructor
  · intro he
    constructor
    · apply (jetMap_eq_zero_iff 60 _).mpr
      intro n hn
      by_cases hlow : n < 45
      · exact reduceSeries_low_zero p _ 45 60 (relationF_low p) n hlow
      · by_cases hg : n ∈ valuesBelowConductor
        · exact coeff_reduceSeries_eq_zero p _ 60 hn hg
        · have hall : ∀ k : Fin 60, 45 ≤ k.val → k.val ∉ valuesBelowConductor →
              k.val = 47 ∨ k.val = 48 ∨ k.val = 49 ∨ k.val = 59 := by decide
          have hcases : n = 47 ∨ n = 48 ∨ n = 49 ∨ n = 59 :=
            hall ⟨n,hn⟩ (by change 45 ≤ n; omega) hg
          rcases hcases with rfl | rfl | rfl | rfl
          · exact he 0
          · exact he 1
          · exact he 3
          · exact he 4
    · apply (jetMap_eq_zero_iff 60 _).mpr
      intro n hn
      by_cases hlow : n < 57
      · exact reduceSeries_low_zero p _ 57 60 (relationG_low p) n hlow
      · by_cases hg : n ∈ valuesBelowConductor
        · exact coeff_reduceSeries_eq_zero p _ 60 hn hg
        · have hall : ∀ k : Fin 60, 57 ≤ k.val → k.val ∉ valuesBelowConductor →
              k.val = 59 := by decide
          have heq : n = 59 := hall ⟨n,hn⟩ (by change 57 ≤ n; omega) hg
          subst n
          exact he 2
  · rintro ⟨hf,hg⟩ i
    have hF := (jetMap_eq_zero_iff 60 _).mp hf
    have hG := (jetMap_eq_zero_iff 60 _).mp hg
    fin_cases i
    · exact hF 47 (by omega)
    · exact hF 48 (by omega)
    · exact hG 59 (by omega)
    · exact hF 49 (by omega)
    · exact hF 59 (by omega)

theorem relationF_mem (p : NormalCoordinate → K) :
    jetMap K 60 (relationF p) ∈ parameterJetAlgebra p := by
  simp only [relationF, map_sub, map_pow, map_mul]
  apply Subalgebra.sub_mem
  · exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self 1)) 4
  · exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Set.mem_range_self 0))
      (Algebra.subset_adjoin (Set.mem_range_self 2))

theorem relationG_mem (p : NormalCoordinate → K) :
    jetMap K 60 (relationG p) ∈ parameterJetAlgebra p := by
  simp only [relationG, map_sub, map_pow, map_mul]
  apply Subalgebra.sub_mem
  · exact Subalgebra.mul_mem _
      (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self 1)) 2)
      (Algebra.subset_adjoin (Set.mem_range_self 2))
  · exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Set.mem_range_self 0))
      (Algebra.subset_adjoin (Set.mem_range_self 3))

/-- Necessity of the five equations is proved from the genuine semigroup
condition, not included in the definition of the parameter space. -/
theorem parameterSpace_definingEquations (p : ParameterSpace (K := K)) :
    ∀ i : Fin 5, definingEquation p.val i = 0 := by
  apply (equations_iff_remainders p.val).mpr
  exact ⟨parameterSpace_remainder_zero p _ (relationF_mem p.val),
    parameterSpace_remainder_zero p _ (relationG_mem p.val)⟩

theorem relationF_mem_tail_of_remainder_zero (p : NormalCoordinate → K)
    (hf : jetRemainder p (jetMap K 60 (relationF p)) = 0) :
    jetMap K 60 (relationF p) ∈ basisJetTailSpace p 45 := by
  have hh := jet_sub_reduceSeries_mem_tail p _ 45 60 (relationF_low p)
  rw [map_sub, ← jetRemainder_jetMap, hf, sub_zero] at hh
  exact hh

theorem mul_basisJet_vanish (p : NormalCoordinate → K) (i : Fin 5)
    (k : ℕ) (hk : k ∈ valuesBelowConductor) (hki : 60 ≤ generatorValue i + k) :
    jetMap K 60 (normalSeries p i) * jetMap K 60 (basisSeries p k) = 0 := by
  rw [← map_mul]
  apply (jetMap_eq_zero_iff 60 _).mpr
  intro n hn
  exact ((monicAt_normalSeries p i).mul (basisSeries_monic p k hk)).1 n (by omega)

theorem mul_X_basis_tail (p : NormalCoordinate → K) (k : ℕ)
    (hk : k ∈ valuesBelowConductor) (hk45 : 45 ≤ k) :
    jetMap K 60 (normalSeries p 0) * jetMap K 60 (basisSeries p k) ∈ basisJetSpace p := by
  by_cases hk50 : 50 ≤ k
  · rw [mul_basisJet_vanish p 0 k hk (by change 60 ≤ 10+k; omega)]
    exact Submodule.zero_mem _
  · have hall : ∀ n ∈ valuesBelowConductor, 45 ≤ n → n < 50 → n = 45 ∨ n = 46 := by decide
    rcases hall k hk hk45 (by omega) with rfl | rfl
    · convert basisJet_mem p 55 (by decide) using 1
      simp only [basisSeries, basisExponent, seriesMonomial, pow_zero, pow_one, one_mul, mul_one, map_mul]
      ring
    · convert basisJet_mem p 56 (by decide) using 1
      simp [basisSeries, basisExponent, seriesMonomial, map_mul]

theorem mul_H_basis_tail (p : NormalCoordinate → K)
    (hG : jetMap K 60 (relationG p) ∈ basisJetSpace p)
    (k : ℕ) (hk : k ∈ valuesBelowConductor) (hk45 : 45 ≤ k) :
    jetMap K 60 (normalSeries p 1) * jetMap K 60 (basisSeries p k) ∈ basisJetSpace p := by
  by_cases hk50 : 50 ≤ k
  · rw [mul_basisJet_vanish p 1 k hk (by change 60 ≤ 11+k; omega)]
    exact Submodule.zero_mem _
  · have hall : ∀ n ∈ valuesBelowConductor, 45 ≤ n → n < 50 → n = 45 ∨ n = 46 := by decide
    rcases hall k hk hk45 (by omega) with rfl | rfl
    · have hh := Submodule.add_mem (basisJetSpace p) (basisJet_mem p 56 (by decide)) hG
      convert hh using 1
      simp only [relationG, basisSeries, basisExponent, seriesMonomial, pow_zero, pow_one,
        one_mul, mul_one, map_sub, map_mul, map_pow]
      ring
    · convert basisJet_mem p 57 (by decide) using 1
      simp [basisSeries, basisExponent, seriesMonomial, map_mul]

theorem mul_X_tail_mem (p : NormalCoordinate → K) (x : Jet K 60)
    (hx : x ∈ basisJetTailSpace p 45) :
    jetMap K 60 (normalSeries p 0) * x ∈ basisJetSpace p := by
  have hle : basisJetTailSpace p 45 ≤ (basisJetSpace p).comap
      (LinearMap.mulLeft K (jetMap K 60 (normalSeries p 0))) := by
    apply Submodule.span_le.mpr
    rintro y ⟨k,rfl⟩
    exact mul_X_basis_tail p k.val k.property.1 k.property.2
  exact hle hx

theorem mul_H_tail_mem (p : NormalCoordinate → K)
    (hG : jetMap K 60 (relationG p) ∈ basisJetSpace p)
    (x : Jet K 60) (hx : x ∈ basisJetTailSpace p 45) :
    jetMap K 60 (normalSeries p 1) * x ∈ basisJetSpace p := by
  have hle : basisJetTailSpace p 45 ≤ (basisJetSpace p).comap
      (LinearMap.mulLeft K (jetMap K 60 (normalSeries p 1))) := by
    apply Submodule.span_le.mpr
    rintro y ⟨k,rfl⟩
    exact mul_H_basis_tail p hG k.val k.property.1 k.property.2
  exact hle hx

/-- The two reduced binomials generate all obstructions, including the two
higher coincidences of weights 54 and 55. -/
theorem remainders_zero_implies_basis (p : NormalCoordinate → K)
    (hF : jetRemainder p (jetMap K 60 (relationF p)) = 0)
    (hG : jetRemainder p (jetMap K 60 (relationG p)) = 0) :
    (parameterJetAlgebra p).toSubmodule = basisJetSpace p := by
  have hFm := (jetRemainder_eq_zero_iff p _).mp hF
  have hGm := (jetRemainder_eq_zero_iff p _).mp hG
  have hFt := relationF_mem_tail_of_remainder_zero p hF
  have hXF := mul_X_tail_mem p _ hFt
  have hHF := mul_H_tail_mem p hGm _ hFt
  apply le_antisymm
  · rw [parameterJetAlgebra_span]
    apply Submodule.span_le.mpr
    rintro x ⟨a,ha,rfl⟩
    change jetMonomial p a ∈ basisJetSpace p
    rcases smallExponents_partition a ha with heq | rfl | rfl | rfl | rfl
    · have hw : monomialWeight a ∈ valuesBelowConductor := by
        apply (gamma_below_conductor ((mem_smallExponents_iff a).mp ha)).mp
        exact ⟨a.1,a.2.1,a.2.2.1,a.2.2.2.1,a.2.2.2.2,rfl⟩
      convert basisJet_mem p (monomialWeight a) hw using 1
      exact congrArg (jetMonomial p) heq
    · have hh := Submodule.add_mem (basisJetSpace p) (basisJet_mem p 44 (by decide)) hFm
      convert hh using 1
      simp only [jetMonomial, relationF, basisSeries, basisExponent, seriesMonomial,
        pow_zero, pow_one, one_mul, mul_one, map_sub, map_mul, map_pow]
      ring
    · have hh := Submodule.add_mem (basisJetSpace p) (basisJet_mem p 54 (by decide)) hXF
      convert hh using 1
      simp only [jetMonomial, relationF, basisSeries, basisExponent, seriesMonomial,
        pow_zero, pow_one, mul_one, map_sub, map_mul, map_pow]
      ring
    · have hh := Submodule.add_mem (basisJetSpace p) (basisJet_mem p 55 (by decide)) hHF
      convert hh using 1
      simp only [jetMonomial, relationF, basisSeries, basisExponent, seriesMonomial,
        pow_zero, pow_one, one_mul, mul_one, map_sub, map_mul, map_pow]
      ring
    · have hh := Submodule.add_mem (basisJetSpace p) (basisJet_mem p 56 (by decide)) hGm
      convert hh using 1
      simp only [jetMonomial, relationG, basisSeries, basisExponent, seriesMonomial,
        pow_zero, pow_one, one_mul, mul_one, map_sub, map_mul, map_pow]
      ring
  · exact basisJetSpace_le p

/-- The exact five-equation criterion for the original semantic locus. -/
theorem parameter_condition_iff_equations (p : NormalCoordinate → K) :
    (∀ n, JetHasValue (parameterJetAlgebra p) n ↔ Gamma n) ↔
      ∀ i : Fin 5, definingEquation p i = 0 := by
  constructor
  · intro hp
    exact parameterSpace_definingEquations ⟨p,hp⟩
  · intro he
    obtain ⟨hF,hG⟩ := (equations_iff_remainders p).mp he
    exact (parameter_condition_iff_basis p).mpr (remainders_zero_implies_basis p hF hG)

end Field
end EmbeddingDimensionStrata
