import EmbeddingDimensionStrata.Monomials
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Polynomial elimination in the actual power-series and jet algebras -/
set_option maxRecDepth 4096

noncomputable section
namespace EmbeddingDimensionStrata
section Universal
variable {A : Type*} [CommRing A]

/-- One division step subtracts the current coefficient times the chosen monic
monomial. No division by a coefficient occurs. -/
def reductionStep (p : NormalCoordinate → A) (n : ℕ) :
    PowerSeries A →ₗ[A] PowerSeries A :=
  if n ∈ valuesBelowConductor then
    LinearMap.id - (PowerSeries.coeff n).smulRight (basisSeries p n)
  else LinearMap.id

/-- Eliminate semigroup coefficients in increasing order. The same operation
is defined over the universal polynomial ring and after any specialization. -/
def reduceSeries (p : NormalCoordinate → A) : ℕ → PowerSeries A →ₗ[A] PowerSeries A
  | 0 => LinearMap.id
  | n+1 => (reductionStep p n).comp (reduceSeries p n)

@[simp]
theorem reduceSeries_zero (p : NormalCoordinate → A) (f : PowerSeries A) :
    reduceSeries p 0 f = f := rfl

theorem reduceSeries_succ (p : NormalCoordinate → A) (f : PowerSeries A) (n : ℕ) :
    reduceSeries p (n+1) f =
      if n ∈ valuesBelowConductor then
        reduceSeries p n f - PowerSeries.coeff n (reduceSeries p n f) • basisSeries p n
      else reduceSeries p n f := by
  by_cases hn : n ∈ valuesBelowConductor <;> simp [reduceSeries, reductionStep, hn]

/-- A division step does not change any coefficient strictly below its pivot. -/
theorem coeff_reductionStep_of_lt (p : NormalCoordinate → A) (f : PowerSeries A)
    {i n : ℕ} (hi : i < n) :
    PowerSeries.coeff i (reductionStep p n f) = PowerSeries.coeff i f := by
  by_cases hn : n ∈ valuesBelowConductor
  · simp [reductionStep, hn, (basisSeries_monic p n hn).1 i hi]
  · simp [reductionStep, hn]

/-- Each processed semigroup coefficient vanishes, including after all later
steps. -/
theorem coeff_reduceSeries_eq_zero (p : NormalCoordinate → A) (f : PowerSeries A)
    (N : ℕ) {i : ℕ} (hi : i < N) (hig : i ∈ valuesBelowConductor) :
    PowerSeries.coeff i (reduceSeries p N f) = 0 := by
  induction N with
  | zero => omega
  | succ n ih =>
    by_cases hin : i < n
    · change PowerSeries.coeff i (reductionStep p n (reduceSeries p n f)) = 0
      rw [coeff_reductionStep_of_lt p _ hin]
      exact ih hin
    · have heq : i = n := by omega
      subst i
      rw [reduceSeries_succ, ite_eq_left hig]
      simp [(basisSeries_monic p n hig).2]

/-- If no coefficient can yet be eliminated, the division leaves the series
itself unchanged. -/
theorem reduceSeries_eq_self_of_low_zero (p : NormalCoordinate → A)
    (f : PowerSeries A) (N : ℕ)
    (hf : ∀ i < N, PowerSeries.coeff i f = 0) : reduceSeries p N f = f := by
  induction N with
  | zero => rfl
  | succ n ih =>
    rw [reduceSeries_succ, ih (fun i hi => hf i (by omega))]
    split_ifs <;> simp [hf n (by omega)]

/-- Once a series has become zero it remains zero through subsequent steps. -/
theorem reduceSeries_eq_zero_of_le (p : NormalCoordinate → A) (f : PowerSeries A)
    {m n : ℕ} (hmn : m ≤ n) (hm : reduceSeries p m f = 0) :
    reduceSeries p n f = 0 := by
  induction n, hmn using Nat.le_induction with
  | base => exact hm
  | succ n hmn ih =>
    change reductionStep p n (reduceSeries p n f) = 0
    rw [ih, map_zero]

/-- Division annihilates every selected monomial after its pivot. -/
theorem reduceSeries_basisSeries (p : NormalCoordinate → A) (k N : ℕ)
    (hk : k ∈ valuesBelowConductor) (hkN : k < N) :
    reduceSeries p N (basisSeries p k) = 0 := by
  apply reduceSeries_eq_zero_of_le p _ (by omega : k+1 ≤ N)
  rw [reduceSeries_succ, ite_eq_left hk,
    reduceSeries_eq_self_of_low_zero p _ k (basisSeries_monic p k hk).1]
  simp [(basisSeries_monic p k hk).2]

/-- Division preserves the vanishing of all coefficients below any fixed
order. -/
theorem reduceSeries_low_zero (p : NormalCoordinate → A) (f : PowerSeries A)
    (m N : ℕ) (hf : ∀ i < m, PowerSeries.coeff i f = 0) :
    ∀ i < m, PowerSeries.coeff i (reduceSeries p N f) = 0 := by
  induction N with
  | zero => exact hf
  | succ n ih =>
    intro i hi
    rw [reduceSeries_succ]
    split_ifs with hn
    · simp only [map_sub, map_smul]
      by_cases hnm : n < m
      · rw [ih n hnm, zero_smul, ih i hi, sub_self]
      · rw [(basisSeries_monic p n hn).1 i (by omega), smul_zero, sub_zero]
        exact ih i hi
    · exact ih i hi

/-- A leading coefficient at a gap survives every division step. -/
theorem reduceSeries_gap_coeff (p : NormalCoordinate → A) (f : PowerSeries A)
    (m N : ℕ) (hm : m ∉ valuesBelowConductor)
    (hf : ∀ i < m, PowerSeries.coeff i f = 0) :
    PowerSeries.coeff m (reduceSeries p N f) = PowerSeries.coeff m f := by
  induction N with
  | zero => rfl
  | succ n ih =>
    rw [reduceSeries_succ]
    split_ifs with hn
    · simp only [map_sub, map_smul]
      by_cases hnm : n < m
      · rw [reduceSeries_low_zero p f m n hf n hnm, zero_smul, sub_zero, ih]
      · have hne : n ≠ m := by intro h; exact hm (h ▸ hn)
        rw [(basisSeries_monic p n hn).1 m (by omega), smul_zero, sub_zero, ih]
    · exact ih

end Universal
section Field
variable {K : Type*} [Field K]

/-- The subspace generated by the 27 selected actual jet monomials. -/
def basisJetSpace (p : NormalCoordinate → K) : Submodule K (Jet K 60) :=
  Submodule.span K (Set.range fun k : {n // n ∈ valuesBelowConductor} =>
    jetMap K 60 (basisSeries p k.val))

theorem basisJet_mem (p : NormalCoordinate → K) (k : ℕ)
    (hk : k ∈ valuesBelowConductor) : jetMap K 60 (basisSeries p k) ∈ basisJetSpace p :=
  Submodule.subset_span (Set.mem_range.mpr ⟨⟨k,hk⟩,rfl⟩)

theorem basisJetSpace_le (p : NormalCoordinate → K) :
    basisJetSpace p ≤ (parameterJetAlgebra p).toSubmodule := by
  apply Submodule.span_le.mpr
  rintro x ⟨k,rfl⟩
  exact jetMonomial_mem p _

/-- The part removed by division is a linear combination of the actual basis
monomials. -/
theorem jet_sub_reduceSeries_mem (p : NormalCoordinate → K) (f : PowerSeries K)
    (N : ℕ) : jetMap K 60 (f - reduceSeries p N f) ∈ basisJetSpace p := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [reduceSeries_succ]
    split_ifs with hn
    · have heq : f - (reduceSeries p n f -
          PowerSeries.coeff n (reduceSeries p n f) • basisSeries p n) =
        (f - reduceSeries p n f) +
          PowerSeries.coeff n (reduceSeries p n f) • basisSeries p n := by abel
      rw [heq, map_add, map_smul]
      exact Submodule.add_mem _ ih (Submodule.smul_mem _ _ (basisJet_mem p n hn))
    · exact ih

theorem jet_reduceSeries_eq (p : NormalCoordinate → K) (f g : PowerSeries K)
    (N : ℕ) (hN : N ≤ 60) (hfg : jetMap K 60 f = jetMap K 60 g) :
    jetMap K 60 (reduceSeries p N f) = jetMap K 60 (reduceSeries p N g) := by
  induction N with
  | zero => exact hfg
  | succ n ih =>
    have ih' := ih (by omega)
    rw [reduceSeries_succ, reduceSeries_succ]
    split_ifs with hn
    · rw [map_sub, map_sub, map_smul, map_smul, ih',
        (jetMap_eq_iff 60 _ _).mp ih' n (by omega)]
    · exact ih'

/-- Division descends to a linear endomorphism of the semantic quotient. -/
def jetRemainder (p : NormalCoordinate → K) : Jet K 60 →ₗ[K] Jet K 60 where
  toFun := Quotient.lift (fun f : PowerSeries K => jetMap K 60 (reduceSeries p 60 f)) (by
    intro f g hfg
    exact jet_reduceSeries_eq p f g 60 le_rfl (Quotient.sound hfg))
  map_add' := by
    intro x y
    obtain ⟨f,rfl⟩ := jetMap_surjective 60 x
    obtain ⟨g,rfl⟩ := jetMap_surjective 60 y
    change jetMap K 60 (reduceSeries p 60 (f+g)) = _
    rw [map_add, map_add]
    rfl
  map_smul' := by
    intro a x
    obtain ⟨f,rfl⟩ := jetMap_surjective 60 x
    change jetMap K 60 (reduceSeries p 60 (a • f)) = _
    rw [map_smul, map_smul]
    rfl

@[simp]
theorem jetRemainder_jetMap (p : NormalCoordinate → K) (f : PowerSeries K) :
    jetRemainder p (jetMap K 60 f) = jetMap K 60 (reduceSeries p 60 f) := rfl

theorem jetRemainder_basis (p : NormalCoordinate → K) (k : ℕ)
    (hk : k ∈ valuesBelowConductor) :
    jetRemainder p (jetMap K 60 (basisSeries p k)) = 0 := by
  have hk60 : k < 60 := by
    have hall : ∀ n ∈ valuesBelowConductor, n < 60 := by decide
    exact hall k hk
  rw [jetRemainder_jetMap, reduceSeries_basisSeries p k 60 hk hk60, map_zero]

/-- The remainder vanishes exactly on the selected 27-monomial subspace. -/
theorem jetRemainder_eq_zero_iff (p : NormalCoordinate → K) (x : Jet K 60) :
    jetRemainder p x = 0 ↔ x ∈ basisJetSpace p := by
  constructor
  · intro hx
    obtain ⟨f,rfl⟩ := jetMap_surjective 60 x
    have hm := jet_sub_reduceSeries_mem p f 60
    rw [map_sub, ← jetRemainder_jetMap, hx, sub_zero] at hm
    exact hm
  · intro hx
    change x ∈ LinearMap.ker (jetRemainder p)
    have hle : basisJetSpace p ≤ LinearMap.ker (jetRemainder p) := by
      apply Submodule.span_le.mpr
      rintro x ⟨k,rfl⟩
      exact jetRemainder_basis p k.val k.property
    exact hle hx

/-- Every genuine parameter point has its whole algebra in the basis subspace;
the proof excludes nonzero gap-supported remainders by the actual value set. -/
theorem parameterSpace_remainder_zero (p : ParameterSpace (K := K))
    (x : Jet K 60) (hx : x ∈ parameterJetAlgebra p.val) : jetRemainder p.val x = 0 := by
  classical
  obtain ⟨f,rfl⟩ := jetMap_surjective 60 x
  by_contra hz
  have hnot : ¬ ∀ i < 60, PowerSeries.coeff i (reduceSeries p.val 60 f) = 0 := by
    intro hh
    exact hz ((jetMap_eq_zero_iff 60 _).mpr hh)
  push Not at hnot
  let n := Nat.find hnot
  have hn := Nat.find_spec hnot
  have horder : HasOrder (reduceSeries p.val 60 f) n := by
    refine ⟨?_,hn.2⟩
    intro i hi
    have hh := Nat.find_min hnot hi
    push Not at hh
    exact hh (by omega)
  have hmem : jetMap K 60 (reduceSeries p.val 60 f) ∈ parameterJetAlgebra p.val := by
    have hh := basisJetSpace_le p.val (jet_sub_reduceSeries_mem p.val f 60)
    rw [map_sub] at hh
    have hs := (parameterJetAlgebra p.val).sub_mem hx hh
    simpa only [sub_sub_cancel] using hs
  have hgamma : Gamma n :=
    (p.property n).mp (Or.inr ⟨hn.1,reduceSeries p.val 60 f,hmem,horder⟩)
  have hg := (gamma_below_conductor hn.1).mp hgamma
  exact horder.2 (coeff_reduceSeries_eq_zero p.val f 60 hn.1 hg)

/-- At every point of the genuine normal-form locus, the selected monomials
span the actual algebra, with no coefficient-table proxy. -/
theorem parameterSpace_eq_basisJetSpace (p : ParameterSpace (K := K)) :
    (parameterJetAlgebra p.val).toSubmodule = basisJetSpace p.val := by
  apply le_antisymm
  · intro x hx
    exact (jetRemainder_eq_zero_iff p.val x).mp (parameterSpace_remainder_zero p x hx)
  · exact basisJetSpace_le p.val

theorem basisJetSpace_no_gap (p : NormalCoordinate → K) (f : PowerSeries K)
    {n : ℕ} (hn : n < 60) (hf : jetMap K 60 f ∈ basisJetSpace p)
    (hord : HasOrder f n) : n ∈ valuesBelowConductor := by
  by_contra hg
  have hz := (jetRemainder_eq_zero_iff p (jetMap K 60 f)).mpr hf
  have hcoeff := (jetMap_eq_zero_iff 60 _).mp hz n hn
  rw [reduceSeries_gap_coeff p f n 60 hg hord.1] at hcoeff
  exact hord.2 hcoeff

/-- Equality to the selected-monomial subspace is equivalent to the full
semantic value condition defining the parameter locus. -/
theorem parameter_condition_iff_basis (p : NormalCoordinate → K) :
    (∀ n, JetHasValue (parameterJetAlgebra p) n ↔ Gamma n) ↔
      (parameterJetAlgebra p).toSubmodule = basisJetSpace p := by
  constructor
  · intro hp
    exact parameterSpace_eq_basisJetSpace ⟨p,hp⟩
  · intro hp n
    by_cases hn : n < 60
    · constructor
      · rintro (ht | ⟨_,f,hf,hord⟩)
        · omega
        · apply (gamma_below_conductor hn).mpr
          apply basisJetSpace_no_gap p f hn _ hord
          change jetMap K 60 f ∈ (parameterJetAlgebra p).toSubmodule at hf
          rwa [hp] at hf
      · intro hg
        have hmem := (gamma_below_conductor hn).mp hg
        refine Or.inr ⟨hn,basisSeries p n,jetMonomial_mem p _,?_,?_⟩
        · exact (basisSeries_monic p n hmem).1
        · rw [(basisSeries_monic p n hmem).2]
          exact one_ne_zero
    · exact ⟨fun _ => gamma_of_ge_sixty n (by omega), fun _ => Or.inl (by omega)⟩

/-- The span of chosen monomials whose pivots are at least `m`. -/
def basisJetTailSpace (p : NormalCoordinate → K) (m : ℕ) : Submodule K (Jet K 60) :=
  Submodule.span K (Set.range fun k : {n : ℕ // n ∈ valuesBelowConductor ∧ m ≤ n} =>
    jetMap K 60 (basisSeries p k.val))

theorem jet_sub_reduceSeries_mem_tail (p : NormalCoordinate → K) (f : PowerSeries K)
    (m N : ℕ) (hf : ∀ i < m, PowerSeries.coeff i f = 0) :
    jetMap K 60 (f - reduceSeries p N f) ∈ basisJetTailSpace p m := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [reduceSeries_succ]
    split_ifs with hn
    · by_cases hnm : n < m
      · rw [reduceSeries_low_zero p f m n hf n hnm, zero_smul, sub_zero]
        exact ih
      · have heq : f - (reduceSeries p n f -
            PowerSeries.coeff n (reduceSeries p n f) • basisSeries p n) =
          (f - reduceSeries p n f) +
            PowerSeries.coeff n (reduceSeries p n f) • basisSeries p n := by abel
        rw [heq, map_add, map_smul]
        apply Submodule.add_mem _ ih
        apply Submodule.smul_mem
        exact Submodule.subset_span (Set.mem_range.mpr ⟨⟨n,hn,by omega⟩,rfl⟩)
    · exact ih

end Field
end EmbeddingDimensionStrata
