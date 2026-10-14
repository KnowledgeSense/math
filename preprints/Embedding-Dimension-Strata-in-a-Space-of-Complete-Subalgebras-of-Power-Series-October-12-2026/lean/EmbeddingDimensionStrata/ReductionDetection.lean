import EmbeddingDimensionStrata.PartialReduction

/-! # No fixed generator-polynomial detects the actual four-generator stratum -/
set_option maxRecDepth 4096
noncomputable section
namespace EmbeddingDimensionStrata

section Rings
variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]

/-- Substitute the actual five normal series into an arbitrary polynomial. -/
def generatorEvaluation (θ : K →+* A) (p : NormalCoordinate → A)
    (f : MvPolynomial (Fin 5) K) : PowerSeries A :=
  MvPolynomial.eval₂ (PowerSeries.C.comp θ) (normalSeries p) f

theorem map_generatorEvaluation (θ : K →+* A) (φ : A →+* B)
    (p : NormalCoordinate → A) (f : MvPolynomial (Fin 5) K) :
    PowerSeries.map φ (generatorEvaluation θ p f) =
      generatorEvaluation (φ.comp θ) (fun j => φ (p j)) f := by
  rw [generatorEvaluation, MvPolynomial.hom_eval₂]
  have hC : (PowerSeries.map φ).comp (PowerSeries.C.comp θ) = PowerSeries.C.comp (φ.comp θ) := by
    apply RingHom.ext
    intro a
    exact PowerSeries.map_C φ (θ a)
  rw [hC]
  have hN : (fun i => PowerSeries.map φ (normalSeries p i)) = normalSeries (fun j => φ (p j)) := by
    funext i
    exact map_normalSeries φ p i
  rw [hN]
  rfl

theorem generatorEvaluation_constant (θ : K →+* A) (p : NormalCoordinate → A)
    (f : MvPolynomial (Fin 5) K) :
    PowerSeries.coeff 0 (generatorEvaluation θ p f) = θ (MvPolynomial.eval 0 f) := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [generatorEvaluation, MvPolynomial.hom_eval₂]
  have hC : PowerSeries.constantCoeff.comp (PowerSeries.C.comp θ) = θ := by ext a; simp
  have hN : (fun i => PowerSeries.constantCoeff (normalSeries p i)) = 0 := by
    funext i
    have hp : ∀ i : Fin 5, 0 < generatorValue i := by decide
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply, Pi.zero_apply] using
      (monicAt_normalSeries p i).1 0 (hp i)
  rw [hC,hN]
  have hzero : (θ ∘ (0 : Fin 5 → K)) = (0 : Fin 5 → A) := by
    funext i
    exact θ.map_zero
  have hh := MvPolynomial.eval₂_comp θ (0 : Fin 5 → K) f
  rw [hzero] at hh
  exact hh.symm

/-- The coefficient at order58 of the universal partial reduction, an
ordinary polynomial in all original normal-form coefficients. -/
def detectionPolynomial (f : MvPolynomial (Fin 5) K) : MvPolynomial NormalCoordinate K :=
  PowerSeries.coeff 58 (partialReduceSeries MvPolynomial.X 60
    (generatorEvaluation MvPolynomial.C MvPolynomial.X f))

theorem eval_detectionPolynomial (p : NormalCoordinate → K) (f : MvPolynomial (Fin 5) K) :
    MvPolynomial.aeval p (detectionPolynomial f) =
      PowerSeries.coeff 58 (partialReduceSeries p 60 (generatorEvaluation (RingHom.id K) p f)) := by
  let φ : MvPolynomial NormalCoordinate K →+* K := (MvPolynomial.aeval p).toRingHom
  have hX : (fun j : NormalCoordinate => φ (MvPolynomial.X j)) = p := by
    funext j
    exact MvPolynomial.aeval_X p j
  have hC : φ.comp MvPolynomial.C = RingHom.id K := by ext a; exact MvPolynomial.aeval_C p a
  have hh := map_partialReduceSeries φ (MvPolynomial.X : NormalCoordinate → MvPolynomial NormalCoordinate K)
    (generatorEvaluation MvPolynomial.C MvPolynomial.X f)
  rw [map_generatorEvaluation, hX, hC] at hh
  exact congrArg (PowerSeries.coeff 58) hh

end Rings
section Field
variable {K : Type*} [Field K]

theorem generatorEvaluation_mem (p : NormalCoordinate → K) (f : MvPolynomial (Fin 5) K) :
    jetMap K 60 (generatorEvaluation (RingHom.id K) p f) ∈ parameterJetAlgebra p := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    change jetMap K 60 (MvPolynomial.eval₂ _ _ (MvPolynomial.C a)) ∈ _
    rw [MvPolynomial.eval₂_C]
    exact (parameterJetAlgebra p).algebraMap_mem a
  | add f g hf hg =>
    change jetMap K 60 (MvPolynomial.eval₂ _ _ (f+g)) ∈ _
    rw [MvPolynomial.eval₂_add,map_add]
    exact (parameterJetAlgebra p).add_mem hf hg
  | mul_X f i hf =>
    change jetMap K 60 (MvPolynomial.eval₂ _ _ (f * MvPolynomial.X i)) ∈ _
    rw [MvPolynomial.eval₂_mul,MvPolynomial.eval₂_X,map_mul]
    exact (parameterJetAlgebra p).mul_mem hf (Algebra.subset_adjoin (Set.mem_range_self i))

/-- For every fixed generator polynomial with zero constant term, the actual
partial-reduction order58 condition is a single polynomial principal open. -/
theorem polynomial_reduction_order58_iff (p : ParameterSpace (K := K))
    (f : MvPolynomial (Fin 5) K) (h0 : MvPolynomial.eval 0 f = 0) :
    HasOrder (partialReduceSeries p.val 60 (generatorEvaluation (RingHom.id K) p.val f)) 58 ↔
      MvPolynomial.aeval p.val (detectionPolynomial f) ≠ 0 := by
  rw [eval_detectionPolynomial]
  apply partialReduceSeries_order58_iff p _ (generatorEvaluation_mem p.val f)
  rw [generatorEvaluation_constant, h0, map_zero]

/-- A nonzero constant term is retained by the actual positive-order algorithm. -/
theorem polynomial_reduction_order_zero (p : NormalCoordinate → K)
    (f : MvPolynomial (Fin 5) K) (h0 : MvPolynomial.eval 0 f ≠ 0) :
    HasOrder (partialReduceSeries p 60 (generatorEvaluation (RingHom.id K) p f)) 0 := by
  refine ⟨by intro i hi; omega,?_⟩
  rw [partialReduceSeries_constant, generatorEvaluation_constant]
  exact h0

/-- The four-generator locus is nonempty, witnessed through the proved
polynomial parametrization rather than an assumed model point. -/
theorem generatorStratum_four_nonempty : (generatorStratum (K := K) 4).Nonempty := by
  let x : AffineCoordinate → K := fun _ => 1
  refine ⟨parameterAffineEquiv.symm x, (generatorStratum_four_coordinates _).mpr ?_⟩
  rw [Equiv.apply_symm_apply]
  exact ⟨0,one_ne_zero⟩

/-- Theorem q47(1), quantified over every fixed polynomial in the five actual
generators. Reduction is the positive-order monomial algorithm for the first
four generator orders; no arbitrary coefficient-table surrogate occurs. -/
theorem no_fixed_polynomial_reduction_detector [IsAlgClosed K]
    (f : MvPolynomial (Fin 5) K) :
    ¬ ∀ p : ParameterSpace (K := K), p ∈ generatorStratum 4 ↔
      HasOrder (partialReduceSeries p.val 60 (generatorEvaluation (RingHom.id K) p.val f)) 58 := by
  intro h
  by_cases h0 : MvPolynomial.eval 0 f = 0
  · apply generatorStratum_four_not_principal_open (detectionPolynomial f)
    ext p
    exact (h p).trans (polynomial_reduction_order58_iff p f h0)
  · obtain ⟨p,hp⟩ := generatorStratum_four_nonempty (K := K)
    have h58 := (h p).mp hp
    have hz := polynomial_reduction_order_zero p.val f h0
    exact hz.2 (h58.1 0 (by omega))

end Field
end EmbeddingDimensionStrata
