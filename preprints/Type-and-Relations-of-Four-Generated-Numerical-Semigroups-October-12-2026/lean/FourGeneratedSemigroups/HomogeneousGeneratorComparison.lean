import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Matrix.Rank

noncomputable section
namespace FourGeneratedSemigroups
open MvPolynomial

variable {σ K : Type*} [Field K]

/-- The component in the degree of a homogeneous polynomial only sees the
constant coefficient of a multiplying polynomial. -/
lemma homogeneous_component_mul_same (w : σ → ℕ) (hw : ∀ i, w i ≠ 0)
    {f : MvPolynomial σ K} {n : ℕ} (hf : IsWeightedHomogeneous w f n)
    (p : MvPolynomial σ K) :
    weightedHomogeneousComponent w n (p * f) = C (p.coeff 0) * f := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a r =>
    by_cases ha : a = 0
    · subst a
      simpa [← MvPolynomial.C_apply] using
        (hf.C_mul r).weightedHomogeneousComponent_same
    · have haw : Finsupp.weight w a ≠ 0 := by
        intro hz
        apply ha
        ext i
        by_contra hi
        have hle := Finsupp.le_weight_of_ne_zero' w hi
        rw [hz] at hle
        exact hw i (Nat.eq_zero_of_le_zero hle)
      have hp := (isWeightedHomogeneous_monomial w a r rfl).mul hf
      rw [hp.weightedHomogeneousComponent_ne n (by omega)]
      simp [coeff_monomial, ha]
  | add p q hp hq => simp only [add_mul, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]


/-- A polynomial syzygy on irredundant homogeneous generators has no nonzero
constant coefficient. This is the elementary graded minimality argument. -/
lemma homogeneous_irredundant_syzygy_constant_eq_zero
    {ι : Type*} [Fintype ι] (w : σ → ℕ) (hw : ∀ i, w i ≠ 0)
    (f : ι → MvPolynomial σ K) (degree : ι → ℕ)
    (hf : ∀ i, IsWeightedHomogeneous w (f i) (degree i))
    (hirred : ∀ i, f i ∉ Ideal.span (f '' {j | j ≠ i}))
    (p : ι → MvPolynomial σ K) (hrel : ∑ i, p i * f i = 0) :
    ∀ i, (p i).coeff 0 = 0 := by
  classical
  let : GradedAlgebra (weightedHomogeneousSubmodule K w) := weightedGradedAlgebra K w
  intro i
  let J : Ideal (MvPolynomial σ K) := Ideal.span (f '' {j | j ≠ i})
  have hother : (∑ j ∈ Finset.univ.erase i, p j * f j) ∈ J := by
    apply J.sum_mem
    intro j hj
    apply J.mul_mem_left
    apply Ideal.subset_span
    exact ⟨j, (Finset.mem_erase.mp hj).1, rfl⟩
  have hsum : (∑ j ∈ Finset.univ.erase i, p j * f j) + p i * f i = 0 := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    exact hrel
  have hmem : p i * f i ∈ J := by
    rw [eq_neg_of_add_eq_zero_right hsum]
    exact J.neg_mem hother
  have hhom : J.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    rintro _ ⟨j, _, rfl⟩
    exact ⟨degree j, hf j⟩
  have hc : C ((p i).coeff 0) * f i ∈ J := by
    rw [← homogeneous_component_mul_same w hw (hf i)]
    exact weightedHomogeneousComponent_mem_of_mem K w hhom hmem (degree i)
  by_contra hne
  apply hirred i
  have hh := J.mul_mem_left (C ((p i).coeff 0)⁻¹) hc
  simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul] using hh


/-- Every irredundant homogeneous generating family has cardinality no larger
than any other finite generating family of the same ideal. -/
theorem homogeneous_generators_card_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0)
    (f : ι → MvPolynomial σ K) (g : κ → MvPolynomial σ K)
    (degree : ι → ℕ)
    (hf : ∀ i, IsWeightedHomogeneous w (f i) (degree i))
    (hirred : ∀ i, f i ∉ Ideal.span (f '' {j | j ≠ i}))
    (hspan : Ideal.span (Set.range f) = Ideal.span (Set.range g)) :
    Fintype.card ι ≤ Fintype.card κ := by
  classical
  have hexA : ∀ i, ∃ c : κ → MvPolynomial σ K, ∑ j, c j * g j = f i := by
    intro i
    apply Ideal.mem_span_range_iff_exists_fun.mp
    rw [← hspan]
    exact Ideal.subset_span (Set.mem_range_self i)
  have hexB : ∀ j, ∃ c : ι → MvPolynomial σ K, ∑ i, c i * f i = g j := by
    intro j
    apply Ideal.mem_span_range_iff_exists_fun.mp
    rw [hspan]
    exact Ideal.subset_span (Set.mem_range_self j)
  choose A hA using hexA
  choose B hB using hexB
  change Matrix ι κ (MvPolynomial σ K) at A
  change Matrix κ ι (MvPolynomial σ K) at B
  have hAv : Matrix.mulVec A g = f := funext hA
  have hBv : Matrix.mulVec B f = g := funext hB
  have hrel : (A * B - (1 : Matrix ι ι (MvPolynomial σ K))).mulVec f = 0 := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hBv, hAv, Matrix.one_mulVec, sub_self]
  have hcoeff : ∀ i j, ((A * B - (1 : Matrix ι ι (MvPolynomial σ K))) i j).coeff 0 = 0 := by
    intro i
    apply homogeneous_irredundant_syzygy_constant_eq_zero w hw f degree hf hirred
    exact congrFun hrel i
  let A₀ : Matrix ι κ K := Matrix.map A constantCoeff
  let B₀ : Matrix κ ι K := Matrix.map B constantCoeff
  have hprod : A₀ * B₀ = 1 := by
    have hmap : (A * B - (1 : Matrix ι ι (MvPolynomial σ K))).map constantCoeff = 0 := by
      ext i j
      exact hcoeff i j
    rw [Matrix.map_sub _ (map_sub constantCoeff), Matrix.map_mul,
      Matrix.map_one _ (map_zero constantCoeff) (map_one constantCoeff), sub_eq_zero] at hmap
    exact hmap
  calc Fintype.card ι = Matrix.rank (1 : Matrix ι ι K) := Matrix.rank_one.symm
    _ = Matrix.rank (A₀ * B₀) := congrArg Matrix.rank hprod.symm
    _ ≤ Matrix.rank A₀ := Matrix.rank_mul_le_left A₀ B₀
    _ ≤ Fintype.card κ := Matrix.rank_le_card_width A₀

end FourGeneratedSemigroups
