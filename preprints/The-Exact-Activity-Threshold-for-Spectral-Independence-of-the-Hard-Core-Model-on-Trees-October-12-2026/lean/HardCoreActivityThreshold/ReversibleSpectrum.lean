import HardCoreActivityThreshold.SupportHeatBath
import HardCoreActivityThreshold.SymmetricSecondEigenvalue
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-! The ordinary matrix spectrum of a finite reversible chain. -/
namespace HardCoreActivityThreshold.FiniteReversibleChain
open Finset Matrix
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def transitionMatrix (P : FiniteReversibleChain Ω) : Matrix Ω Ω ℝ := P.transition

/-- The symmetric conjugate `D^(1/2) P D^(-1/2)` of the transition matrix. -/
noncomputable def symmetricTransition (P : FiniteReversibleChain Ω) : Matrix Ω Ω ℝ :=
  fun x y => Real.sqrt (P.law.mass x) * P.transition x y / Real.sqrt (P.law.mass y)

/-- The change of coordinates from functions to ordinary Euclidean coordinates. -/
noncomputable def sqrtMassMatrix (P : FiniteReversibleChain Ω) : Matrix Ω Ω ℝ :=
  diagonal (fun x => Real.sqrt (P.law.mass x))

noncomputable def invSqrtMassMatrix (P : FiniteReversibleChain Ω) : Matrix Ω Ω ℝ :=
  diagonal (fun x => (Real.sqrt (P.law.mass x))⁻¹)

theorem sqrtMassMatrix_mul_inv (P : FiniteReversibleChain Ω)
    (hp : ∀ x, 0 < P.law.mass x) : P.sqrtMassMatrix * P.invSqrtMassMatrix = 1 := by
  rw [sqrtMassMatrix, invSqrtMassMatrix, diagonal_mul_diagonal]
  simp [Real.sqrt_ne_zero'.mpr (hp _)]

theorem invSqrtMassMatrix_mul (P : FiniteReversibleChain Ω)
    (hp : ∀ x, 0 < P.law.mass x) : P.invSqrtMassMatrix * P.sqrtMassMatrix = 1 := by
  rw [invSqrtMassMatrix, sqrtMassMatrix, diagonal_mul_diagonal]
  simp [Real.sqrt_ne_zero'.mpr (hp _)]

theorem symmetricTransition_eq_conjugate (P : FiniteReversibleChain Ω) :
    P.symmetricTransition = P.sqrtMassMatrix * P.transitionMatrix * P.invSqrtMassMatrix := by
  ext x y
  rw [sqrtMassMatrix, invSqrtMassMatrix, mul_diagonal, diagonal_mul]
  rfl

omit [DecidableEq Ω] in
theorem symmetricTransition_isHermitian (P : FiniteReversibleChain Ω)
    (hp : ∀ x, 0 < P.law.mass x) : P.symmetricTransition.IsHermitian := by
  rw [Matrix.IsHermitian]
  ext x y
  simp only [conjTranspose_apply, star_trivial, symmetricTransition]
  apply (div_eq_div_iff (Real.sqrt_ne_zero'.mpr (hp x))
    (Real.sqrt_ne_zero'.mpr (hp y))).2
  have hx := Real.sq_sqrt (P.law.nonneg x)
  have hy := Real.sq_sqrt (P.law.nonneg y)
  calc
    _ = P.law.mass y * P.transition y x := by nlinarith [congrArg (fun t => t * P.transition y x) hy]
    _ = P.law.mass x * P.transition x y := (P.reversible x y).symm
    _ = _ := by nlinarith [congrArg (fun t => t * P.transition x y) hx]

/-- Similarity preserves the characteristic polynomial, including multiplicities. -/
theorem symmetricTransition_charpoly (P : FiniteReversibleChain Ω)
    (hp : ∀ x, 0 < P.law.mass x) : P.symmetricTransition.charpoly =
      P.transitionMatrix.charpoly := by
  rw [symmetricTransition_eq_conjugate, charpoly_mul_comm, ← Matrix.mul_assoc,
    invSqrtMassMatrix_mul P hp, Matrix.one_mul]

/-- Thus this is the spectrum of the actual stochastic transition, not a surrogate gap. -/
theorem symmetricTransition_spectrum (P : FiniteReversibleChain Ω)
    (hp : ∀ x, 0 < P.law.mass x) : spectrum ℝ P.symmetricTransition =
      spectrum ℝ P.transitionMatrix := by
  ext r
  simp only [Matrix.mem_spectrum_iff_isRoot_charpoly, symmetricTransition_charpoly P hp]

/-- Eigenvalues of the actual transition, in decreasing order with multiplicity. -/
noncomputable def transitionEigenvalues (P : FiniteReversibleChain Ω)
    (hp : ∀ x, 0 < P.law.mass x) : Fin (Fintype.card Ω) → ℝ :=
  (P.symmetricTransition_isHermitian hp).eigenvalues₀

theorem transitionEigenvalues_antitone (P : FiniteReversibleChain Ω)
    (hp : ∀ x, 0 < P.law.mass x) : Antitone (P.transitionEigenvalues hp) :=
  (P.symmetricTransition_isHermitian hp).eigenvalues₀_antitone

theorem transition_roots_charpoly (P : FiniteReversibleChain Ω)
    (hp : ∀ x, 0 < P.law.mass x) :
    P.transitionMatrix.charpoly.roots =
      Multiset.map (P.transitionEigenvalues hp) Finset.univ.val := by
  rw [← symmetricTransition_charpoly P hp]
  simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq, transitionEigenvalues] using
    (P.symmetricTransition_isHermitian hp).roots_charpoly_eq_eigenvalues₀

/-- Sorting the actual transition's characteristic roots gives exactly these eigenvalues. -/
theorem transition_sorted_roots_charpoly (P : FiniteReversibleChain Ω)
    (hp : ∀ x, 0 < P.law.mass x) :
    P.transitionMatrix.charpoly.roots.sort (· ≥ ·) = List.ofFn (P.transitionEigenvalues hp) := by
  rw [← symmetricTransition_charpoly P hp]
  simpa only [RCLike.re_to_real, Multiset.map_id', transitionEigenvalues] using
    (P.symmetricTransition_isHermitian hp).sort_roots_charpoly_eq_eigenvalues₀

/-- The paper's ordinary spectral gap, with the one-state convention. -/
noncomputable def ordinarySpectralGap (P : FiniteReversibleChain Ω)
    (hp : ∀ x, 0 < P.law.mass x) : ℝ :=
  if h : 1 < Fintype.card Ω then 1 - P.transitionEigenvalues hp ⟨1, h⟩ else 1

omit [DecidableEq Ω] in
/-- A one-state chain has no nonconstant observables. -/
theorem spectralGap_eq_one_of_subsingleton (P : FiniteReversibleChain Ω) [Subsingleton Ω] :
    P.spectralGap = 1 := by
  have hv (f : Ω → ℝ) : P.law.variance f = 0 := by
    cases isEmpty_or_nonempty Ω with
    | inl h =>
      have := h
      simp [FiniteLaw.variance, FiniteLaw.expectation]
    | inr h =>
      have := h
      let x := Classical.choice h
      have hf : f = fun _ => f x := funext (fun y => congrArg f (Subsingleton.elim y x))
      rw [hf, FiniteLaw.variance, FiniteLaw.expectation_const]
      simp
  simp [spectralGap, hv]


omit [DecidableEq Ω] in
theorem stationary (P : FiniteReversibleChain Ω) (y : Ω) :
    (∑ x, P.law.mass x * P.transition x y) = P.law.mass y := by
  simp_rw [P.reversible]
  rw [← mul_sum, P.row_sum, mul_one]

omit [DecidableEq Ω] in
theorem dirichlet_nonneg (P : FiniteReversibleChain Ω) (f : Ω → ℝ) :
    0 ≤ P.dirichlet f := by
  apply div_nonneg _ (by norm_num)
  exact sum_nonneg fun x _ => sum_nonneg fun y _ =>
    mul_nonneg (mul_nonneg (P.law.nonneg x) (P.nonneg x y)) (sq_nonneg _)

omit [DecidableEq Ω] in
theorem dirichlet_sub_const (P : FiniteReversibleChain Ω) (f : Ω → ℝ) (c : ℝ) :
    P.dirichlet (fun x => f x - c) = P.dirichlet f := by
  unfold dirichlet
  congr 1
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  congr 2
  ring

omit [DecidableEq Ω] in
theorem dirichlet_eq_second_moment_sub (P : FiniteReversibleChain Ω) (f : Ω → ℝ) :
    P.dirichlet f = P.law.expectation (fun x => f x ^ 2) -
      ∑ x, P.law.mass x * f x * ∑ y, P.transition x y * f y := by
  have hfirst : (∑ x, ∑ y, P.law.mass x * P.transition x y * f x ^ 2) =
      P.law.expectation (fun x => f x ^ 2) := by
    apply sum_congr rfl
    intro x _
    calc
      _ = P.law.mass x * f x ^ 2 * ∑ y, P.transition x y := by
        rw [mul_sum]; apply sum_congr rfl; intro y _; ring
      _ = _ := by rw [P.row_sum, mul_one]
  have hsecond : (∑ x, ∑ y, P.law.mass x * P.transition x y * f y ^ 2) =
      P.law.expectation (fun x => f x ^ 2) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro y _
    rw [← sum_mul, P.stationary]
  have hcross : (∑ x, ∑ y, P.law.mass x * P.transition x y * (f x * f y)) =
      ∑ x, P.law.mass x * f x * ∑ y, P.transition x y * f y := by
    apply sum_congr rfl
    intro x _
    rw [mul_sum]
    apply sum_congr rfl
    intro y _
    ring
  have hpoly (x y : Ω) : P.law.mass x * P.transition x y * (f x - f y)^2 =
      P.law.mass x * P.transition x y * f x ^ 2 +
      P.law.mass x * P.transition x y * f y ^ 2 -
      2 * (P.law.mass x * P.transition x y * (f x * f y)) := by ring
  simp_rw [dirichlet, hpoly, sum_sub_distrib, sum_add_distrib, ← mul_sum]
  rw [hfirst, hsecond, hcross]
  ring

/-- The Euclidean coordinate transform corresponding to the diagonal similarity. -/
noncomputable def toEuclidean (P : FiniteReversibleChain Ω) (f : Ω → ℝ) : EuclideanSpace ℝ Ω :=
  WithLp.toLp 2 (fun x => Real.sqrt (P.law.mass x) * f x)

noncomputable def fromEuclidean (P : FiniteReversibleChain Ω) (v : EuclideanSpace ℝ Ω) : Ω → ℝ :=
  fun x => v x / Real.sqrt (P.law.mass x)

omit [DecidableEq Ω] in
theorem toEuclidean_fromEuclidean (P : FiniteReversibleChain Ω)
    (hp : ∀ x, 0 < P.law.mass x) (v : EuclideanSpace ℝ Ω) :
    P.toEuclidean (P.fromEuclidean v) = v := by
  apply PiLp.ext
  intro x
  simp only [toEuclidean, fromEuclidean, WithLp.ofLp_toLp]
  exact mul_div_cancel₀ _ (Real.sqrt_ne_zero'.mpr (hp x))

omit [DecidableEq Ω] in
theorem toEuclidean_inner (P : FiniteReversibleChain Ω) (f g : Ω → ℝ) :
    inner ℝ (P.toEuclidean f) (P.toEuclidean g) =
      P.law.expectation (fun x => f x * g x) := by
  simp only [PiLp.inner_apply, toEuclidean, Real.inner_apply,
    FiniteLaw.expectation]
  apply sum_congr rfl
  intro x _
  have hx := Real.sq_sqrt (P.law.nonneg x)
  calc
    _ = Real.sqrt (P.law.mass x)^2 * (f x * g x) := by ring
    _ = _ := by rw [hx]

omit [DecidableEq Ω] in
theorem toEuclidean_norm_sq (P : FiniteReversibleChain Ω) (f : Ω → ℝ) :
    ‖P.toEuclidean f‖^2 = P.law.expectation (fun x => f x^2) := by
  rw [← real_inner_self_eq_norm_sq, toEuclidean_inner]
  simp only [pow_two]

theorem symmetricTransition_toEuclidean (P : FiniteReversibleChain Ω)
    (hp : ∀ x, 0 < P.law.mass x) (f : Ω → ℝ) :
    P.symmetricTransition.toEuclideanLin (P.toEuclidean f) =
      P.toEuclidean (fun x => ∑ y, P.transition x y * f y) := by
  rw [Matrix.toLpLin_apply]
  apply PiLp.ext
  intro x
  simp only [WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, toEuclidean, symmetricTransition]
  rw [mul_sum]
  apply sum_congr rfl
  intro y _
  field_simp [Real.sqrt_ne_zero'.mpr (hp y)]

theorem dirichlet_eq_norm_sub_inner (P : FiniteReversibleChain Ω)
    (hp : ∀ x, 0 < P.law.mass x) (f : Ω → ℝ) :
    P.dirichlet f = ‖P.toEuclidean f‖^2 -
      inner ℝ (P.symmetricTransition.toEuclideanLin (P.toEuclidean f)) (P.toEuclidean f) := by
  rw [P.symmetricTransition_toEuclidean hp, P.toEuclidean_inner, P.toEuclidean_norm_sq,
    P.dirichlet_eq_second_moment_sub]
  congr 1
  unfold FiniteLaw.expectation
  apply sum_congr rfl
  intro x _
  ring


/-- The unit stationary vector in symmetric coordinates. -/
noncomputable def stationaryVector (P : FiniteReversibleChain Ω) : EuclideanSpace ℝ Ω :=
  P.toEuclidean (fun _ => 1)

omit [DecidableEq Ω] in
theorem stationaryVector_norm (P : FiniteReversibleChain Ω) : ‖P.stationaryVector‖ = 1 := by
  have h : ‖P.stationaryVector‖^2 = 1 := by
    rw [stationaryVector, P.toEuclidean_norm_sq]
    simp
  nlinarith [norm_nonneg P.stationaryVector]

omit [DecidableEq Ω] in
theorem stationaryVector_inner (P : FiniteReversibleChain Ω) (f : Ω → ℝ) :
    inner ℝ P.stationaryVector (P.toEuclidean f) = P.law.expectation f := by
  rw [stationaryVector, P.toEuclidean_inner]
  simp only [one_mul]

theorem symmetricTransition_stationaryVector (P : FiniteReversibleChain Ω)
    (hp : ∀ x, 0 < P.law.mass x) :
    P.symmetricTransition.toEuclideanLin P.stationaryVector = P.stationaryVector := by
  rw [stationaryVector, P.symmetricTransition_toEuclidean hp]
  simp only [mul_one, P.row_sum]

theorem symmetricTransition_quadratic_le (P : FiniteReversibleChain Ω)
    (hp : ∀ x, 0 < P.law.mass x) (v : EuclideanSpace ℝ Ω) :
    inner ℝ (P.symmetricTransition.toEuclideanLin v) v ≤ ‖v‖^2 := by
  have h := P.dirichlet_nonneg (P.fromEuclidean v)
  rwa [P.dirichlet_eq_norm_sub_inner hp, P.toEuclidean_fromEuclidean hp,
    sub_nonneg] at h

omit [DecidableEq Ω] in
theorem toEuclidean_centered_norm (P : FiniteReversibleChain Ω) (f : Ω → ℝ) :
    ‖P.toEuclidean (fun x => f x - P.law.expectation f)‖^2 = P.law.variance f := by
  rw [P.toEuclidean_norm_sq]
  rfl

omit [DecidableEq Ω] in
theorem toEuclidean_centered_orthogonal (P : FiniteReversibleChain Ω) (f : Ω → ℝ) :
    inner ℝ P.stationaryVector (P.toEuclidean (fun x => f x - P.law.expectation f)) = 0 := by
  rw [P.stationaryVector_inner, P.law.expectation_sub, P.law.expectation_const, sub_self]

/-- Convert a genuine centered spectral extremum into the optimal Poincaré constant. -/
theorem spectralGap_eq_of_centered_eigenvalue (P : FiniteReversibleChain Ω)
    (hp : ∀ x, 0 < P.law.mass x) (lam : ℝ)
    (hbound : ∀ v : EuclideanSpace ℝ Ω, inner ℝ P.stationaryVector v = 0 →
      inner ℝ (P.symmetricTransition.toEuclideanLin v) v ≤ lam * ‖v‖^2)
    (hwitness : ∃ v : EuclideanSpace ℝ Ω, v ≠ 0 ∧
      inner ℝ P.stationaryVector v = 0 ∧ P.symmetricTransition.toEuclideanLin v = lam • v) :
    P.spectralGap = 1 - lam := by
  have hlower (f : Ω → ℝ) (hf : 0 < P.law.variance f) :
      1 - lam ≤ P.dirichlet f / P.law.variance f := by
    apply (le_div_iff₀ hf).2
    have h := hbound (P.toEuclidean (fun x => f x - P.law.expectation f))
      (P.toEuclidean_centered_orthogonal f)
    have he := P.dirichlet_eq_norm_sub_inner hp (fun x => f x - P.law.expectation f)
    rw [P.dirichlet_sub_const, P.toEuclidean_centered_norm] at he
    rw [P.toEuclidean_centered_norm] at h
    nlinarith
  obtain ⟨v, hv, ho, he⟩ := hwitness
  let f := P.fromEuclidean v
  have hfv : P.toEuclidean f = v := P.toEuclidean_fromEuclidean hp v
  have hef : P.law.expectation f = 0 := by
    rw [← P.stationaryVector_inner f, hfv]
    exact ho
  have hvar : P.law.variance f = ‖v‖^2 := by
    rw [FiniteLaw.variance, hef]
    simp only [sub_zero]
    rw [← P.toEuclidean_norm_sq, hfv]
  have hpos : 0 < P.law.variance f := by
    rw [hvar]
    exact sq_pos_of_pos (norm_pos_iff.mpr hv)
  have hratio : P.dirichlet f / P.law.variance f = 1 - lam := by
    rw [P.dirichlet_eq_norm_sub_inner hp, hfv, he, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hvar]
    apply (div_eq_iff (ne_of_gt (by rwa [← hvar] : 0 < ‖v‖^2))).2
    ring
  unfold spectralGap
  rw [ite_eq_left ⟨f, hpos⟩]
  have hne : {r : ℝ | ∃ g : Ω → ℝ, 0 < P.law.variance g ∧
      r = P.dirichlet g / P.law.variance g}.Nonempty := ⟨_, f, hpos, rfl⟩
  have hb : BddBelow {r : ℝ | ∃ g : Ω → ℝ, 0 < P.law.variance g ∧
      r = P.dirichlet g / P.law.variance g} := by
    refine ⟨1 - lam, ?_⟩
    rintro r ⟨g, hg, rfl⟩
    exact hlower g hg
  apply le_antisymm
  · exact csInf_le hb ⟨f, hpos, hratio.symm⟩
  · apply le_csInf hne
    rintro r ⟨g, hg, rfl⟩
    exact hlower g hg


/-- The largest transition eigenvalue is one. -/
theorem transitionEigenvalues_zero (P : FiniteReversibleChain Ω)
    (hp : ∀ x, 0 < P.law.mass x) (hn : 0 < Fintype.card Ω) :
    P.transitionEigenvalues hp ⟨0, hn⟩ = 1 := by
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr (P.symmetricTransition_isHermitian hp)
  have hu : P.stationaryVector ≠ 0 := by
    intro hz
    have he := P.stationaryVector_norm
    simp [hz] at he
  have heig : Module.End.HasEigenvalue P.symmetricTransition.toEuclideanLin (1 : ℝ) := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨?_, hu⟩
    rw [Module.End.mem_eigenspace_iff, one_smul]
    exact P.symmetricTransition_stationaryVector hp
  obtain ⟨i, hi⟩ := hT.exists_eigenvalues_eq finrank_euclideanSpace heig
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hi
  have hle := hT.eigenvalues_antitone finrank_euclideanSpace (show (⟨0, hn⟩ : Fin (Fintype.card Ω)) ≤ i from Nat.zero_le _)
  rw [hi] at hle
  have hge := symmetric_eigenvalue_le_one hT finrank_euclideanSpace
    (P.symmetricTransition_quadratic_le hp) ⟨0, hn⟩
  exact le_antisymm hge hle

/-- The Poincaré gap is exactly one minus the second-largest transition eigenvalue,
counted with multiplicity. No irreducibility or simplicity assumption is needed. -/
theorem spectralGap_eq_one_sub_second_eigenvalue (P : FiniteReversibleChain Ω)
    (hp : ∀ x, 0 < P.law.mass x) (hn2 : 1 < Fintype.card Ω) :
    P.spectralGap = 1 - P.transitionEigenvalues hp ⟨1, hn2⟩ := by
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr (P.symmetricTransition_isHermitian hp)
  apply P.spectralGap_eq_of_centered_eigenvalue hp
  · exact symmetric_second_eigenvalue_bound hT finrank_euclideanSpace hn2
      P.stationaryVector P.stationaryVector_norm (P.symmetricTransition_stationaryVector hp)
      (P.symmetricTransition_quadratic_le hp)
  · exact symmetric_second_eigenvalue_attained hT finrank_euclideanSpace hn2
      P.stationaryVector (P.symmetricTransition_stationaryVector hp)
      (P.symmetricTransition_quadratic_le hp)

/-- The exact ordinary finite-state spectral interpretation, including the one-state convention. -/
theorem spectralGap_eq_ordinarySpectralGap (P : FiniteReversibleChain Ω)
    (hp : ∀ x, 0 < P.law.mass x) : P.spectralGap = P.ordinarySpectralGap hp := by
  unfold ordinarySpectralGap
  split_ifs with hn
  · exact P.spectralGap_eq_one_sub_second_eigenvalue hp hn
  · have : Subsingleton Ω := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    exact P.spectralGap_eq_one_of_subsingleton

end HardCoreActivityThreshold.FiniteReversibleChain

namespace HardCoreActivityThreshold
noncomputable instance FiniteLaw.supportDecidableEq {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) : DecidableEq μ.Support := Classical.decEq _

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The heat-bath gap in the main theorem is the ordinary transition spectral gap on
its true positive-probability support, including the singleton convention. -/
theorem heatBathGap_eq_ordinary_support_gap (μ : FiniteLaw (Finset V)) :
    heatBathGap μ = (supportHeatBath μ).ordinarySpectralGap (fun s => s.property) := by
  rw [heatBathGap_eq_support_spectralGap]
  exact (supportHeatBath μ).spectralGap_eq_ordinarySpectralGap (fun s => s.property)

/-- On a support with at least two states, the gap is exactly `1 - second eigenvalue`
of the actual support heat-bath transition matrix. -/
theorem heatBathGap_eq_one_sub_second_support_eigenvalue (μ : FiniteLaw (Finset V))
    (hn2 : 1 < Fintype.card μ.Support) :
    heatBathGap μ = 1 - (supportHeatBath μ).transitionEigenvalues (fun s => s.property) ⟨1, hn2⟩ := by
  rw [heatBathGap_eq_support_spectralGap]
  exact (supportHeatBath μ).spectralGap_eq_one_sub_second_eigenvalue (fun s => s.property) hn2

end HardCoreActivityThreshold
